use crate::hil::{
    ReturnArity, StructuredFunction,
    cflow::region::RegionNode,
    ir::HilExpr,
    passes::visitor::{Visitor, walk_region},
};

struct ReturnCollector<'a> {
    known: &'a [Option<ReturnArity>],
    signal: Option<ReturnArity>,
}

impl ReturnCollector<'_> {
    fn expr_arity(&self, expr: &HilExpr) -> ReturnArity {
        match expr {
            HilExpr::Call { fun, .. } => self.call_arity(fun),
            HilExpr::MethodCall { .. } => ReturnArity::Unknown,
            HilExpr::VarArgs => ReturnArity::Unknown,
            _ => ReturnArity::Exact(1),
        }
    }

    fn call_arity(&self, fun: &HilExpr) -> ReturnArity {
        let HilExpr::Closure { proto, .. } = fun else {
            return ReturnArity::Unknown;
        };

        match self
            .known
            .get(*proto)
            .copied()
            .flatten()
            .unwrap_or(ReturnArity::Unknown)
        {
            ReturnArity::Exact(n) => ReturnArity::Exact(n),
            ReturnArity::Unknown => ReturnArity::Unknown,
        }
    }

    fn values_arity(&self, values: &[HilExpr]) -> ReturnArity {
        let Some((tail, prefix)) = values.split_last() else {
            return ReturnArity::Exact(0);
        };

        let tail_arity = self.expr_arity(tail);
        match tail_arity {
            ReturnArity::Exact(n) => ReturnArity::Exact(prefix.len() + n),
            ReturnArity::Unknown => ReturnArity::Unknown,
        }
    }

    fn observe_return(&mut self, values: &[HilExpr]) {
        let curr = self.values_arity(values);
        self.signal = Some(match self.signal {
            Some(prev) => prev.merge(curr),
            None => curr,
        });
    }
}

impl Visitor for ReturnCollector<'_> {
    fn visit_region(&mut self, node: &RegionNode) {
        if let RegionNode::Return { values } = node {
            self.observe_return(values);
            return;
        }

        walk_region(self, node);
    }
}

pub fn infer_all(functions: &mut [StructuredFunction]) {
    let mut known = vec![None; functions.len()];

    loop {
        let mut changed = false;

        for fun in functions.iter_mut() {
            let mut collector = ReturnCollector {
                known: &known,
                signal: None,
            };
            collector.visit_region(&fun.root);

            let inferred = collector.signal.unwrap_or(ReturnArity::Exact(0));

            if known[fun.proto] != Some(inferred) {
                known[fun.proto] = Some(inferred);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    for fun in functions {
        fun.return_arity = known[fun.proto];
    }
}
