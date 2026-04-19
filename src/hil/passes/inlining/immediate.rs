use smallvec::SmallVec;

use crate::{
    hil::{
        ReturnArity, StructuredFunction,
        cflow::region::RegionNode,
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
        passes::inlining::common::{Analyzer, Var},
        visitor::{Visitor, VisitorMut, walk_expr, walk_expr_mut, walk_region_mut},
    },
    scopes::Scope,
};

struct SingleSymbolRewriter<'a> {
    sym: SymbolId,
    expr: &'a HilExpr,
    change_count: usize,
}

impl<'a> VisitorMut for SingleSymbolRewriter<'a> {
    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Call { fun, args } = expr
            && matches!(self.expr, HilExpr::Closure { .. })
            && matches!(fun.as_ref(), HilExpr::Symbol(s) if *s == self.sym)
        {
            for arg in args {
                walk_expr_mut(self, arg);
            }
            return;
        }

        if let HilExpr::Symbol(s) = expr
            && *s == self.sym
        {
            *expr = self.expr.clone();
            self.change_count += 1;
            return;
        }
        walk_expr_mut(self, expr);
    }
}

struct SingleWalker {
    sym: SymbolId,
    count: usize,
}

impl Visitor for SingleWalker {
    fn visit_symbol(&mut self, sym: SymbolId) {
        if sym == self.sym {
            self.count += 1;
        }
    }
}

struct TupleWalker<'a> {
    syms: &'a [HilExpr],
    count: usize,
}

impl<'a> Visitor for TupleWalker<'a> {
    fn visit_expr(&mut self, expr: &HilExpr) {
        if let HilExpr::Call { args, .. } | HilExpr::MethodCall { args, .. } = expr
            && self.syms == args
        {
            self.count += 1;
        }

        walk_expr(self, expr);
    }
}

struct TupleSymbolRewriter<'a> {
    syms: &'a [HilExpr],
    expr: &'a HilExpr,
    change_count: usize,
}

impl<'a> VisitorMut for TupleSymbolRewriter<'a> {
    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Call { args, .. } | HilExpr::MethodCall { args, .. } = expr
            && self.syms == args
        {
            args.clear();
            args.push(self.expr.clone());
            self.change_count += 1;
            return;
        }

        walk_expr_mut(self, expr);
    }
}

trait Substitutable: Clone {
    fn appears_in(&self, sym: SymbolId) -> bool;
    fn appear_in(&self, syms: &[HilExpr]) -> bool;
    fn substitute_exact(&self, sym: SymbolId, expr: &HilExpr) -> Option<Self>;
    fn substitute_tuple_exact(&self, syms: &[HilExpr], expr: &HilExpr) -> Option<Self>;
}

impl Substitutable for HilStmt {
    fn appears_in(&self, sym: SymbolId) -> bool {
        let mut walker = SingleWalker { sym, count: 0 };
        walker.visit_stmt(self);
        walker.count > 0
    }

    fn appear_in(&self, syms: &[HilExpr]) -> bool {
        let mut walker = TupleWalker { syms, count: 0 };
        walker.visit_stmt(self);
        walker.count > 0
    }

    fn substitute_exact(&self, sym: SymbolId, expr: &HilExpr) -> Option<Self> {
        let mut cloned = self.clone();
        let mut rewriter = SingleSymbolRewriter {
            sym,
            expr,
            change_count: 0,
        };
        rewriter.visit_stmt(&mut cloned);
        if rewriter.change_count == 1 {
            Some(cloned)
        } else {
            None
        }
    }

    fn substitute_tuple_exact(&self, syms: &[HilExpr], expr: &HilExpr) -> Option<Self> {
        let mut cloned = self.clone();
        let mut rewriter = TupleSymbolRewriter {
            syms,
            expr,
            change_count: 0,
        };
        rewriter.visit_stmt(&mut cloned);
        if rewriter.change_count == 1 {
            Some(cloned)
        } else {
            None
        }
    }
}

impl Substitutable for HilExpr {
    fn appears_in(&self, sym: SymbolId) -> bool {
        let mut walker = SingleWalker { sym, count: 0 };
        walker.visit_expr(self);
        walker.count > 0
    }

    fn appear_in(&self, _: &[HilExpr]) -> bool {
        false
    }

    fn substitute_exact(&self, sym: SymbolId, expr: &HilExpr) -> Option<Self> {
        let mut cloned = self.clone();
        let mut rewriter = SingleSymbolRewriter {
            sym,
            expr,
            change_count: 0,
        };
        rewriter.visit_expr(&mut cloned);
        if rewriter.change_count == 1 {
            Some(cloned)
        } else {
            None
        }
    }

    fn substitute_tuple_exact(&self, _: &[HilExpr], _: &HilExpr) -> Option<Self> {
        None
    }
}

struct Inliner {
    vars: Scope<SymbolId, Var>,
    return_arities: Vec<ReturnArity>,
    was_changed: bool,
}

impl Inliner {
    fn with_vars(vars: Scope<SymbolId, Var>, return_arities: &[ReturnArity]) -> Self {
        Self {
            vars,
            return_arities: return_arities.to_vec(),
            was_changed: false,
        }
    }

    fn can_inline_tuple_binding(&self, left: &[HilExpr], value: &HilExpr) -> bool {
        !left.is_empty()
            && left.iter().all(|lvalue| match lvalue {
                HilExpr::Symbol(sym) => self
                    .vars
                    .get(sym)
                    .is_some_and(|v| v.read_count == 1 && v.write_count == 1),
                _ => true,
            })
            && self.expr_arity(value).is_some_and(|n| n == left.len())
    }

    fn try_inline_tuple_return(&self, decl: &HilStmt, values: &mut SmallVec<[HilExpr; 3]>) -> bool {
        let HilStmt::AssignMany { left, value } = decl else {
            return false;
        };

        if !self.can_inline_tuple_binding(left, value) || left.as_slice() != values.as_slice() {
            return false;
        }

        values.clear();
        values.push(value.clone());
        true
    }

    fn expr_arity(&self, expr: &HilExpr) -> Option<usize> {
        match expr {
            HilExpr::Call { fun, .. } => self.call_arity(fun),
            HilExpr::MethodCall { .. } => None,
            HilExpr::VarArgs => None,
            _ => Some(1),
        }
    }

    fn call_arity(&self, fun: &HilExpr) -> Option<usize> {
        let HilExpr::Closure { proto, .. } = fun else {
            return None;
        };

        match self
            .return_arities
            .get(*proto)
            .copied()
            .unwrap_or(ReturnArity::Unknown)
        {
            ReturnArity::Exact(n) => Some(n),
            ReturnArity::Unknown => None,
        }
    }

    fn try_inline<T: Substitutable>(&self, decl: &HilStmt, target: &T) -> Option<T> {
        match decl {
            HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                value,
            } => {
                if self
                    .vars
                    .get(sym)
                    .is_some_and(|v| v.read_count == 1 && !v.disqualified)
                    && target.appears_in(*sym)
                {
                    target.substitute_exact(*sym, value)
                } else {
                    None
                }
            }
            HilStmt::AssignMany { left, value } => {
                if self.can_inline_tuple_binding(left.as_slice(), value) && target.appear_in(left) {
                    target.substitute_tuple_exact(left, value)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Attempts to inline into the first evaluated expression of the next region block
    fn try_apply_to_region_entry(&mut self, decl: &HilStmt, right: &mut RegionNode) -> bool {
        let mut applied = false;

        let mut check_expr = |expr: &mut HilExpr| {
            if !applied && let Some(inlined) = self.try_inline(decl, expr) {
                *expr = inlined;
                applied = true;
            }
        };

        match right {
            RegionNode::BasicBlock { stmts } => {
                if let Some(next) = stmts.first_mut()
                    && let Some(inlined) = self.try_inline(decl, next)
                {
                    *next = inlined;
                    applied = true;
                }
            }
            RegionNode::If { condition, .. } | RegionNode::While { condition, .. } => {
                check_expr(condition)
            }
            RegionNode::Return { values } => {
                if self.try_inline_tuple_return(decl, values) {
                    applied = true;
                } else {
                    values.iter_mut().for_each(check_expr);
                }
            }
            RegionNode::NumericFor {
                start, end, step, ..
            } => {
                check_expr(start);
                check_expr(end);
                check_expr(step);
            }
            RegionNode::GenericFor { exprs, .. } => {
                exprs.iter_mut().for_each(check_expr);
            }
            _ => {}
        }

        applied
    }
}

impl VisitorMut for Inliner {
    fn visit_region(&mut self, node: &mut RegionNode) {
        if let RegionNode::Sequence { nodes } = node {
            // First, visit them normally as they are.
            for n in nodes.iter_mut() {
                self.visit_region(n);
            }

            // Then, in case of region edges, for instance `local vN = vM; return vN`
            for i in 0..nodes.len().saturating_sub(1) {
                let (left_slice, right_slice) = nodes.split_at_mut(i + 1);
                let left = &mut left_slice[i];
                let right = &mut right_slice[0];

                if let RegionNode::BasicBlock { stmts: decl_stmts } = left
                    && let Some(decl) = decl_stmts.last().cloned()
                    && self.try_apply_to_region_entry(&decl, right)
                {
                    decl_stmts.pop();
                    self.was_changed = true;
                }
            }
            return;
        }

        walk_region_mut(self, node);
    }

    fn visit_block(&mut self, stmts: &mut Vec<HilStmt>) {
        if stmts.is_empty() {
            return;
        }

        let mut i = 0;
        while i < stmts.len() - 1 {
            let curr = &stmts[i];
            let next = &stmts[i + 1];

            if let Some(inlined) = self.try_inline(curr, next) {
                stmts[i] = inlined;
                stmts.remove(i + 1);
                self.was_changed = true;
                continue; // i is now at the place of the next stmt
            }

            i += 1;
        }
    }
}

pub fn run(fun: &mut StructuredFunction, return_arities: &[ReturnArity]) -> bool {
    let mut changed = false;

    loop {
        let vars = Analyzer::analyze_function(fun);

        let mut inliner = Inliner::with_vars(vars, return_arities);
        inliner.visit_function(fun);

        if !inliner.was_changed {
            break;
        }
        changed = true;
    }

    changed
}
