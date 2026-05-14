use crate::hil::{StructuredFunction, cflow::cfg::ControlFlowGraph};

mod fold_bool_assign;
mod fold_tables;
mod inlining;
mod normalize;
mod return_arity;
mod short_circuit;
mod tuple_assign;

pub fn run(fns: &mut [StructuredFunction]) {
    return_arity::infer_all(fns);
    let return_arities: Vec<_> = fns
        .iter()
        .map(|f| {
            f.return_arity
                .expect("return arity must be inferred before inlining")
        })
        .collect();

    for fun in fns {
        loop {
            let mut changed = inlining::run(fun, &return_arities);
            changed |= tuple_assign::run(fun);
            changed |= fold_tables::run(fun);
            changed |= short_circuit::run(fun);
            changed |= fold_bool_assign::run(fun);
            changed |= normalize::run(fun);

            if !changed {
                break;
            }
        }
    }
}

pub(crate) fn run_pre_region(cfg: &mut ControlFlowGraph) -> bool {
    inlining::run_pre_region(cfg)
}
