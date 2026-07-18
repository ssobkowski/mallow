use crate::hil::{StructuredFunction, cflow::cfg::ControlFlowGraph, lifter::ssa::FunctionSymbols};

mod continue_cleanup;
mod fold_bool_assign;
mod fold_tables;
mod inlining;
mod nested_ifs;
mod normalize;
mod return_arity;
mod short_circuit;
mod terminator_cleanup;
mod tuple_assign;

macro_rules! run_pass {
    ($proto:expr, $iteration:expr, $name:literal, $run:expr) => {{
        let span = tracing::info_span!(
            $name,
            proto = $proto,
            iteration = $iteration,
            changed = tracing::field::Empty,
        );
        let _enter = span.enter();

        let changed = $run;
        span.record("changed", changed);
        changed
    }};
}

pub fn run(fns: &mut [StructuredFunction]) {
    {
        let span = tracing::info_span!("infer_return_arity", function_count = fns.len());
        let _enter = span.enter();
        return_arity::infer_all(fns);
    }
    let return_arities: Vec<_> = fns
        .iter()
        .map(|f| {
            f.return_arity
                .expect("return arity must be inferred before inlining")
        })
        .collect();

    for fun in &mut *fns {
        let span = tracing::info_span!("post_region_function", proto = fun.proto.0);
        let _enter = span.enter();
        let mut iteration = 0;

        loop {
            iteration += 1;
            let proto_index = fun.proto.0;

            let mut changed = run_pass!(proto_index, iteration, "inlining_post_region", {
                inlining::run_post_region(fun, &return_arities)
            });
            changed |= run_pass!(proto_index, iteration, "tuple_assign", {
                tuple_assign::run(fun)
            });
            changed |= run_pass!(proto_index, iteration, "fold_tables", {
                fold_tables::run(fun)
            });
            changed |= run_pass!(proto_index, iteration, "short_circuit", {
                short_circuit::run(fun)
            });
            changed |= run_pass!(proto_index, iteration, "fold_bool_assign", {
                fold_bool_assign::run(fun)
            });
            changed |= run_pass!(proto_index, iteration, "continue_cleanup", {
                continue_cleanup::run(fun)
            });
            changed |= run_pass!(proto_index, iteration, "terminator_cleanup", {
                terminator_cleanup::run(fun)
            });
            changed |= run_pass!(proto_index, iteration, "nested_ifs", {
                nested_ifs::run(fun)
            });
            changed |= run_pass!(proto_index, iteration, "normalize", { normalize::run(fun) });

            if !changed {
                break;
            }
        }
    }
}

pub(crate) fn run_pre_region(cfg: &mut ControlFlowGraph, symbols: &FunctionSymbols) -> bool {
    let span = tracing::info_span!("inlining_pre_region", changed = tracing::field::Empty,);
    let _enter = span.enter();

    let changed = inlining::run_pre_region(cfg, symbols);
    span.record("changed", changed);
    changed
}
