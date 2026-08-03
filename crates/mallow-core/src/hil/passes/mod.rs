use std::error::Error;
use std::fmt;

use crate::hil::StructuredFunction;
use crate::hil::cflow::cfg::ControlFlowGraph;
use crate::hil::lifter::ssa::FunctionSymbols;
use crate::il::ProtoId;

/// A non-fatal failure produced while simplifying structured HIL.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PassError {
    /// Post-region passes kept changing the function at the iteration limit.
    DidNotConverge {
        /// Function that did not reach a fixed point.
        proto: ProtoId,
        /// Number of completed pass iterations.
        iterations: usize,
    },
}

impl fmt::Display for PassError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DidNotConverge { proto, iterations } => write!(
                f,
                "post-region passes did not converge for proto {proto} after {iterations} iterations; output may be less simplified"
            ),
        }
    }
}

impl Error for PassError {}

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
mod use_def;

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

/// Runs the post-region passes and returns every non-fatal pass failure.
pub fn run(fns: &mut [StructuredFunction], max_iterations: usize) -> Vec<PassError> {
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

    let mut errors = Vec::new();
    for fun in &mut *fns {
        let span = tracing::info_span!("post_region_function", proto = fun.proto.0);
        let _enter = span.enter();

        let mut converged = false;
        for iteration in 1..=max_iterations {
            let proto_index = fun.proto.0;

            run_pass!(proto_index, iteration, "inlining_post_region", {
                inlining::run_post_region(fun, &return_arities)
            });

            // Inlining owns its fixed point. Only a later pass can make another
            // outer round necessary after inlining has finished.
            let mut changed = run_pass!(proto_index, iteration, "tuple_assign", {
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
                converged = true;
                break;
            }
        }

        if !converged {
            errors.push(PassError::DidNotConverge {
                proto: fun.proto,
                iterations: max_iterations,
            });
        }
    }

    errors
}

pub(crate) fn run_pre_region(cfg: &mut ControlFlowGraph, symbols: &FunctionSymbols) -> bool {
    let span = tracing::info_span!("inlining_pre_region", changed = tracing::field::Empty,);
    let _enter = span.enter();

    let changed = inlining::run_pre_region(cfg, symbols);
    span.record("changed", changed);
    changed
}
