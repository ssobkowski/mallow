use crate::hil::{ReturnArity, StructuredFunction, cflow::cfg::ControlFlowGraph};

mod common;
mod immediate;
mod pure;

pub fn run(fun: &mut StructuredFunction, return_arities: &[ReturnArity]) -> bool {
    immediate::run(fun, return_arities)
}

pub fn run_pre_region(cfg: &mut ControlFlowGraph) -> bool {
    pure::run_cfg(cfg)
}
