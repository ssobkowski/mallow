use crate::hil::{
    ReturnArity, StructuredFunction, cflow::cfg::ControlFlowGraph, lifter::ssa::FunctionSymbols,
};

mod common;
mod post_region;
mod pre_region;

pub fn run_post_region(fun: &mut StructuredFunction, return_arities: &[ReturnArity]) -> bool {
    post_region::run(fun, return_arities)
}

pub fn run_pre_region(cfg: &mut ControlFlowGraph, symbols: &FunctionSymbols) -> bool {
    pre_region::run(cfg, symbols)
}
