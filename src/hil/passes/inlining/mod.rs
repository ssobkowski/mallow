use crate::hil::{ReturnArity, StructuredFunction};

mod common;
mod immediate;
mod pure;

pub fn run(fun: &mut StructuredFunction, return_arities: &[ReturnArity]) -> bool {
    let immediate_changed = immediate::run(fun, return_arities);
    let pure_changed = pure::run(fun);
    immediate_changed || pure_changed
}
