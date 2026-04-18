use crate::hil::{ReturnArity, StructuredFunction};

mod common;
mod immediate;
mod pure;

pub fn run(fun: &mut StructuredFunction, return_arities: &[ReturnArity]) -> bool {
    pure::run(fun) || immediate::run(fun, return_arities)
}
