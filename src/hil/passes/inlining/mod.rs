use crate::hil::StructuredFunction;

mod common;
mod immediate;
mod pure;

pub fn run(fun: &mut StructuredFunction) -> bool {
    pure::run(fun) || immediate::run(fun)
}
