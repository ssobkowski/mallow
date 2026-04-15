use crate::hil::StructuredFunction;

mod common;
mod immediate;
mod pure;

pub fn run(fun: &mut StructuredFunction) {
    pure::run(fun);
    immediate::run(fun);
}
