use crate::hil::StructuredFunction;

mod inlining;
pub mod visitor;

pub fn run(fns: &mut [StructuredFunction]) {
    for fun in fns {
        inlining::run(fun);
    }
}
