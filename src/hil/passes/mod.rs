use crate::hil::StructuredFunction;

mod inliner;
pub mod visitor;

pub fn run(fns: &mut [StructuredFunction]) {
    for fun in fns {
        inliner::run(fun);
    }
}
