use crate::hil::StructuredFunction;

mod fold_tables;
mod inlining;
pub mod visitor;

pub fn run(fns: &mut [StructuredFunction]) {
    for fun in fns {
        loop {
            let mut changed = inlining::run(fun);

            changed = changed || fold_tables::run(fun);

            if !changed {
                break;
            }
        }
    }
}
