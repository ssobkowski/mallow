use crate::hil::{ReturnArity, StructuredFunction};

mod fold_tables;
mod inlining;
mod return_arity;
mod tuple_assign;
pub mod visitor;

pub fn run(fns: &mut [StructuredFunction]) {
    return_arity::infer_all(fns);
    let return_arities: Vec<ReturnArity> = fns
        .iter()
        .map(|f| {
            f.return_arity
                .expect("return arity must be inferred before inlining")
        })
        .collect();

    for fun in fns {
        loop {
            let mut changed = inlining::run(fun, &return_arities);
            changed = changed || tuple_assign::run(fun);

            changed = changed || fold_tables::run(fun);

            if !changed {
                break;
            }
        }
    }
}
