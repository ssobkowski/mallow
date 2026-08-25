//! NIR passes run after materialization and verification.

mod fold_packs;
mod inline;

use super::Function;

/// Runs every NIR pass over all functions until stable.
///
/// Returns whether any function was changed.
pub(crate) fn run(functions: &mut [Function]) -> bool {
    let mut changed = false;
    loop {
        let mut round_changed = false;
        for function in functions.iter_mut() {
            round_changed |= fold_packs::run(function);
            round_changed |= inline::run(function);
        }
        if !round_changed {
            return changed;
        }
        changed = true;
    }
}
