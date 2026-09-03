//! NIR passes run after materialization and verification.

mod fold_packs;
mod fold_shapes;
mod fold_tables;
mod inline;
mod normalize;

use crate::ir::Unit;

use super::Function;

/// Runs every NIR pass over all functions until stable.
///
/// Returns whether any function was changed.
pub(crate) fn run(unit: &mut Unit<Function>) -> bool {
    let mut changed = false;
    loop {
        let mut round_changed = false;
        for function in unit.functions_mut() {
            round_changed |= normalize::run(function);
            round_changed |= fold_packs::run(function);
            round_changed |= inline::run(function);
            round_changed |= fold_tables::run(function);
            round_changed |= fold_shapes::run(function);
        }
        if !round_changed {
            return changed;
        }
        changed = true;
    }
}
