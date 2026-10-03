//! NIR passes run after materialization and verification.

mod dead_initializers;
mod fold_assignments;
mod fold_packs;
mod fold_shapes;
mod fold_tables;
mod inline;
mod normalize;

use id_arena::Arena;

use crate::ir::Unit;
use crate::ir::fir::ValueId;

use super::visitor::{Visitor, walk_expr};
use super::{Expr, Function, Local, LocalId, Region, Stmt};

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
            round_changed |= fold_assignments::run(function);
            round_changed |= dead_initializers::run(function);
            round_changed |= fold_shapes::run(function);
        }
        if !round_changed {
            return changed;
        }
        changed = true;
    }
}

/// Finds any mention of one source storage, through any of its symbols.
struct StorageUse<'a> {
    locals: &'a Arena<Local>,
    source: ValueId,
    found: bool,
}

impl Visitor for StorageUse<'_> {
    fn visit_expr(&mut self, expr: &Expr) {
        if !self.found {
            walk_expr(self, expr);
        }
    }

    fn visit_local(&mut self, local: LocalId) {
        self.found |= self.locals[local].source == self.source;
    }
}

impl<'a> StorageUse<'a> {
    const fn new(locals: &'a Arena<Local>, source: ValueId) -> Self {
        Self {
            locals,
            source,
            found: false,
        }
    }

    /// Returns whether an expression mentions the storage anywhere.
    fn in_expr(locals: &Arena<Local>, source: ValueId, expr: &Expr) -> bool {
        let mut finder = StorageUse::new(locals, source);
        finder.visit_expr(expr);
        finder.found
    }

    /// Returns whether a statement mentions the storage anywhere.
    fn in_stmt(locals: &Arena<Local>, source: ValueId, stmt: &Stmt) -> bool {
        let mut finder = StorageUse::new(locals, source);
        finder.visit_stmt(stmt);
        finder.found
    }

    /// Returns whether a region mentions the storage anywhere.
    fn in_region(locals: &Arena<Local>, source: ValueId, region: &Region) -> bool {
        let mut finder = StorageUse::new(locals, source);
        finder.visit_region(region);
        finder.found
    }
}
