mod fold_tables;

use crate::hil::ir::{HilStmt, Spanned};

/// Runs all available lifter passes on the given HIL statements.
pub fn run_passes(stmts: Vec<Spanned<HilStmt>>) -> Vec<Spanned<HilStmt>> {
    let stmts = fold_tables::fold_table_constructors(stmts);

    stmts
}
