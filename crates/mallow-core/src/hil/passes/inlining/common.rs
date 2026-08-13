use std::collections::HashSet;

use crate::hil::cflow::region::RegionNode;
use crate::hil::ir::{Expr, PhiNode, Stmt};
use crate::hil::lifter::ssa::SymbolId;
use crate::hil::visitor::{Visitor, VisitorMut, walk_expr, walk_expr_mut};

#[derive(Debug, Default)]
struct SymbolReadSet {
    reads: HashSet<SymbolId>,
}

impl Visitor for SymbolReadSet {
    fn visit_expr(&mut self, expr: &Expr) {
        if let Expr::Symbol(sym) = expr {
            self.reads.insert(*sym);
            return;
        }

        walk_expr(self, expr);
    }

    fn visit_phi(&mut self, _: &PhiNode) {
        unreachable!("phi nodes should have been unfolded at this point")
    }
}

struct SymbolReadCounter {
    sym: SymbolId,
    count: usize,
}

impl SymbolReadCounter {
    fn new(sym: SymbolId) -> Self {
        Self { sym, count: 0 }
    }
}

impl Visitor for SymbolReadCounter {
    fn visit_expr(&mut self, expr: &Expr) {
        if let Expr::Symbol(sym) = expr
            && *sym == self.sym
        {
            self.count += 1;
            return;
        }

        walk_expr(self, expr);
    }

    fn visit_phi(&mut self, _: &PhiNode) {
        unreachable!("phi nodes should have been unfolded at this point")
    }
}

struct SymbolReplacer<'a> {
    sym: SymbolId,
    replacement: &'a Expr,
    change_count: usize,
}

impl VisitorMut for SymbolReplacer<'_> {
    fn visit_phi(&mut self, _: &mut PhiNode) {
        unreachable!("phi nodes should have been unfolded at this point")
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if let Expr::Symbol(sym) = expr
            && *sym == self.sym
        {
            *expr = self.replacement.clone();
            self.change_count += 1;
            return;
        }

        walk_expr_mut(self, expr);
    }
}

/// Collects every symbol expression reached by the normal expression visitor.
pub(super) fn expr_read_symbols(expr: &Expr) -> HashSet<SymbolId> {
    let mut reads = SymbolReadSet::default();
    reads.visit_expr(expr);
    reads.reads
}

/// Collects every symbol expression reached by the normal region visitor.
pub(super) fn region_read_symbols(region: &RegionNode) -> HashSet<SymbolId> {
    let mut reads = SymbolReadSet::default();
    reads.visit_region(region);
    reads.reads
}

/// Counts the number of times a symbol is read in an expression.
pub(super) fn count_symbol_reads_in_expr(expr: &Expr, sym: SymbolId) -> usize {
    let mut counter = SymbolReadCounter::new(sym);
    counter.visit_expr(expr);
    counter.count
}

/// Replaces all occurrences of a symbol in an expression with a replacement.
/// Returns the number of replacements made.
pub(super) fn replace_symbol_in_expr(expr: &mut Expr, sym: SymbolId, replacement: &Expr) -> usize {
    let mut replacer = SymbolReplacer {
        sym,
        replacement,
        change_count: 0,
    };
    replacer.visit_expr(expr);
    replacer.change_count
}

/// Replaces all occurrences of a symbol in a statement with a replacement.
/// Returns the number of replacements made.
pub(super) fn replace_symbol_in_stmt(stmt: &mut Stmt, sym: SymbolId, replacement: &Expr) -> usize {
    let mut replacer = SymbolReplacer {
        sym,
        replacement,
        change_count: 0,
    };
    replacer.visit_stmt(stmt);
    replacer.change_count
}

/// Returns the set of symbols written by a statement.
pub(super) fn stmt_written_symbols(stmt: &Stmt) -> HashSet<SymbolId> {
    match stmt {
        Stmt::Assign { left, .. } => expr_read_symbols(left),
        Stmt::AssignMany { left, .. } => left.iter().flat_map(expr_read_symbols).collect(),
        Stmt::SetList { table, .. } => HashSet::from([*table]),
        Stmt::Call(_) | Stmt::OpenCell { .. } | Stmt::StoreCell { .. } => HashSet::new(),
        Stmt::LoadCell { target, .. } => HashSet::from([*target]),
        Stmt::Phi(_) => {
            unreachable!("phi nodes should have been unfolded at this point")
        }
    }
}
