use std::collections::HashSet;

use crate::hil::{
    cflow::region::RegionNode,
    ir::HilExpr,
    lifter::ssa::SymbolId,
    visitor::{Visitor, walk_expr},
};

#[derive(Default)]
pub struct ReadCollector {
    symbols: HashSet<SymbolId>,
}

impl ReadCollector {
    pub fn in_region(nodes: &[RegionNode]) -> HashSet<SymbolId> {
        let mut collector = ReadCollector::default();
        for node in nodes {
            collector.visit_region(node);
        }
        collector.symbols
    }

    pub fn in_expr(expr: &HilExpr) -> HashSet<SymbolId> {
        let mut collector = ReadCollector::default();
        collector.visit_expr(expr);
        collector.symbols
    }

    pub fn in_exprs<'a, I: IntoIterator<Item = &'a HilExpr>>(exprs: I) -> HashSet<SymbolId> {
        let mut collector = ReadCollector::default();
        for expr in exprs {
            collector.visit_expr(expr);
        }
        collector.symbols
    }
}

impl Visitor for ReadCollector {
    /// Override lvalue traversal so that plain symbol write targets are *not* collected as reads.
    /// Sub-expressions of compound lvalues (`t[k]`, `t.field`) are still traversed as reads.
    fn visit_lvalue_expr(&mut self, expr: &HilExpr) {
        match expr {
            HilExpr::Symbol(_) => {}
            HilExpr::GetField { obj, .. } => self.visit_expr(obj),
            HilExpr::GetIndex { obj, index } => {
                self.visit_expr(obj);
                self.visit_expr(index);
            }
            other => walk_expr(self, other),
        }
    }

    fn visit_symbol(&mut self, sym: SymbolId) {
        self.symbols.insert(sym);
    }

    fn visit_capture(&mut self, _index: usize, sym: SymbolId) {
        self.symbols.insert(sym);
    }
}
