use crate::{
    hil::{
        StructuredFunction,
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
        passes::inlining::common::{Analyzer, Var},
        visitor::{VisitorMut, walk_block_mut, walk_expr_mut},
    },
    scopes::Scope,
};

struct Inliner {
    vars: Scope<SymbolId, Var>,
    was_changed: bool,
}

impl Inliner {
    fn with_vars(vars: Scope<SymbolId, Var>) -> Self {
        Self {
            vars,
            was_changed: false,
        }
    }

    fn can_inline(&self, var: &Var) -> bool {
        !var.disqualified
            && var.write_count == 1
            && var.read_count == 1
            && self.is_inlinable_rhs(&var.expr)
    }

    fn is_inlinable_rhs(&self, expr: &HilExpr) -> bool {
        // TODO: Check the todo in `hil::common::invert_condition`. This can be applied here (i think)
        match expr {
            // A symbol can be inlined only when its value is stable for the whole function.
            // Otherwise a copied temporary can capture an old value and become wrong after
            // substitutions (for example, when doing a swap via a temporary).
            HilExpr::Symbol(sym) => self
                .vars
                .get(sym)
                .is_some_and(|v| !v.disqualified && v.write_count == 1),
            HilExpr::Number(_)
            | HilExpr::String(_)
            | HilExpr::Bool(_)
            | HilExpr::Global(_)
            | HilExpr::Import(_)
            | HilExpr::Nil => true,
            HilExpr::Binary { lhs, rhs, .. }
                if self.is_inlinable_rhs(lhs) && self.is_inlinable_rhs(rhs) =>
            {
                true
            }
            HilExpr::Unary { expr, .. } if self.is_inlinable_rhs(expr) => true,
            _ => false,
        }
    }
}

impl VisitorMut for Inliner {
    fn visit_block(&mut self, stmts: &mut Vec<HilStmt>) {
        stmts.retain(|stmt| {
            if let HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                ..
            } = &stmt
                && let Some(v) = self.vars.get(sym)
                && self.can_inline(v)
            {
                // Remove the assignment as it's getting inlined
                self.was_changed = true;
                return false;
            }

            true
        });

        walk_block_mut(self, stmts);
    }

    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Symbol(sym) = expr
            && let Some(v) = self.vars.get(sym)
            && self.can_inline(v)
            && !v.expr.reads_symbol(sym)
        {
            self.was_changed = true;
            *expr = v.expr.clone();

            self.visit_expr(expr);
            return;
        }

        walk_expr_mut(self, expr);
    }
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut changed = false;
    loop {
        let vars = Analyzer::analyze_function(fun);

        let mut inliner = Inliner::with_vars(vars);
        inliner.visit_function(fun);

        if !inliner.was_changed {
            break;
        }
        changed = true
    }

    changed
}
