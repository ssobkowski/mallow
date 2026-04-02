use crate::{
    hil::{
        StructuredFunction,
        cflow::graph::{Block, ControlFlowGraph},
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
        passes::visitor::{Visitor, VisitorMut, walk_block_mut, walk_expr, walk_expr_mut},
    },
    scopes::Scope,
};

#[derive(Debug, Clone)]
struct Var {
    write_count: usize,
    read_count: usize,
    disqualified: bool,
    /// The last expression that assigned to this variable.
    expr: HilExpr,
}

impl Var {
    fn new(expr: HilExpr) -> Self {
        Self {
            write_count: 1,
            read_count: 0,
            disqualified: false,
            expr,
        }
    }
}

#[derive(Default)]
struct Analyzer {
    vars: Scope<SymbolId, Var>,
}

impl Visitor for Analyzer {
    fn visit_block(&mut self, _: usize, block: &Block, cfg: &ControlFlowGraph) {
        for up in &cfg.upvalues {
            // This can be inserted as a dummy expression, because upvalues are NEVER to be inlined.
            let mut var = Var::new(HilExpr::Nil);
            var.disqualified = true;
            self.vars.declare(*up, var);
        }

        for stmt in &block.stmts {
            if let HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                value,
            } = &stmt.inner
            {
                match self.vars.get_mut(sym) {
                    Some(var) => {
                        var.write_count += 1;
                        var.expr = value.clone();
                    }
                    None => {
                        self.vars.declare(*sym, Var::new(value.clone()));
                    }
                }

                // Manually visit the rvalue of the assignments, as we would visit the same
                // stmt twice if we delegated this whole stmt to the `visit_stmt_spanned` below.
                self.visit_expr(value);
                continue;
            }

            self.visit_stmt_spanned(stmt);
        }
    }

    fn visit_expr(&mut self, expr: &HilExpr) {
        if let HilExpr::Symbol(sym) = expr
            && let Some(var) = self.vars.get_mut(sym)
        {
            var.read_count += 1;
            return;
        }

        walk_expr(self, expr);
    }

    fn visit_binding_symbol(&mut self, sym: SymbolId) {
        // This gets called only on AssignMany. This inliner pass
        // only supports inlining single-assignment variables.
        match self.vars.get_mut(&sym) {
            Some(var) => {
                var.write_count += 1;
                var.disqualified = true;
            }
            None => {
                // Initialize with a dummy expression, but immediately mark as not a candidate
                let mut var = Var::new(HilExpr::Nil);
                var.disqualified = true;
                self.vars.declare(sym, var);
            }
        }
    }

    fn visit_capture(&mut self, _: usize, sym: SymbolId) {
        if let Some(v) = self.vars.get_mut(&sym) {
            v.disqualified = true;
        }
    }
}

impl Analyzer {
    fn analyze_function(fun: &StructuredFunction) -> Scope<SymbolId, Var> {
        let mut analyzer = Analyzer::default();
        analyzer.visit_function(fun);
        analyzer.vars
    }
}

struct Inliner {
    vars: Scope<SymbolId, Var>,
    was_changed: bool,
}

impl Inliner {
    fn can_inline(&self, var: &Var) -> bool {
        !var.disqualified
            && var.write_count == 1
            && var.read_count == 1
            && self.is_inlinable_rhs(&var.expr)
    }

    fn is_inlinable_rhs(&self, expr: &HilExpr) -> bool {
        // TODO: Check the todo in `hil::common::invert_condition`. This can be applied here (i think)
        match expr {
            // A symbol can be inlined if it's not an upvalue, ie. if this symbol is a potential candidate
            HilExpr::Symbol(sym) => self.vars.get(sym).is_some_and(|v| !v.disqualified),
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
    fn visit_block(&mut self, block_id: usize, block: &mut Block) {
        block.stmts.retain(|stmt| {
            if let HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                ..
            } = &stmt.inner
                && let Some(v) = self.vars.get(sym)
                && self.can_inline(v)
            {
                // Remove the assignment as it's getting inlined
                self.was_changed = true;
                return false;
            }

            true
        });

        walk_block_mut(self, block_id, block);
    }

    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Symbol(sym) = expr
            && let Some(v) = self.vars.get(sym)
            && self.can_inline(v)
        {
            self.was_changed = true;
            *expr = v.expr.clone();

            self.visit_expr(expr);
            return;
        }

        walk_expr_mut(self, expr);
    }
}

pub fn run(fun: &mut StructuredFunction) {
    loop {
        let vars = Analyzer::analyze_function(fun);
        let mut inliner = Inliner {
            vars,
            was_changed: false,
        };
        inliner.visit_function(fun);
        if !inliner.was_changed {
            break;
        }
    }
}
