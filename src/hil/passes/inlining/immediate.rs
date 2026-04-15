use crate::{
    hil::{
        StructuredFunction,
        cflow::region::RegionNode,
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
        passes::{
            inlining::common::{Analyzer, Var},
            visitor::{Visitor, VisitorMut, walk_expr_mut, walk_region_mut, walk_stmt_mut},
        },
    },
    scopes::Scope,
};

struct SingleSymbolRewriter<'a> {
    sym: SymbolId,
    expr: &'a HilExpr,
    change_count: usize,
}

impl<'a> VisitorMut for SingleSymbolRewriter<'a> {
    fn visit_stmt(&mut self, stmt: &mut HilStmt) {
        if let HilStmt::Assign { value, .. } = stmt {
            walk_expr_mut(self, value);
            return;
        }
        walk_stmt_mut(self, stmt);
    }

    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Symbol(s) = expr {
            if *s == self.sym {
                *expr = self.expr.clone();
                self.change_count += 1;
                return;
            }
        }
        walk_expr_mut(self, expr);
    }
}

struct Walker {
    sym: SymbolId,
    count: usize,
}

impl Visitor for Walker {
    fn visit_symbol(&mut self, sym: SymbolId) {
        if sym == self.sym {
            self.count += 1;
        }
    }
}

trait Substitutable: Clone {
    fn appears_in(&self, sym: SymbolId) -> bool;
    fn substitute_exact(&self, sym: SymbolId, expr: &HilExpr) -> Option<Self>;
}

impl Substitutable for HilStmt {
    fn appears_in(&self, sym: SymbolId) -> bool {
        let mut walker = Walker { sym, count: 0 };
        walker.visit_stmt(self);
        walker.count > 0
    }

    fn substitute_exact(&self, sym: SymbolId, expr: &HilExpr) -> Option<Self> {
        let mut cloned = self.clone();
        let mut rewriter = SingleSymbolRewriter {
            sym,
            expr,
            change_count: 0,
        };
        rewriter.visit_stmt(&mut cloned);
        if rewriter.change_count == 1 {
            Some(cloned)
        } else {
            None
        }
    }
}

impl Substitutable for HilExpr {
    fn appears_in(&self, sym: SymbolId) -> bool {
        let mut walker = Walker { sym, count: 0 };
        walker.visit_expr(self);
        walker.count > 0
    }

    fn substitute_exact(&self, sym: SymbolId, expr: &HilExpr) -> Option<Self> {
        let mut cloned = self.clone();
        let mut rewriter = SingleSymbolRewriter {
            sym,
            expr,
            change_count: 0,
        };
        rewriter.visit_expr(&mut cloned);
        if rewriter.change_count == 1 {
            Some(cloned)
        } else {
            None
        }
    }
}

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

    fn try_inline<T: Substitutable>(&self, decl: &HilStmt, target: &T) -> Option<T> {
        let (sym, value) = if let HilStmt::Assign {
            left: HilExpr::Symbol(sym),
            value,
        } = decl
        {
            (*sym, value)
        } else {
            return None;
        };

        if self
            .vars
            .get(&sym)
            .is_some_and(|v| v.read_count == 1 && !v.disqualified)
            && target.appears_in(sym)
        {
            target.substitute_exact(sym, value)
        } else {
            None
        }
    }

    /// Attempts to inline into the first evaluated expression of the next region block
    fn try_apply_to_region_entry(&mut self, decl: &HilStmt, right: &mut RegionNode) -> bool {
        let mut applied = false;

        let mut check_expr = |expr: &mut HilExpr| {
            if !applied {
                if let Some(inlined) = self.try_inline(decl, expr) {
                    *expr = inlined;
                    applied = true;
                }
            }
        };

        match right {
            RegionNode::BasicBlock { stmts } => {
                if let Some(next) = stmts.first_mut() {
                    if let Some(inlined) = self.try_inline(decl, next) {
                        *next = inlined;
                        applied = true;
                    }
                }
            }
            RegionNode::If { condition, .. } | RegionNode::While { condition, .. } => {
                check_expr(condition)
            }
            RegionNode::Return { values } => values.iter_mut().for_each(check_expr),
            RegionNode::NumericFor {
                start, end, step, ..
            } => {
                check_expr(start);
                check_expr(end);
                check_expr(step);
            }
            RegionNode::GenericFor { exprs, .. } => exprs.iter_mut().for_each(check_expr),
            _ => {}
        }

        applied
    }
}

impl VisitorMut for Inliner {
    fn visit_region(&mut self, node: &mut RegionNode) {
        if let RegionNode::Sequence { nodes } = node {
            // First, visit them normally as they are.
            for n in nodes.iter_mut() {
                self.visit_region(n);
            }

            // Then, in case of region edges, for instance `local vN = vM; return vN`
            for i in 0..nodes.len().saturating_sub(1) {
                let (left_slice, right_slice) = nodes.split_at_mut(i + 1);
                let left = &mut left_slice[i];
                let right = &mut right_slice[0];

                if let RegionNode::BasicBlock { stmts: decl_stmts } = left
                    && let Some(decl) = decl_stmts.last().cloned()
                    && self.try_apply_to_region_entry(&decl, right)
                {
                    decl_stmts.pop();
                    self.was_changed = true;
                }
            }
            return;
        }

        walk_region_mut(self, node);
    }

    fn visit_block(&mut self, stmts: &mut Vec<HilStmt>) {
        if stmts.is_empty() {
            return;
        }

        let mut i = 0;
        while i < stmts.len() - 1 {
            let curr = &stmts[i];
            let next = &stmts[i + 1];

            if let Some(inlined) = self.try_inline(curr, next) {
                *stmts.get_mut(i).unwrap() = inlined;
                stmts.remove(i + 1);
                self.was_changed = true;
                continue; // i is now at the place of the next stmt
            }

            i += 1;
        }
    }
}

pub fn run(fun: &mut StructuredFunction) {
    loop {
        let vars = Analyzer::analyze_function(fun);

        let mut inliner = Inliner::with_vars(vars);
        inliner.visit_function(fun);

        if !inliner.was_changed {
            break;
        }
    }
}
