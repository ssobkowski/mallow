use crate::{
    hil::{
        StructuredFunction,
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
        passes::{
            inlining::common::{Analyzer, Var},
            visitor::{Visitor, VisitorMut, walk_expr_mut, walk_stmt_mut},
        },
    },
    scopes::Scope,
};

struct StmtRewriter<'a> {
    sym: SymbolId,
    expr: &'a HilExpr,

    change_count: usize,
}

impl<'a> VisitorMut for StmtRewriter<'a> {
    fn visit_stmt(&mut self, stmt: &mut HilStmt) {
        if let HilStmt::Assign { value, .. } = stmt {
            walk_expr_mut(self, value);
            return;
        }
        walk_stmt_mut(self, stmt);
    }

    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Symbol(s) = expr
            && *s == self.sym
        {
            *expr = self.expr.clone();
            self.change_count += 1;
            return;
        }

        walk_expr_mut(self, expr);
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
}

impl VisitorMut for Inliner {
    fn visit_block(&mut self, stmts: &mut Vec<HilStmt>) {
        if stmts.is_empty() {
            return;
        }

        let mut i = 0;
        while i < stmts.len() - 1 {
            let (sym, value) = if let HilStmt::Assign { left, value } = &stmts[i]
                && let HilExpr::Symbol(sym) = left
            {
                (*sym, value)
            } else {
                i += 1;
                continue;
            };

            if self.vars.get(&sym).is_some_and(|v| v.read_count == 1)
                && appears_once(sym, &stmts[i + 1])
                && let Some(inlined) = substitute_exact(&stmts[i + 1], sym, value)
            {
                eprintln!("Chain:");
                eprintln!("  {}", stmts[i]);
                eprintln!("  {}", stmts[i + 1]);
                eprintln!("is inlineable into");
                eprintln!("  {}", inlined);
                eprintln!();

                *stmts.get_mut(i).unwrap() = inlined;
                stmts.remove(i + 1);

                self.was_changed = true;

                // i is now at the place of the next stmt
                continue;
            }

            i += 1;
        }
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

fn substitute_exact(stmt: &HilStmt, sym: SymbolId, expr: &HilExpr) -> Option<HilStmt> {
    let mut cloned = stmt.clone();

    let mut rewriter = StmtRewriter {
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

fn appears_once(sym: SymbolId, stmt: &HilStmt) -> bool {
    let mut walker = Walker { sym, count: 0 };
    walker.visit_stmt(stmt);
    walker.count == 1
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
