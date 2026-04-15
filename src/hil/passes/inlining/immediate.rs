use crate::{
    hil::{
        StructuredFunction,
        cflow::graph::Block,
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
}

impl VisitorMut for Inliner {
    fn visit_block(&mut self, _: usize, block: &mut Block) {
        if block.stmts.is_empty() {
            return;
        }

        let mut i = 0;
        while i < block.stmts.len() - 1 {
            let candidate = if let HilStmt::Assign { left, value } = &block.stmts[i].inner
                && let HilExpr::Symbol(sym) = left
            {
                (*sym, value)
            } else {
                i += 1;
                continue;
            };

            let sym = candidate.0;
            if self.vars.get(&sym).is_some_and(|v| v.read_count == 1)
                && appears_once(sym, &block.stmts[i + 1].inner)
                && let Some(inlined) = substitute_exact(&block.stmts[i + 1].inner, candidate)
            {
                eprintln!("Chain:");
                eprintln!("  {}", block.stmts[i].inner);
                eprintln!("  {}", block.stmts[i + 1].inner);
                eprintln!("is inlineable into");
                eprintln!("  {}", inlined);
                eprintln!();

                block.stmts.get_mut(i).unwrap().inner = inlined;
                block.stmts.remove(i + 1);

                self.was_changed = true;

                // i is now at the place of the next stmt
                return;
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

fn substitute_exact(stmt: &HilStmt, var: (SymbolId, &HilExpr)) -> Option<HilStmt> {
    let mut cloned = stmt.clone();

    let mut rewriter = StmtRewriter {
        sym: var.0,
        expr: var.1,
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
        let analysis = Analyzer::analyze_function(fun);
        let mut inliner = Inliner::with_vars(analysis);
        inliner.visit_function(fun);
        if !inliner.was_changed {
            break;
        }
    }
}
