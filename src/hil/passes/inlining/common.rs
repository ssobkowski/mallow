use crate::{
    hil::{
        StructuredFunction,
        cflow::region::RegionNode,
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
        passes::visitor::{Visitor, walk_expr, walk_function, walk_region},
    },
    scopes::Scope,
};

#[derive(Debug, Clone)]
pub struct Var {
    pub write_count: usize,
    pub read_count: usize,
    pub disqualified: bool,
    /// The last expression that assigned to this variable.
    pub expr: HilExpr,
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
pub struct Analyzer {
    vars: Scope<SymbolId, Var>,
}

impl Visitor for Analyzer {
    fn visit_function(&mut self, fun: &StructuredFunction) {
        // Parameters are inlined into themselves - essentially they need to be present
        // in the vars array (see `is_inlinable_rhs`) and because they have no underlying
        // value this just allows us to skip bindings like `v{N} = p{N}`.
        for param in &fun.cfg.params {
            self.vars.declare(*param, Var::new(HilExpr::Symbol(*param)));
        }

        for upvalue in &fun.upvalues {
            // This can be inserted as a dummy expression, because upvalues are NEVER to be inlined.
            let mut var = Var::new(HilExpr::Nil);
            var.disqualified = true;
            self.vars.declare(*upvalue, var);
        }

        walk_function(self, fun);
    }

    fn visit_block(&mut self, stmts: &[HilStmt]) {
        for stmt in stmts {
            match &stmt {
                HilStmt::Assign {
                    left: HilExpr::Symbol(sym),
                    value,
                } => {
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
                HilStmt::AssignMany { left, value } => {
                    // Block all tuple-assigns from being inlined. This can only be done in the
                    // (TODO) "immediate use" pass.
                    for sym in left {
                        match self.vars.get_mut(sym) {
                            Some(var) => {
                                var.write_count += 1;
                                var.disqualified = true;
                            }
                            None => {
                                // Initialize with a dummy expression, but immediately mark as not a candidate
                                let mut var = Var::new(HilExpr::Nil);
                                var.disqualified = true;
                                self.vars.declare(*sym, var);
                            }
                        }
                    }

                    self.visit_expr(value);
                    continue;
                }
                _ => {
                    self.visit_stmt(stmt);
                }
            }
        }
    }

    fn visit_region(&mut self, node: &RegionNode) {
        match node {
            RegionNode::NumericFor { var, .. } => {
                if let Some(existing) = self.vars.get_mut(var) {
                    existing.write_count += 1;
                } else {
                    self.vars.declare(*var, Var::new(HilExpr::Symbol(*var)));
                }
            }
            RegionNode::GenericFor { vars, .. } => {
                for var in vars {
                    if let Some(existing) = self.vars.get_mut(var) {
                        existing.write_count += 1;
                    } else {
                        self.vars.declare(*var, Var::new(HilExpr::Symbol(*var)));
                    }
                }
            }
            _ => {}
        }

        walk_region(self, node);
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

    fn visit_capture(&mut self, _: usize, sym: SymbolId) {
        if let Some(v) = self.vars.get_mut(&sym) {
            v.disqualified = true;
        }
    }
}

impl Analyzer {
    pub fn analyze_function(fun: &StructuredFunction) -> Scope<SymbolId, Var> {
        let mut analyzer = Analyzer::default();
        analyzer.visit_function(fun);
        analyzer.vars
    }
}
