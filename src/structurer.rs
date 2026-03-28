use smol_str::format_smolstr;

use crate::{
    ast::{Block, Expr, Identifier, Literal, Parameter, Stmt},
    hil::{
        StructuredFunction,
        cflow::{
            graph::ControlFlowGraph,
            region::{RegionBlock, RegionNode},
        },
        ir::{HilExpr, HilStmt},
        lifter::symbol::SymbolId,
    },
    scopes::Scopes,
};

struct Structurer {
    functions: Vec<StructuredFunction>,
    entry: usize,

    scopes: Scopes<SymbolId, ()>,
}

pub fn structure(functions: Vec<StructuredFunction>, entry: usize) -> Block {
    let mut st = Structurer {
        functions,
        entry,
        scopes: Scopes::new(),
    };

    st.visit_entry()
}

impl Structurer {
    fn visit_entry(&mut self) -> Block {
        self.visit_function(self.entry)
    }

    fn visit_function(&mut self, index: usize) -> Block {
        let fun = &self.functions[index].clone();

        self.scopes.push_scope();
        let block = self.visit_region(&fun.root, &fun.cfg);
        self.scopes.pop_scope();
        block
    }

    fn visit_region(&mut self, region: &RegionBlock, cfg: &ControlFlowGraph) -> Block {
        let mut stmts = Vec::new();
        for node in &region.nodes {
            self.visit_node(node, cfg, &mut stmts);
        }
        Block::with_stmts(stmts)
    }

    fn visit_node(&mut self, node: &RegionNode, cfg: &ControlFlowGraph, buf: &mut Vec<Stmt>) {
        match node {
            RegionNode::BasicBlock { block } => self.visit_block(*block, cfg, buf),
            RegionNode::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let then_body = self.visit_region(then_branch, cfg);
                let else_body =
                    (!else_branch.nodes.is_empty()).then(|| self.visit_region(else_branch, cfg));

                buf.push(Stmt::If {
                    condition: self.visit_expr(condition),
                    then_body,
                    else_body,
                });
            }
            RegionNode::While {
                condition, body, ..
            } => {
                let body = self.visit_region(body, cfg);
                buf.push(Stmt::While {
                    condition: self.visit_expr(condition),
                    body,
                });
            }
            RegionNode::RepeatUntil {
                condition, body, ..
            } => {
                let body = self.visit_region(body, cfg);
                buf.push(Stmt::Repeat {
                    body,
                    condition: self.visit_expr(condition),
                })
            }
            RegionNode::NumericFor {
                body,
                start,
                end,
                step,
                ..
            } => {
                let var = symbol_ident(start);
                let start = Expr::Named(symbol_ident(start));
                let end = Expr::Named(symbol_ident(end));
                let step = Some(Expr::Named(symbol_ident(step)));

                let body = self.visit_region(body, cfg);
                buf.push(Stmt::NumericFor {
                    var,
                    start,
                    end,
                    step,
                    body,
                })
            }
            RegionNode::GenericFor {
                vars, exprs, body, ..
            } => {
                let vars = vars.iter().map(symbol_ident).collect();
                let exprs = exprs
                    .iter()
                    .map(|sym| Expr::Named(symbol_ident(sym)))
                    .collect();
                let body = self.visit_region(body, cfg);
                buf.push(Stmt::GenericFor { vars, exprs, body });
            }
            RegionNode::Continue => buf.push(Stmt::Continue),
            RegionNode::Break => buf.push(Stmt::Break),
            RegionNode::Return { values } => {
                buf.push(Stmt::Return {
                    values: values.iter().map(|expr| self.visit_expr(expr)).collect(),
                });
            }
        }
    }

    fn visit_block(&mut self, block_idx: usize, cfg: &ControlFlowGraph, buf: &mut Vec<Stmt>) {
        let block = &cfg.blocks[block_idx];

        for stmt in &block.stmts {
            buf.push(self.visit_stmt(&stmt.inner));
        }
    }

    fn visit_stmt(&mut self, stmt: &HilStmt) -> Stmt {
        match stmt {
            HilStmt::Assign { left, value } => {
                let left = match left {
                    HilExpr::Symbol(sym) => {
                        self.scopes.declare(*sym, ());
                        Expr::Named(symbol_ident(sym))
                    }
                    _ => todo!("assignment lhs"),
                };

                let right = self.visit_expr(value);

                Stmt::Assignment {
                    lhs: vec![left],
                    rhs: vec![right],
                }
            }
            HilStmt::AssignMany { left, value } => {
                let left = left.iter().map(|expr| self.visit_expr(expr)).collect();
                let right = self.visit_expr(value);

                Stmt::Assignment {
                    lhs: left,
                    rhs: vec![right],
                }
            }
            HilStmt::SetField { table, key, value } => Stmt::Assignment {
                lhs: vec![Expr::Field {
                    base: Box::new(self.visit_expr(&HilExpr::Symbol(*table))),
                    field: Identifier::new(key.clone()),
                }],
                rhs: vec![self.visit_expr(value)],
            },
            HilStmt::SetList { .. } => {
                panic!("Unimplemented SetList {:#?}", stmt);
            }
            HilStmt::Call(expr) => Stmt::Expression {
                expr: self.visit_expr(expr),
            },
            HilStmt::Phi { target, operands } => {
                panic!(
                    "encountered unfolded phi node during structuring: target={}, operands={:?}",
                    target.index(),
                    operands
                )
            }
            HilStmt::Return(_) => panic!("wild return spotted in the wild"),
        }
    }

    fn visit_expr(&mut self, expr: &HilExpr) -> Expr {
        match expr {
            HilExpr::Nil => Expr::Literal(Literal::Nil),
            HilExpr::Number(num) => Expr::Literal(Literal::Number(*num)),
            HilExpr::String(s) => Expr::Literal(Literal::String(s.into())),
            HilExpr::Bool(b) => Expr::Literal(Literal::Bool(*b)),
            HilExpr::Symbol(sym) => Expr::Named(symbol_ident(sym)),
            HilExpr::Closure { proto, captures } => self.visit_closure(*proto, captures),
            HilExpr::Binary { lhs, op, rhs } => Expr::Binary {
                lhs: Box::new(self.visit_expr(lhs)),
                op: *op,
                rhs: Box::new(self.visit_expr(rhs)),
            },
            HilExpr::Unary { op, expr } => Expr::Unary {
                op: *op,
                expr: Box::new(self.visit_expr(expr)),
            },
            HilExpr::Import(import) => Expr::Named(Identifier::new(import.clone())),
            HilExpr::Call { fun, args } => Expr::FunctionCall {
                func: Box::new(self.visit_expr(fun)),
                args: args.iter().map(|expr| self.visit_expr(expr)).collect(),
            },
            _ => todo!("Visiting Expr: {:#?}", expr),
        }
    }

    fn visit_closure(&mut self, proto_idx: usize, captures: &[SymbolId]) -> Expr {
        let old_scopes = std::mem::take(&mut self.scopes);

        let fun = &self.functions[proto_idx];
        let mut params: Vec<_> = (0..fun.num_params)
            .map(|i| Parameter::Regular(Identifier::new(format_smolstr!("v{}", i))))
            .collect();
        if fun.is_vararg {
            params.push(Parameter::Vararg);
        }

        let body = self.visit_function(proto_idx);

        self.scopes = old_scopes;

        Expr::AnonymousFunction { params, body }
    }
}

fn symbol_ident(sym: &SymbolId) -> Identifier {
    Identifier::new(format_smolstr!("v{}", sym.index()))
}
