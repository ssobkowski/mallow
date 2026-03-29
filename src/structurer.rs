use std::collections::HashMap;

use smol_str::format_smolstr;

use crate::{
    ast::{Block, Expr, Identifier, Literal, Parameter, Stmt, TableItem, UnOp},
    hil::{
        StructuredFunction,
        cflow::{
            graph::ControlFlowGraph,
            region::{RegionBlock, RegionNode},
        },
        ir::{HilExpr, HilStmt, HilTableItem},
        lifter::ssa::SymbolId,
    },
    scopes::Scopes,
};

struct Structurer {
    functions: Vec<StructuredFunction>,
    entry: usize,

    scopes: Scopes<SymbolId, ()>,
    names: HashMap<(usize, SymbolId), Identifier>,
    current_func: usize,
}

pub fn structure(functions: Vec<StructuredFunction>, entry: usize) -> Block {
    let mut st = Structurer {
        functions,
        entry,
        scopes: Scopes::new(),
        names: HashMap::new(),
        current_func: entry,
    };

    st.visit_entry()
}

impl Structurer {
    fn visit_entry(&mut self) -> Block {
        self.visit_function(self.entry)
    }

    fn visit_function(&mut self, index: usize) -> Block {
        let old_func = self.current_func;
        self.current_func = index;

        let fun = &self.functions[index].clone();

        self.scopes.push_scope();
        for &sym in &fun.cfg.upvalues {
            self.scopes.declare(sym, ());
        }

        let block = self.visit_region(&fun.root, &fun.cfg);
        self.scopes.pop_scope();

        self.current_func = old_func;
        block
    }

    fn get_symbol_name(&mut self, sym: &SymbolId) -> Identifier {
        if let Some(name) = self.names.get(&(self.current_func, *sym)) {
            return name.clone();
        }

        let name = Identifier::new(format_smolstr!("v{}", sym.index()));
        self.names.insert((self.current_func, *sym), name.clone());
        name
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
                let var = self.get_symbol_name(start);
                let start = Expr::Named(self.get_symbol_name(start));
                let end = Expr::Named(self.get_symbol_name(end));
                let step = Some(Expr::Named(self.get_symbol_name(step)));

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
                let vars = vars.iter().map(|s| self.get_symbol_name(s)).collect();
                let exprs = exprs
                    .iter()
                    .map(|sym| Expr::Named(self.get_symbol_name(sym)))
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
                let mut needs_declaration = false;
                let left_expr = match left {
                    HilExpr::Symbol(sym) => {
                        if !self.scopes.contains(sym) {
                            self.scopes.declare(*sym, ());
                            needs_declaration = true;
                        }
                        Expr::Named(self.get_symbol_name(sym))
                    }
                    _ => self.visit_expr(left),
                };
                let right = self.visit_expr(value);

                if needs_declaration {
                    let Expr::Named(name) = left_expr else {
                        unreachable!("Symbol was not visited as Named");
                    };
                    Stmt::LocalDeclaration {
                        names: vec![name],
                        values: vec![right],
                    }
                } else {
                    Stmt::Assignment {
                        lhs: vec![left_expr],
                        rhs: vec![right],
                    }
                }
            }
            HilStmt::AssignMany { left, value } => {
                let all_declared = left.iter().all(|sym| self.scopes.contains(sym));

                let names: Vec<_> = left.iter().map(|s| self.get_symbol_name(s)).collect();
                let right = self.visit_expr(value);

                if all_declared {
                    Stmt::Assignment {
                        lhs: names.into_iter().map(Expr::Named).collect(),
                        rhs: vec![right],
                    }
                } else {
                    for sym in left {
                        self.scopes.declare(*sym, ());
                    }
                    Stmt::LocalDeclaration {
                        names,
                        values: vec![right],
                    }
                }
            }
            HilStmt::SetField { table, key, value } => Stmt::Assignment {
                lhs: vec![Expr::Field {
                    base: Box::new(self.visit_expr(&HilExpr::Symbol(*table))),
                    field: Identifier::new(key.clone()),
                }],
                rhs: vec![self.visit_expr(value)],
            },
            HilStmt::SetList {
                table,
                index,
                values,
                has_variadic_tail,
            } => {
                let table_expr = self.visit_expr(&HilExpr::Symbol(*table));
                if *has_variadic_tail {
                    // The idea is that if we have a variadic tail, we can't simply assign
                    // a tuple to a single index (t[k] = a, b)
                    //
                    // We create a temporary table and then copy the contents of it into the
                    // true table with `table.move`
                    //
                    // TODO: This is technically subject to some kind of global poisoning attack, so
                    // perhaps a better way to handle this would be to have a pass before structuring
                    // and after inlining that unfolds such SetLists into normal table constructors.

                    let temp_table_ident = Identifier::new("__t");
                    Stmt::Do {
                        body: Block::with_stmts(vec![
                            Stmt::LocalDeclaration {
                                names: vec![temp_table_ident.clone()],
                                values: vec![Expr::Table {
                                    items: values
                                        .iter()
                                        .map(|v| TableItem::Implicit {
                                            value: self.visit_expr(v),
                                        })
                                        .collect(),
                                }],
                            },
                            Stmt::Expression {
                                expr: Expr::FunctionCall {
                                    func: Box::new(Expr::Field {
                                        base: Box::new(Expr::Named(Identifier::new("table"))),
                                        field: Identifier::new("move"),
                                    }),
                                    args: vec![
                                        Expr::Named(temp_table_ident.clone()),
                                        Expr::Literal(Literal::Number(1.0)),
                                        Expr::Unary {
                                            op: UnOp::Length,
                                            expr: Box::new(Expr::Named(temp_table_ident)),
                                        },
                                        Expr::Literal(Literal::Number(*index as f64)),
                                        table_expr,
                                    ],
                                },
                            },
                        ]),
                    }
                } else {
                    let base = *index as usize;
                    let lhs = (base..base + values.len())
                        .map(|i| Expr::Index {
                            base: Box::new(table_expr.clone()),
                            index: Box::new(Expr::Literal(Literal::Number(i as f64))),
                        })
                        .collect();
                    let rhs = values.iter().map(|v| self.visit_expr(v)).collect();

                    Stmt::Assignment { lhs, rhs }
                }
            }
            HilStmt::Call(expr) => Stmt::Expression {
                expr: self.visit_expr(expr),
            },
            HilStmt::Phi(node) => {
                panic!(
                    "encountered unfolded phi node during structuring: target={}, operands={:?}",
                    node.target.index(),
                    node.operands
                )
            }
        }
    }

    fn visit_expr(&mut self, expr: &HilExpr) -> Expr {
        match expr {
            HilExpr::Nil => Expr::Literal(Literal::Nil),
            HilExpr::Number(num) => Expr::Literal(Literal::Number(*num)),
            HilExpr::String(s) => Expr::Literal(Literal::String(s.into())),
            HilExpr::Bool(b) => Expr::Literal(Literal::Bool(*b)),
            HilExpr::Symbol(sym) => Expr::Named(self.get_symbol_name(sym)),
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
            HilExpr::Global(name) => Expr::Named(Identifier::new(name.clone())),
            HilExpr::Import(import) => Expr::Named(Identifier::new(import.clone())),
            HilExpr::GetField { obj, field } => Expr::Field {
                base: Box::new(self.visit_expr(obj)),
                field: Identifier::new(field.clone()),
            },
            HilExpr::GetIndex { obj, index } => Expr::Index {
                base: Box::new(self.visit_expr(obj)),
                index: Box::new(self.visit_expr(index)),
            },
            HilExpr::Call { fun, args } => Expr::FunctionCall {
                func: Box::new(self.visit_expr(fun)),
                args: args.iter().map(|expr| self.visit_expr(expr)).collect(),
            },
            HilExpr::MethodCall {
                object,
                method,
                args,
            } => Expr::MethodCall {
                object: Box::new(self.visit_expr(object)),
                method: Identifier::new(method.clone()),
                args: args.iter().map(|expr| self.visit_expr(expr)).collect(),
            },
            HilExpr::Table { items } => Expr::Table {
                items: self.visit_table_items(items),
            },
            HilExpr::VarArgs => Expr::Vararg,
        }
    }

    fn visit_table_items(&mut self, items: &[HilTableItem]) -> Vec<TableItem> {
        items
            .iter()
            .map(|item| match item {
                HilTableItem::List(expr) => TableItem::Implicit {
                    value: self.visit_expr(expr),
                },
                HilTableItem::Index(key, value) => TableItem::Indexed {
                    index: self.visit_expr(key),
                    value: self.visit_expr(value),
                },
                HilTableItem::Packed(expr) => TableItem::Implicit {
                    value: self.visit_expr(expr),
                },
            })
            .collect()
    }

    fn visit_closure(&mut self, proto_idx: usize, captures: &[SymbolId]) -> Expr {
        let parent_names: Vec<_> = captures
            .iter()
            .map(|sym| self.get_symbol_name(sym))
            .collect();

        let child_fun = &self.functions[proto_idx];
        for (i, name) in parent_names.into_iter().enumerate() {
            if let Some(&child_upval_sym) = child_fun.cfg.upvalues.get(i) {
                self.names.insert((proto_idx, child_upval_sym), name);
            }
        }

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
