use smol_str::SmolStr;

use crate::{
    ast::{Block, Expr, Identifier, Literal, Parameter, Stmt, TableItem},
    disasm::Proto,
    hil::{
        cflow::{
            graph::ControlFlowGraph,
            region::{RegionBlock, RegionNode},
        },
        ir::{HilCapture, HilExpr, HilStmt, HilTableItem},
    },
    scopes::{Scope, ScopeManager},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Var {
    Reg(u8),
    Local(SmolStr),
}

struct Structurer<'a> {
    regions: &'a [RegionBlock],
    cfgs: &'a [ControlFlowGraph],
    entry: usize,
    protos: &'a [Proto],

    scopes: ScopeManager<Var, ()>,

    // upvalue index -> captured register
    upvalues: Scope<u8, u8>,
    // aliases GETUPVALUEs
    register_overrides: ScopeManager<u8, u8>,
}

pub fn structure(
    regions: &[RegionBlock],
    cfgs: &[ControlFlowGraph],
    entry: usize,
    protos: &[Proto],
) -> Block {
    let mut structurer = Structurer {
        regions,
        cfgs,
        entry,
        protos,
        scopes: ScopeManager::new(),
        upvalues: Scope::new(),
        register_overrides: ScopeManager::new(),
    };
    structurer.structure_entry()
}

impl<'a> Structurer<'a> {
    fn structure_entry(&mut self) -> Block {
        self.structure_proto(self.entry, &[])
    }

    fn structure_proto(&mut self, proto_idx: usize, init_vars: &[Var]) -> Block {
        let Some(region) = self.regions.get(proto_idx) else {
            return Block::new();
        };
        let Some(cfg) = self.cfgs.get(proto_idx) else {
            return Block::new();
        };

        self.lower_region_with_init(region, cfg, init_vars)
    }

    fn lower_region(&mut self, region: &RegionBlock, cfg: &ControlFlowGraph) -> Block {
        self.lower_region_with_init(region, cfg, &[])
    }

    fn lower_region_with_init(
        &mut self,
        region: &RegionBlock,
        cfg: &ControlFlowGraph,
        init_vars: &[Var],
    ) -> Block {
        self.scopes.push_scope();
        self.register_overrides.push_scope();
        for var in init_vars {
            self.declare_var(var.clone());
        }
        let mut stmts = Vec::new();
        for node in &region.nodes {
            self.lower_node_into(node, cfg, &mut stmts);
        }
        self.scopes.pop_scope();
        self.register_overrides.pop_scope();
        Block::with_stmts(stmts)
    }

    fn lower_node_into(&mut self, node: &RegionNode, cfg: &ControlFlowGraph, out: &mut Vec<Stmt>) {
        match node {
            RegionNode::BasicBlock { block } => self.lower_basic_block_into(*block, cfg, out),
            RegionNode::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let else_body = if !else_branch.nodes.is_empty() {
                    Some(self.lower_region(else_branch, cfg))
                } else {
                    None
                };
                let then_body = self.lower_region(then_branch, cfg);
                out.push(Stmt::If {
                    condition: self.lower_expr(condition),
                    then_body,
                    else_body,
                });
            }
            RegionNode::While {
                condition, body, ..
            } => {
                let condition = self.lower_expr(condition);
                let body = self.lower_region(body, cfg);
                out.push(Stmt::While { condition, body });
            }
            RegionNode::Continue { .. } => out.push(Stmt::Continue),
            RegionNode::Break { .. } => out.push(Stmt::Break),
            RegionNode::Return { values, .. } => out.push(Stmt::Return {
                values: values.iter().map(|value| self.lower_expr(value)).collect(),
            }),
            RegionNode::NumericFor { base, body, .. } => {
                let step_reg = *base as u8 + 1;
                let step = Some(Expr::Name(local_ident(step_reg)));

                let body = self.lower_region(body, cfg);
                out.push(Stmt::NumericFor {
                    var: local_ident(*base as u8 + 2),
                    start: Expr::Name(local_ident(*base as u8 + 2)),
                    end: Expr::Name(local_ident(*base as u8)),
                    step,
                    body,
                })
            }
            RegionNode::GenericFor {
                base,
                result_count,
                body,
                ..
            } => {
                let mut vars: Vec<_> = (0..*result_count)
                    .map(|i| local_ident(*base as u8 + 3 + i as u8))
                    .collect();
                if vars.is_empty() {
                    vars.push(Identifier::from("_"));
                }

                let body = self.lower_region(body, cfg);
                out.push(Stmt::GenericFor {
                    vars,
                    exprs: vec![
                        Expr::Name(local_ident(*base as u8)),
                        Expr::Name(local_ident(*base as u8 + 1)),
                        Expr::Name(local_ident(*base as u8 + 2)),
                    ],
                    body,
                });
            }
            RegionNode::Jump { .. } => unreachable!("unexpected jump node in structured region"),
        }
    }

    fn lower_basic_block_into(
        &mut self,
        block_idx: usize,
        cfg: &ControlFlowGraph,
        out: &mut Vec<Stmt>,
    ) {
        let Some(block) = cfg.blocks.get(block_idx) else {
            return;
        };

        for stmt in &block.stmts {
            self.lower_stmt_into(&stmt.inner, out);
        }
    }

    fn lower_stmt_into(&mut self, stmt: &HilStmt, out: &mut Vec<Stmt>) {
        match stmt {
            HilStmt::Assign { left, value } => self.lower_assign_into(left, value, out),
            HilStmt::AssignMany { left, value } => {
                let regs: Vec<_> = left.iter().map(local_reg).collect();
                let names: Vec<_> = regs.iter().copied().map(local_ident).collect();
                for reg in regs {
                    self.declare_var(Var::Reg(reg));
                }

                out.push(Stmt::LocalDeclaration {
                    names,
                    values: vec![self.lower_expr(value)],
                });
            }
            HilStmt::SetField { table, key, value } => out.push(Stmt::Assignment {
                lhs: Expr::Index {
                    base: Box::new(Expr::Name(local_ident(self.resolve_reg(*table)))),
                    index: Box::new(Expr::Literal(Literal::String(key.clone()))),
                },
                rhs: self.lower_expr(value),
            }),
            HilStmt::SetList {
                table,
                index,
                values,
                ..
            } => {
                for (offset, value) in values.iter().enumerate() {
                    out.push(Stmt::Assignment {
                        lhs: Expr::Index {
                            base: Box::new(Expr::Name(local_ident(self.resolve_reg(*table)))),
                            index: Box::new(Expr::Literal(Literal::Number(
                                f64::from(*index) + offset as f64,
                            ))),
                        },
                        rhs: self.lower_expr(value),
                    });
                }
            }
            HilStmt::Call(expr) => out.push(Stmt::Expression {
                expr: self.lower_expr(expr),
            }),
            HilStmt::Return(values) => out.push(Stmt::Return {
                values: values.iter().map(|value| self.lower_expr(value)).collect(),
            }),
        }
    }

    fn lower_assign_into(&mut self, left: &HilExpr, value: &HilExpr, out: &mut Vec<Stmt>) {
        let mut force_declaration = false;
        let rhs = match value {
            HilExpr::Upval(up_reg) => {
                // GETUPVAL: alias the destination register to the canonical parent register,
                // because we can't simply reproduce the bytecode's "capture by reference".
                // No statement is emitted; all subsequent reads/writes of dest use the
                // canonical name transparently via resolve_reg.
                let target_reg = match left {
                    HilExpr::Reg(reg) => reg,
                    _ => unimplemented!("assigning upvalue to non-local"),
                };

                let canonical = self.upvalues.get(up_reg).copied().unwrap_or_else(|| {
                    panic!("GETUPVAL references upvalue {up_reg} that is not in the upvalue table")
                });
                self.register_overrides
                    .top_scope_mut()
                    .expect("there must be a scope")
                    .declare(*target_reg, canonical);
                return;
            }
            HilExpr::Call { fun, .. } => {
                // If we call a captured upvalue, we must not override it by accident
                if let HilExpr::Reg(fun_reg) = fun.as_ref()
                    && let Some(alias) = self
                        .register_overrides
                        .top_scope()
                        .expect("there must be a scope")
                        .get(fun_reg)
                {
                    // Only force the declaration if the upvalue wasn't shadowed by a local already
                    // We check for the override as if it's an upvalue, it must have an override and
                    // will not appear as the "true" register.
                    force_declaration = self.scopes.get_var(&Var::Reg(*alias)).is_none();
                };

                self.lower_expr(value)
            }
            _ => self.lower_expr(value),
        };

        match left {
            HilExpr::Reg(reg) => {
                let resolved = self.resolve_reg(*reg);
                let var = Var::Reg(*reg);
                if force_declaration || !self.is_declared(&var) {
                    self.declare_var(var);
                    out.push(Stmt::LocalDeclaration {
                        names: vec![local_ident(resolved)],
                        values: vec![rhs],
                    });
                } else {
                    out.push(Stmt::Assignment {
                        lhs: Expr::Name(local_ident(resolved)),
                        rhs,
                    });
                }
            }
            HilExpr::Local(name) => {
                let var = Var::Local(name.clone());
                if self.is_declared(&var) {
                    out.push(Stmt::Assignment {
                        lhs: Expr::Name(Identifier::from(name.clone())),
                        rhs,
                    });
                } else {
                    self.declare_var(var);
                    out.push(Stmt::LocalDeclaration {
                        names: vec![Identifier::from(name.clone())],
                        values: vec![rhs],
                    });
                }
            }
            HilExpr::Global(name) => out.push(Stmt::Assignment {
                lhs: Expr::Name(Identifier::from(name.clone())),
                rhs,
            }),
            HilExpr::Upval(up) => {
                // SETUPVAL: write back to the canonical parent variable
                let &resolved = self.upvalues.get(up).unwrap_or_else(|| {
                    panic!("SETUPVAL references upvalue {up} that is not in the upvalue table")
                });

                let lhs_name = local_ident(resolved);
                // Skip self-assignments: these arise when SETUPVAL follows a GETUPVAL on the
                // same upvalue/register pair — the aliased write already happened.
                if matches!(&rhs, Expr::Name(n) if n == &lhs_name) {
                    return;
                }

                out.push(Stmt::Assignment {
                    lhs: Expr::Name(lhs_name),
                    rhs,
                });
            }
            HilExpr::GetField { obj, field } => out.push(Stmt::Assignment {
                lhs: Expr::Field {
                    base: Box::new(self.lower_expr(obj)),
                    field: Identifier::from(field.clone()),
                },
                rhs,
            }),
            HilExpr::GetIndex { obj, index } => out.push(Stmt::Assignment {
                lhs: Expr::Index {
                    base: Box::new(self.lower_expr(obj)),
                    index: Box::new(self.lower_expr(index)),
                },
                rhs,
            }),
            _ => unreachable!("unsupported assignment target: {left:?}"),
        }
    }

    fn lower_expr(&mut self, expr: &HilExpr) -> Expr {
        match expr {
            HilExpr::Nil => Expr::Literal(Literal::Nil),
            HilExpr::Number(value) => Expr::Literal(Literal::Number(*value)),
            HilExpr::String(value) => Expr::Literal(Literal::String(value.clone().into())),
            HilExpr::Bool(value) => Expr::Literal(Literal::Bool(*value)),
            HilExpr::Reg(reg) => Expr::Name(local_ident(self.resolve_reg(*reg))),
            HilExpr::Local(name) => Expr::Name(Identifier::from(name.clone())),
            HilExpr::Closure { proto, captures } => self.lower_closure_expr(*proto, captures),
            HilExpr::Global(name) | HilExpr::Import(name) => {
                Expr::Name(Identifier::from(name.clone()))
            }
            HilExpr::GetField { obj, field } => Expr::Field {
                base: Box::new(self.lower_expr(obj)),
                field: Identifier::from(field.clone()),
            },
            HilExpr::GetIndex { obj, index } => Expr::Index {
                base: Box::new(self.lower_expr(obj)),
                index: Box::new(self.lower_expr(index)),
            },
            HilExpr::Call { fun, args } => Expr::FunctionCall {
                func: Box::new(self.lower_expr(fun)),
                args: args.iter().map(|arg| self.lower_expr(arg)).collect(),
            },
            HilExpr::MethodCall {
                object,
                method,
                args,
            } => Expr::MethodCall {
                object: Box::new(self.lower_expr(object)),
                method: Identifier::from(method.clone()),
                args: args.iter().map(|arg| self.lower_expr(arg)).collect(),
            },
            HilExpr::Binary { lhs, op, rhs } => Expr::Binary {
                lhs: Box::new(self.lower_expr(lhs)),
                op: *op,
                rhs: Box::new(self.lower_expr(rhs)),
            },
            HilExpr::Unary { op, expr } => Expr::Unary {
                op: op.clone(),
                expr: Box::new(self.lower_expr(expr)),
            },
            HilExpr::Table { items } => Expr::Table {
                items: items
                    .iter()
                    .map(|item| self.lower_table_item(item))
                    .collect(),
            },
            HilExpr::VarArgs => Expr::Vararg,
            HilExpr::Upval(_) => unreachable!("unexpected upvalue expression"),
        }
    }

    fn lower_closure_expr(&mut self, proto_idx: usize, captures: &[HilCapture]) -> Expr {
        let proto = &self.protos[proto_idx];
        debug_assert_eq!(proto.num_upvals as usize, captures.len());

        let old_upvalues = std::mem::take(&mut self.upvalues);
        let old_overrides = std::mem::take(&mut self.register_overrides);
        let old_scopes = std::mem::take(&mut self.scopes);

        for (up_index, cap) in captures.iter().enumerate() {
            match cap {
                // the proto captures a local from the current frame directly.
                HilCapture::Local(reg) => {
                    self.upvalues.declare(up_index as u8, *reg);
                }
                // the proto re-exports one of our own upvalues. propagate the canonical
                // register so the chain resolves all the way to the outermost declaration.
                HilCapture::Upval(parent_upval_idx) => {
                    let resolved = old_upvalues.get(parent_upval_idx).copied().expect(
                        "closure at proto {proto_idx} captures parent upvalue \
                         {parent_upval_idx} but parent upvalue table has no such entry",
                    );
                    self.upvalues.declare(up_index as u8, resolved);
                }
            }
        }

        let (mut params, param_vars): (Vec<_>, Vec<_>) = (0..proto.num_params)
            .map(|reg| (Parameter::Regular(local_ident(reg)), Var::Reg(reg)))
            .collect();
        if proto.is_vararg {
            params.push(Parameter::Vararg);
        }

        let body = self.structure_proto(proto_idx, &param_vars);

        self.upvalues = old_upvalues;
        self.register_overrides = old_overrides;
        self.scopes = old_scopes;

        Expr::AnonymousFunction { params, body }
    }

    fn lower_table_item(&mut self, item: &HilTableItem) -> TableItem {
        match item {
            HilTableItem::List(value) => TableItem::Implicit {
                value: self.lower_expr(value),
            },
            HilTableItem::Index(index, value) => TableItem::Indexed {
                index: self.lower_expr(index),
                value: self.lower_expr(value),
            },
            HilTableItem::Packed(expr) => TableItem::Implicit {
                value: Expr::FunctionCall {
                    func: Box::new(Expr::Field {
                        base: Box::new(Expr::Name("table".into())),
                        field: "unpack".into(),
                    }),
                    args: vec![self.lower_expr(expr)],
                },
            },
        }
    }

    fn declare_var(&mut self, var: Var) {
        if !self.is_declared(&var) && !self.scopes.declare_var(var.clone(), ()) {
            panic!("failed to declare variable {:?}", var);
        }
    }

    fn is_declared(&self, var: &Var) -> bool {
        match var {
            Var::Reg(reg) => {
                self.register_overrides
                    .top_scope()
                    .expect("there must be a scope")
                    .get(reg)
                    .is_some()
                    || self.scopes.get_var(var).is_some()
            }
            Var::Local(_) => self.scopes.get_var(var).is_some(),
        }
    }

    fn resolve_reg(&self, reg: u8) -> u8 {
        self.register_overrides
            .top_scope()
            .expect("there must be a scope")
            .get(&reg)
            .copied()
            .unwrap_or(reg)
    }
}

fn local_ident(reg: u8) -> Identifier {
    Identifier::from(format!("r{reg}"))
}

fn local_reg(expr: &HilExpr) -> u8 {
    match expr {
        HilExpr::Reg(reg) => *reg,
        _ => unreachable!("expected local register, got {expr:?}"),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{Expr as AstExpr, Literal as AstLiteral, Stmt as AstStmt},
        disasm::Proto,
        hil::{
            cflow::{
                graph::{Block as CfgBlock, BlockExit, ControlFlowGraph},
                region::{RegionBlock, RegionNode},
            },
            ir::{HilExpr, HilStmt, Spanned},
        },
        structurer::structure,
    };

    #[test]
    fn structure_lowers_straight_line_region() {
        let cfg = ControlFlowGraph::new(
            vec![CfgBlock::new(
                0,
                vec![Spanned::new(
                    HilStmt::Assign {
                        left: HilExpr::Reg(0),
                        value: HilExpr::Number(1.0),
                    },
                    0,
                )],
                BlockExit::Return(Vec::new()),
            )],
            0,
        );
        let region = RegionBlock {
            nodes: vec![
                RegionNode::BasicBlock { block: 0 },
                RegionNode::Return {
                    from_block: 0,
                    values: Vec::new(),
                },
            ],
        };

        let ast = structure(&[region], &[cfg], 0, &[Proto::default()]);

        assert_eq!(ast.stmts.len(), 2);
        assert!(matches!(
            &ast.stmts[0],
            AstStmt::LocalDeclaration { names, values }
                if names.len() == 1
                    && names[0].as_str() == "r0"
                    && matches!(values.as_slice(), [AstExpr::Literal(AstLiteral::Number(value))] if *value == 1.0)
        ));
        assert!(matches!(&ast.stmts[1], AstStmt::Return { values } if values.is_empty()));
    }

    #[test]
    fn structure_lowers_if_region() {
        let cfg = ControlFlowGraph::new(
            vec![
                CfgBlock::new(
                    0,
                    Vec::new(),
                    BlockExit::CondJump {
                        cond: HilExpr::Reg(0),
                        then_block: 1,
                        else_block: 2,
                    },
                ),
                CfgBlock::new(
                    1,
                    vec![Spanned::new(
                        HilStmt::Assign {
                            left: HilExpr::Reg(1),
                            value: HilExpr::Bool(true),
                        },
                        1,
                    )],
                    BlockExit::Jump(3),
                ),
                CfgBlock::new(
                    2,
                    vec![Spanned::new(
                        HilStmt::Assign {
                            left: HilExpr::Reg(2),
                            value: HilExpr::Bool(false),
                        },
                        2,
                    )],
                    BlockExit::Jump(3),
                ),
                CfgBlock::new(3, Vec::new(), BlockExit::Return(Vec::new())),
            ],
            0,
        );
        let region = RegionBlock {
            nodes: vec![
                RegionNode::If {
                    header: 0,
                    condition: HilExpr::Reg(0),
                    then_branch: RegionBlock {
                        nodes: vec![RegionNode::BasicBlock { block: 1 }],
                    },
                    else_branch: RegionBlock {
                        nodes: vec![RegionNode::BasicBlock { block: 2 }],
                    },
                    merge_block: Some(3),
                },
                RegionNode::Return {
                    from_block: 3,
                    values: Vec::new(),
                },
            ],
        };

        let ast = structure(&[region], &[cfg], 0, &[Proto::default()]);

        assert_eq!(ast.stmts.len(), 2);
        let AstStmt::If {
            condition,
            then_body,
            else_body,
        } = &ast.stmts[0]
        else {
            panic!("expected if statement");
        };
        assert!(matches!(condition, AstExpr::Name(name) if name.as_str() == "r0"));
        assert!(matches!(
            then_body.stmts.as_slice(),
            [AstStmt::LocalDeclaration { names, .. }] if names[0].as_str() == "r1"
        ));
        let else_body = else_body.as_ref().expect("expected else branch");
        assert!(matches!(
            else_body.stmts.as_slice(),
            [AstStmt::LocalDeclaration { names, .. }] if names[0].as_str() == "r2"
        ));
    }

    #[test]
    fn structure_lowers_generic_for_and_emits_preheader_assignments() {
        let cfg = ControlFlowGraph::new(
            vec![
                CfgBlock::new(
                    0,
                    vec![
                        Spanned::new(
                            HilStmt::Assign {
                                left: HilExpr::Reg(0),
                                value: HilExpr::Table { items: Vec::new() },
                            },
                            0,
                        ),
                        Spanned::new(
                            HilStmt::Assign {
                                left: HilExpr::Reg(1),
                                value: HilExpr::Reg(0),
                            },
                            1,
                        ),
                        Spanned::new(
                            HilStmt::Assign {
                                left: HilExpr::Reg(2),
                                value: HilExpr::Nil,
                            },
                            2,
                        ),
                        Spanned::new(
                            HilStmt::Assign {
                                left: HilExpr::Reg(3),
                                value: HilExpr::Nil,
                            },
                            3,
                        ),
                    ],
                    BlockExit::ForGPrep {
                        base: 1,
                        loop_block: 1,
                    },
                ),
                CfgBlock::new(
                    1,
                    Vec::new(),
                    BlockExit::ForGLoop {
                        base: 1,
                        body_block: 1,
                        exit_block: 2,
                        result_count: 2,
                    },
                ),
                CfgBlock::new(2, Vec::new(), BlockExit::Return(Vec::new())),
            ],
            0,
        );
        let region = RegionBlock {
            nodes: vec![
                RegionNode::BasicBlock { block: 0 },
                RegionNode::GenericFor {
                    header: 0,
                    base: 1,
                    result_count: 2,
                    body: RegionBlock::default(),
                    exit_block: 2,
                },
                RegionNode::Return {
                    from_block: 2,
                    values: Vec::new(),
                },
            ],
        };

        let ast = structure(&[region], &[cfg], 0, &[Proto::default()]);

        assert_eq!(ast.stmts.len(), 6);
        assert!(matches!(
            &ast.stmts[0],
            AstStmt::LocalDeclaration { names, .. }
                if matches!(names.as_slice(), [name] if name.as_str() == "r0")
        ));
        assert!(matches!(
            &ast.stmts[1],
            AstStmt::LocalDeclaration { names, .. }
                if matches!(names.as_slice(), [name] if name.as_str() == "r1")
        ));
        assert!(matches!(
            &ast.stmts[2],
            AstStmt::LocalDeclaration { names, .. }
                if matches!(names.as_slice(), [name] if name.as_str() == "r2")
        ));
        assert!(matches!(
            &ast.stmts[3],
            AstStmt::LocalDeclaration { names, .. }
                if matches!(names.as_slice(), [name] if name.as_str() == "r3")
        ));
        assert!(matches!(
            &ast.stmts[4],
            AstStmt::GenericFor { vars, exprs, .. }
                if vars.len() == 2
                    && vars[0].as_str() == "r4"
                    && vars[1].as_str() == "r5"
                    && exprs.len() == 3
                    && matches!(&exprs[0], AstExpr::Name(name) if name.as_str() == "r1")
                    && matches!(&exprs[1], AstExpr::Name(name) if name.as_str() == "r2")
                    && matches!(&exprs[2], AstExpr::Name(name) if name.as_str() == "r3")
        ));
        assert!(matches!(&ast.stmts[5], AstStmt::Return { values } if values.is_empty()));
    }
}
