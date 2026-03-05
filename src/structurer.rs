use crate::{
    ast::{Block, Expr, Identifier, Literal, Parameter, Stmt, TableConstructorField},
    disasm::Proto,
    hil::{
        cflow::{
            graph::{Block as CfgBlock, BlockExit, ControlFlowGraph},
            region::{RegionBlock, RegionNode},
        },
        ir::{HilExpr, HilStmt},
    },
    scopes::ScopeManager,
};

struct GenericForPreheader<'a> {
    exprs: Vec<&'a HilExpr>,
    consumed_stmt_count: usize,
}

struct Structurer<'a> {
    regions: &'a [RegionBlock],
    cfgs: &'a [ControlFlowGraph],
    entry: usize,
    protos: &'a [Proto],
    scopes: ScopeManager<u8, ()>,
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
    };
    structurer.structure_entry()
}

impl<'a> Structurer<'a> {
    fn structure_entry(&mut self) -> Block {
        self.scopes.push_scope();
        let block = self.structure_proto(self.entry);
        self.scopes.pop_scope();
        block
    }

    fn structure_proto(&mut self, proto_idx: usize) -> Block {
        let Some(region) = self.regions.get(proto_idx) else {
            return Block::new();
        };
        let Some(cfg) = self.cfgs.get(proto_idx) else {
            return Block::new();
        };

        self.scopes.push_scope();
        let block = self.lower_region(region, cfg);
        self.scopes.pop_scope();
        block
    }

    fn lower_region(&mut self, region: &RegionBlock, cfg: &ControlFlowGraph) -> Block {
        let mut stmts = Vec::new();
        self.lower_region_into(region, cfg, &mut stmts);
        Block::with_stmts(stmts)
    }

    fn lower_region_into(
        &mut self,
        region: &RegionBlock,
        cfg: &ControlFlowGraph,
        out: &mut Vec<Stmt>,
    ) {
        for node in &region.nodes {
            self.lower_node_into(node, cfg, out);
        }
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
                let else_body =
                    (!else_branch.nodes.is_empty()).then(|| self.lower_region(else_branch, cfg));
                out.push(Stmt::If {
                    condition: self.lower_expr(condition),
                    then_body: self.lower_region(then_branch, cfg),
                    else_body,
                });
            }
            RegionNode::While {
                condition, body, ..
            } => {
                out.push(Stmt::While {
                    condition: self.lower_expr(condition),
                    body: self.lower_region(body, cfg),
                });
            }
            RegionNode::Continue { .. } => out.push(Stmt::Continue),
            RegionNode::Break { .. } => out.push(Stmt::Break),
            RegionNode::Return { values, .. } => out.push(Stmt::Return {
                values: values.iter().map(|value| self.lower_expr(value)).collect(),
            }),
            RegionNode::NumericFor {
                header, base, body, ..
            } => {
                let block = &cfg.blocks[*header];
                let Some((start, end, step)) = numeric_for_preheader(block, *base) else {
                    panic!("failed to resolve numeric for preheader");
                };
                let step = match self.lower_expr(step) {
                    Expr::Literal(Literal::Number(1.0)) => None,
                    other => Some(other),
                };

                out.push(Stmt::NumericFor {
                    var: local_ident(*base as u8 + 2),
                    start: self.lower_expr(start),
                    end: self.lower_expr(end),
                    step,
                    body: self.lower_region(body, cfg),
                })
            }
            RegionNode::GenericFor {
                header,
                base,
                result_count,
                body,
                ..
            } => {
                let block = &cfg.blocks[*header];
                let Some(preheader) = generic_for_preheader(block, *base) else {
                    panic!("failed to resolve generic for preheader");
                };
                let mut vars: Vec<_> = (0..*result_count)
                    .map(|i| local_ident(*base as u8 + 3 + i as u8))
                    .collect();
                if vars.is_empty() {
                    vars.push(Identifier::from("_"));
                }

                out.push(Stmt::GenericFor {
                    vars,
                    exprs: preheader
                        .exprs
                        .into_iter()
                        .map(|expr| self.lower_expr(expr))
                        .collect(),
                    body: self.lower_region(body, cfg),
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

        for stmt in &block.stmts[..visible_stmt_count(block)] {
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
                    self.declare_local(reg);
                }

                out.push(Stmt::LocalDeclaration {
                    names,
                    values: vec![self.lower_expr(value)],
                });
            }
            HilStmt::SetField { table, key, value } => out.push(Stmt::Assignment {
                lhs: Expr::Index {
                    base: Box::new(Expr::Name(local_ident(*table))),
                    index: Box::new(Expr::Literal(Literal::String(key.clone().into()))),
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
                            base: Box::new(Expr::Name(local_ident(*table))),
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
        let rhs = self.lower_expr(value);
        match left {
            HilExpr::Local(reg) => {
                if self.is_declared(*reg) {
                    out.push(Stmt::Assignment {
                        lhs: Expr::Name(local_ident(*reg)),
                        rhs,
                    });
                } else {
                    self.declare_local(*reg);
                    out.push(Stmt::LocalDeclaration {
                        names: vec![local_ident(*reg)],
                        values: vec![rhs],
                    });
                }
            }
            HilExpr::Global(name) => out.push(Stmt::Assignment {
                lhs: Expr::Name(Identifier::from(name.clone())),
                rhs,
            }),
            HilExpr::Upval(up) => out.push(Stmt::Assignment {
                lhs: Expr::Name(upvalue_ident(*up)),
                rhs,
            }),
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
            HilExpr::CaptureValue(inner) => self.lower_expr(inner),
            HilExpr::Local(reg) => Expr::Name(local_ident(*reg)),
            HilExpr::Upval(up) => Expr::Name(upvalue_ident(*up)),
            HilExpr::Closure { proto, .. } => self.lower_closure_expr(*proto),
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
                fields: items
                    .iter()
                    .map(|item| TableConstructorField::Implicit {
                        value: self.lower_expr(item),
                    })
                    .collect(),
            },
            HilExpr::VarArgs => Expr::Vararg,
        }
    }

    fn lower_closure_expr(&mut self, proto_idx: usize) -> Expr {
        let proto = &self.protos[proto_idx];
        let params = proto_parameters(proto);
        let body = self.structure_proto(proto_idx);
        Expr::AnonymousFunction { params, body }
    }

    fn declare_local(&mut self, reg: u8) {
        if !self.is_declared(reg) {
            self.scopes.declare_var(reg, ());
        }
    }

    fn is_declared(&self, reg: u8) -> bool {
        self.scopes.get_var(&reg).is_some()
    }
}

fn local_ident(reg: u8) -> Identifier {
    Identifier::from(format!("r{reg}"))
}

fn upvalue_ident(up: u8) -> Identifier {
    Identifier::from(format!("_up{up}"))
}

fn local_reg(expr: &HilExpr) -> u8 {
    match expr {
        HilExpr::Local(reg) => *reg,
        _ => unreachable!("expected local register, got {expr:?}"),
    }
}

fn proto_parameters(proto: &Proto) -> Vec<Parameter> {
    let mut params: Vec<_> = (0..proto.num_params)
        .map(|reg| Parameter::Regular(local_ident(reg)))
        .collect();
    if proto.is_vararg {
        params.push(Parameter::Vararg);
    }
    params
}

fn visible_stmt_count(block: &CfgBlock) -> usize {
    block
        .stmts
        .len()
        .saturating_sub(synthetic_preheader_stmt_count(block))
}

fn synthetic_preheader_stmt_count(block: &CfgBlock) -> usize {
    match &block.exit {
        BlockExit::ForNPrep { base, .. } => {
            usize::from(numeric_for_preheader(block, *base).is_some()) * 3
        }
        BlockExit::ForGPrep { base, .. } => {
            generic_for_preheader(block, *base).map_or(0, |preheader| preheader.consumed_stmt_count)
        }
        _ => 0,
    }
}

fn numeric_for_preheader(block: &CfgBlock, base: usize) -> Option<(&HilExpr, &HilExpr, &HilExpr)> {
    let mut start = None;
    let mut end = None;
    let mut step = None;

    for stmt_idx in block.stmts.len().saturating_sub(3)..block.stmts.len() {
        let HilStmt::Assign {
            left: HilExpr::Local(reg),
            value,
        } = &block.stmts.get(stmt_idx)?.inner
        else {
            return None;
        };

        match *reg as usize {
            r if r == base => end = Some(value),
            r if r == base + 1 => step = Some(value),
            r if r == base + 2 => start = Some(value),
            _ => return None,
        }
    }

    Some((start?, end?, step?))
}

fn generic_for_preheader(block: &CfgBlock, base: usize) -> Option<GenericForPreheader<'_>> {
    if let Some(last) = block.stmts.last()
        && let HilStmt::AssignMany { left, value } = &last.inner
        && let Some(HilExpr::Local(reg)) = left.first()
        && *reg as usize == base
    {
        return Some(GenericForPreheader {
            exprs: vec![value],
            consumed_stmt_count: 1,
        });
    }

    let mut generator = None;
    let mut state = None;
    let mut control = None;

    for stmt_idx in block.stmts.len().saturating_sub(3)..block.stmts.len() {
        let HilStmt::Assign {
            left: HilExpr::Local(reg),
            value,
        } = &block.stmts.get(stmt_idx)?.inner
        else {
            return None;
        };

        match *reg as usize {
            r if r == base => generator = Some(value),
            r if r == base + 1 => state = Some(value),
            r if r == base + 2 => control = Some(value),
            _ => return None,
        }
    }

    let generator = generator?;
    let state = state?;
    let control = control?;
    let exprs = if matches!(state, HilExpr::Nil) && matches!(control, HilExpr::Nil) {
        vec![generator]
    } else {
        vec![generator, state, control]
    };

    Some(GenericForPreheader {
        exprs,
        consumed_stmt_count: 3,
    })
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
        structurer::{generic_for_preheader, structure},
    };

    #[test]
    fn structure_lowers_straight_line_region() {
        let cfg = ControlFlowGraph::new(
            vec![CfgBlock::new(
                0,
                vec![Spanned::new(
                    HilStmt::Assign {
                        left: HilExpr::Local(0),
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
                        cond: HilExpr::Local(0),
                        then_block: 1,
                        else_block: 2,
                    },
                ),
                CfgBlock::new(
                    1,
                    vec![Spanned::new(
                        HilStmt::Assign {
                            left: HilExpr::Local(1),
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
                            left: HilExpr::Local(2),
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
                    condition: HilExpr::Local(0),
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
    fn generic_for_preheader_accepts_assign_many_source() {
        let block = CfgBlock::new(
            0,
            vec![Spanned::new(
                HilStmt::AssignMany {
                    left: vec![HilExpr::Local(2), HilExpr::Local(3), HilExpr::Local(4)],
                    value: HilExpr::Global("pairs".to_string()),
                },
                0,
            )],
            BlockExit::ForGPrep {
                base: 2,
                loop_block: 1,
            },
        );

        let preheader = generic_for_preheader(&block, 2).expect("expected generic-for preheader");

        assert_eq!(preheader.exprs.len(), 1);
        assert_eq!(preheader.consumed_stmt_count, 1);
        assert!(matches!(
            preheader.exprs.as_slice(),
            [HilExpr::Global(name)] if name == "pairs"
        ));
    }

    #[test]
    fn structure_lowers_generic_for_and_skips_synthetic_preheader_assignments() {
        let cfg = ControlFlowGraph::new(
            vec![
                CfgBlock::new(
                    0,
                    vec![
                        Spanned::new(
                            HilStmt::Assign {
                                left: HilExpr::Local(0),
                                value: HilExpr::Table { items: Vec::new() },
                            },
                            0,
                        ),
                        Spanned::new(
                            HilStmt::Assign {
                                left: HilExpr::Local(1),
                                value: HilExpr::Local(0),
                            },
                            1,
                        ),
                        Spanned::new(
                            HilStmt::Assign {
                                left: HilExpr::Local(2),
                                value: HilExpr::Nil,
                            },
                            2,
                        ),
                        Spanned::new(
                            HilStmt::Assign {
                                left: HilExpr::Local(3),
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

        assert_eq!(ast.stmts.len(), 3);
        assert!(matches!(
            &ast.stmts[0],
            AstStmt::LocalDeclaration { names, .. }
                if matches!(names.as_slice(), [name] if name.as_str() == "r0")
        ));
        assert!(matches!(
            &ast.stmts[1],
            AstStmt::GenericFor { vars, exprs, .. }
                if vars.len() == 2
                    && vars[0].as_str() == "r4"
                    && vars[1].as_str() == "r5"
                    && matches!(exprs.as_slice(), [AstExpr::Name(name)] if name.as_str() == "r0")
        ));
        assert!(matches!(&ast.stmts[2], AstStmt::Return { values } if values.is_empty()));
    }
}
