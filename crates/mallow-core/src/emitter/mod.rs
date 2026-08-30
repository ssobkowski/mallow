mod name;
mod plan;
mod storage;

use std::collections::HashMap;

use anyhow::{Result, bail, ensure};
use name::{Namer, PlainNamer};
use plan::{BindingKey, FunctionPlan};
use smol_str::SmolStr;
use storage::Storage;

use crate::ast::Identifier;
use crate::common::is_valid_luau_identifier;
use crate::il::ProtoId;
use crate::ir::fir::{CellId, Constant, Number};
use crate::ir::nir;
use crate::operator::{BinOp, CompoundBinOp};
use crate::{DecompileOptions, ast};

/// Emits a materialized NIR program with the default naming policy.
pub(crate) fn emit_ast(
    functions: Vec<nir::Function>,
    entry: ProtoId,
    options: DecompileOptions,
) -> Result<ast::Block> {
    emit_ast_with_namer(functions, entry, options, PlainNamer::default())
}

/// Emits a materialized NIR program with a caller-provided naming policy.
pub(crate) fn emit_ast_with_namer<N: Namer>(
    functions: Vec<nir::Function>,
    entry: ProtoId,
    options: DecompileOptions,
    mut namer: N,
) -> Result<ast::Block> {
    let EmittedFunction { body, .. } =
        emit_function(&functions, options, &mut namer, entry, HashMap::new())?;
    Ok(body)
}

/// Emits one function under the storage aliases supplied by its closure.
fn emit_function<N: Namer>(
    functions: &[nir::Function],
    options: DecompileOptions,
    namer: &mut N,
    id: ProtoId,
    inherited_cells: HashMap<CellId, Storage>,
) -> Result<EmittedFunction> {
    let function = &functions[id.0 as usize];
    let plan = FunctionPlan::build(function, &inherited_cells, options.spill_locals, namer)?;
    FunctionEmitter::new(functions, options, namer, function, plan).emit()
}

/// AST parts produced for one function prototype.
struct EmittedFunction {
    params: Vec<ast::Typed<ast::Parameter>>,
    body: ast::Block,
}

/// Describes how Luau syntax adjusts one emitted expression.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ExprContext {
    /// The surrounding syntax already keeps only one value.
    Scalar,
    /// The expression ends a list where calls and varargs can expand.
    OpenTail,
}

/// Lowers one fully planned NIR function into AST nodes.
struct FunctionEmitter<'f, 'n, N: Namer> {
    functions: &'f [nir::Function],
    options: DecompileOptions,
    namer: &'n mut N,
    function: &'f nir::Function,
    plan: FunctionPlan,
    /// Placeholder claimed once for every discard slot in this function.
    discard: Option<ast::Identifier>,
    next_scope: usize,
}

impl<'f, 'n, N: Namer> FunctionEmitter<'f, 'n, N> {
    /// Creates one mechanical function lowerer.
    fn new(
        functions: &'f [nir::Function],
        options: DecompileOptions,
        namer: &'n mut N,
        function: &'f nir::Function,
        plan: FunctionPlan,
    ) -> Self {
        Self {
            functions,
            options,
            namer,
            function,
            plan,
            discard: None,
            next_scope: 1,
        }
    }

    /// Emits parameters, prologue statements, and structured body.
    fn emit(mut self) -> Result<EmittedFunction> {
        let params = self
            .function
            .params
            .iter()
            .map(|local| {
                let name = self
                    .plan
                    .local(*local)?
                    .name()
                    .cloned()
                    .ok_or_else(|| anyhow::anyhow!("function parameter was spilled"))?;
                Ok(ast::Typed::untyped(ast::Parameter::Regular(name)))
            })
            .collect::<Result<Vec<_>>>()?;
        let mut params = params;
        if self.function.is_vararg {
            params.push(ast::Typed::untyped(ast::Parameter::Vararg));
        }

        let mut stmts = self.scope_prefix(0)?;
        self.lower_stmts(&self.function.prologue, 0, &mut stmts)?;
        self.lower_region(&self.function.body, 0, &mut stmts)?;

        Ok(EmittedFunction {
            params,
            body: ast::Block::with_stmts(stmts),
        })
    }

    /// Emits the spill table required at one scope entry.
    fn scope_prefix(&self, scope: usize) -> Result<Vec<ast::Stmt>> {
        let scope = self.plan.scope(scope)?;
        let mut stmts = Vec::new();
        if !scope.prefix_names.is_empty() {
            stmts.push(ast::Stmt::LocalDeclaration {
                names: scope
                    .prefix_names
                    .iter()
                    .cloned()
                    .map(ast::Typed::untyped)
                    .collect(),
                values: Vec::new(),
            });
        }
        if let Some(table) = &scope.spill_table {
            stmts.push(ast::Stmt::LocalDeclaration {
                names: vec![ast::Typed::untyped(table.clone())],
                values: vec![ast::Expr::Table { items: Vec::new() }],
            });
        }
        Ok(stmts)
    }

    /// Returns the shared placeholder identifier for discard slots.
    ///
    /// Claimed once per function so user variables named `_` are never shadowed.
    fn discard_name(&mut self) -> ast::Identifier {
        if let Some(name) = &self.discard {
            return name.clone();
        }
        let name = self.plan.names.claim(ast::Identifier::new("_"));
        self.discard = Some(name.clone());
        name
    }

    /// Allocates the next child scope in structural traversal order.
    fn child_scope(&mut self) -> usize {
        let scope = self.next_scope;
        self.next_scope += 1;
        scope
    }

    /// Lowers one child region inside a fresh lexical scope.
    fn lower_child_scope(&mut self, region: &nir::Region) -> Result<ast::Block> {
        let scope = self.child_scope();
        let mut stmts = self.scope_prefix(scope)?;
        self.lower_region(region, scope, &mut stmts)?;
        Ok(ast::Block::with_stmts(stmts))
    }

    /// Lowers one structured region into the current AST statement buffer.
    fn lower_region(
        &mut self,
        region: &nir::Region,
        scope: usize,
        out: &mut Vec<ast::Stmt>,
    ) -> Result<()> {
        match region {
            nir::Region::Block { stmts, .. } => self.lower_stmts(stmts, scope, out)?,
            nir::Region::Sequence(nodes) => {
                for node in nodes {
                    self.lower_region(node, scope, out)?;
                }
            }
            nir::Region::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.lower_expr(condition)?;
                let then_body = self.lower_child_scope(then_branch)?;
                let else_clause = if let Some(else_branch) = else_branch {
                    let mut body = self.lower_child_scope(else_branch)?;
                    Some(match body.stmts.as_slice() {
                        [ast::Stmt::If(_)] => {
                            let Some(ast::Stmt::If(nested)) = body.stmts.pop() else {
                                unreachable!()
                            };
                            ast::ElseClause::If(Box::new(nested))
                        }
                        _ => ast::ElseClause::Else(body),
                    })
                } else {
                    None
                };
                out.push(ast::Stmt::If(ast::If {
                    condition,
                    then_body,
                    else_clause,
                }));
            }
            nir::Region::While { condition, body } => {
                let condition = self.lower_expr(condition)?;
                let body = self.lower_child_scope(body)?;
                out.push(ast::Stmt::While { condition, body });
            }
            nir::Region::RepeatUntil { condition, body } => {
                let body = self.lower_child_scope(body)?;
                let condition = self.lower_expr(condition)?;
                out.push(ast::Stmt::RepeatUntil { condition, body });
            }
            nir::Region::NumericFor {
                variable,
                start,
                end,
                step,
                body,
            } => {
                let var = self
                    .plan
                    .local(*variable)?
                    .name()
                    .cloned()
                    .ok_or_else(|| anyhow::anyhow!("numeric-for variable was spilled"))?;
                let start = self.lower_expr(start)?;
                let end = self.lower_expr(end)?;
                let step = Some(self.lower_expr(step)?);
                let body = self.lower_child_scope(body)?;
                out.push(ast::Stmt::NumericFor {
                    var,
                    start,
                    end,
                    step,
                    body,
                });
            }
            nir::Region::GenericFor {
                variables,
                values,
                body,
            } => {
                let vars = variables
                    .iter()
                    .map(|variable| {
                        self.plan
                            .local(*variable)?
                            .name()
                            .cloned()
                            .ok_or_else(|| anyhow::anyhow!("generic-for variable was spilled"))
                    })
                    .collect::<Result<_>>()?;
                let exprs = values
                    .iter()
                    .enumerate()
                    .map(|(index, value)| {
                        let context = if index + 1 == values.len() {
                            ExprContext::OpenTail
                        } else {
                            ExprContext::Scalar
                        };
                        self.lower_expr_in(value, context)
                    })
                    .collect::<Result<_>>()?;
                let body = self.lower_child_scope(body)?;
                out.push(ast::Stmt::GenericFor { vars, exprs, body });
            }
            nir::Region::Continue => out.push(ast::Stmt::Continue),
            nir::Region::Break => out.push(ast::Stmt::Break),
            nir::Region::Return(values) => out.push(ast::Stmt::Return {
                values: self.lower_pack(values)?,
            }),
        }
        Ok(())
    }

    /// Lowers a flat statement list.
    fn lower_stmts(
        &mut self,
        stmts: &[nir::Stmt],
        scope: usize,
        out: &mut Vec<ast::Stmt>,
    ) -> Result<()> {
        for stmt in stmts {
            self.lower_stmt(stmt, scope, out)?;
        }
        Ok(())
    }

    /// Emits one pack-producing effect whose results are unused.
    fn eval_pack(&mut self, value: &nir::PackExpr, out: &mut Vec<ast::Stmt>) -> Result<()> {
        match value {
            nir::PackExpr::Call { .. } | nir::PackExpr::MethodCall { .. } => {
                let mut values = self.lower_pack(value)?;
                ensure!(values.len() == 1, "call pack must lower to one expression");
                out.push(ast::Stmt::Expression {
                    expr: values.pop().expect("the call produced one expression"),
                });
            }
            nir::PackExpr::Values { .. } => {
                let values = self.lower_pack(value)?;
                if !values.is_empty() {
                    out.push(ast::Stmt::Comment {
                        text: "the following code evaluates an unused value pack".to_string(),
                    });
                    out.push(ast::Stmt::Expression {
                        expr: ast::Expr::FunctionCall {
                            func: Box::new(field(global("table"), "pack")),
                            args: values,
                        },
                    });
                }
            }
            nir::PackExpr::Local(_) | nir::PackExpr::VarArgs => {}
        }
        Ok(())
    }

    /// Binds one multivalue result into one list of places.
    fn lower_bind_many(
        &mut self,
        targets: &[nir::Place],
        values: &nir::PackExpr,
        scope: usize,
        out: &mut Vec<ast::Stmt>,
    ) -> Result<()> {
        /// One prepared binding inside a multibind.
        enum Slot {
            /// Declares one new name in this statement's scope.
            Fresh(SmolStr),
            /// Reuses existing source storage.
            Existing(Storage),
            /// Writes one non-storage place.
            Place(ast::Expr),
        }

        let rhs = self.lower_pack(values)?;
        let slots: Vec<_> = targets
            .iter()
            .map(|target| {
                Ok(match target {
                    // A discard slot always joins the fresh declaration group.
                    nir::Place::Discard => Slot::Fresh(self.discard_name().0),
                    nir::Place::Local(local) => {
                        if self
                            .plan
                            .claim_declaration(BindingKey::Local(*local), scope)
                            && let Some(name) = self.plan.local(*local)?.name().cloned()
                        {
                            Slot::Fresh(name.0)
                        } else {
                            Slot::Existing(self.plan.local(*local)?.clone())
                        }
                    }
                    nir::Place::Cell(cell) => {
                        if self.plan.claim_declaration(BindingKey::Cell(*cell), scope)
                            && let Some(name) = self.plan.cell(*cell)?.name().cloned()
                        {
                            Slot::Fresh(name.0)
                        } else {
                            Slot::Existing(self.plan.cell(*cell)?.clone())
                        }
                    }
                    nir::Place::Global(_) | nir::Place::Table { .. } => {
                        Slot::Place(self.lower_place(target)?)
                    }
                })
            })
            .collect::<Result<_>>()?;

        if slots.iter().all(|slot| matches!(slot, Slot::Fresh(_))) {
            let names = slots
                .into_iter()
                .map(|slot| match slot {
                    Slot::Fresh(name) => ast::Typed::untyped(Identifier(name)),
                    Slot::Existing(_) | Slot::Place(_) => unreachable!("all slots are fresh"),
                })
                .collect();
            out.push(ast::Stmt::LocalDeclaration { names, values: rhs });
            return Ok(());
        }

        let fresh: Vec<_> = slots
            .iter()
            .filter_map(|slot| match slot {
                Slot::Fresh(name) => Some(ast::Typed::untyped(Identifier(name.clone()))),
                Slot::Existing(_) | Slot::Place(_) => None,
            })
            .collect();
        if !fresh.is_empty() {
            out.push(ast::Stmt::LocalDeclaration {
                names: fresh,
                values: Vec::new(),
            });
        }
        let lhs = slots
            .into_iter()
            .map(|slot| match slot {
                Slot::Fresh(name) => ast::Expr::Named(Identifier(name)),
                Slot::Existing(storage) => storage.expr(),
                Slot::Place(place) => place,
            })
            .collect();
        out.push(ast::Stmt::Assignment { lhs, rhs });
        Ok(())
    }

    /// Lowers one NIR statement.
    fn lower_stmt(
        &mut self,
        stmt: &nir::Stmt,
        scope: usize,
        out: &mut Vec<ast::Stmt>,
    ) -> Result<()> {
        match stmt {
            nir::Stmt::Bind { target, value, .. } => match target {
                nir::Place::Local(local) => {
                    let declaration = self
                        .plan
                        .claim_declaration(BindingKey::Local(*local), scope);
                    if !declaration && let Some((op, rhs)) = compound_binding(target, value) {
                        out.push(ast::Stmt::CompoundAssignment {
                            lhs: self.plan.local(*local)?.expr(),
                            op,
                            rhs: self.lower_expr(rhs)?,
                        });
                    } else {
                        let value = self.lower_expr(value)?;
                        self.bind_storage(self.plan.local(*local)?, value, declaration, out);
                    }
                }
                nir::Place::Cell(cell) => {
                    let declaration = self.plan.claim_declaration(BindingKey::Cell(*cell), scope);
                    if !declaration && let Some((op, rhs)) = compound_binding(target, value) {
                        out.push(ast::Stmt::CompoundAssignment {
                            lhs: self.plan.cell(*cell)?.expr(),
                            op,
                            rhs: self.lower_expr(rhs)?,
                        });
                    } else {
                        let value = self.lower_expr(value)?;
                        self.bind_storage(self.plan.cell(*cell)?, value, declaration, out);
                    }
                }
                nir::Place::Global(_) | nir::Place::Table { .. } => {
                    let target = self.lower_place(target)?;
                    let value = self.lower_expr(value)?;
                    out.push(ast::Stmt::Assignment {
                        lhs: vec![target],
                        rhs: vec![value],
                    });
                }
                nir::Place::Discard => {
                    unreachable!("single binds never target a discard; only multibindings do")
                }
            },
            nir::Stmt::BindMany { targets, values } => {
                self.lower_bind_many(targets, values, scope, out)?;
            }
            nir::Stmt::BindPack { local, value } => {
                let packed = ast::Expr::FunctionCall {
                    func: Box::new(field(global("table"), "pack")),
                    args: self.lower_pack(value)?,
                };
                out.push(ast::Stmt::Comment {
                    text: "the following code preserves a value pack that cannot be represented"
                        .to_string(),
                });
                let declaration = self.plan.claim_declaration(BindingKey::Pack(*local), scope);
                self.bind_storage(self.plan.pack(*local)?, packed, declaration, out);
            }
            nir::Stmt::Eval { value } => self.eval_pack(value, out)?,
            nir::Stmt::OpenCell { cell, value, .. } => {
                let backing_local =
                    self.function.cell_locals.get(cell).ok_or_else(|| {
                        anyhow::anyhow!("opened cell has no backing source local")
                    })?;
                ensure!(
                    matches!(value, nir::Expr::Local(local) if local == backing_local),
                    "opened cell does not reference its backing source local"
                );
            }
            nir::Stmt::SetList {
                table,
                index,
                values,
                ..
            } => self.lower_set_list(table, *index, values, out)?,
        }
        Ok(())
    }

    /// Emits a first binding as a declaration or assignment.
    fn bind_storage(
        &self,
        storage: &Storage,
        value: ast::Expr,
        declaration: bool,
        out: &mut Vec<ast::Stmt>,
    ) {
        if declaration && let Some(name) = storage.name() {
            out.push(ast::Stmt::LocalDeclaration {
                names: vec![ast::Typed::untyped(name.clone())],
                values: vec![value],
            });
        } else {
            out.push(ast::Stmt::Assignment {
                lhs: vec![storage.expr()],
                rhs: vec![value],
            });
        }
    }

    /// Lowers a table list write while preserving open-pack length.
    fn lower_set_list(
        &mut self,
        table: &nir::Expr,
        index: u32,
        values: &nir::PackExpr,
        out: &mut Vec<ast::Stmt>,
    ) -> Result<()> {
        let table = self.lower_expr(table)?;
        if let Some(length) = values.fixed_len() {
            let lhs = (0..length)
                .map(|offset| ast::Expr::Index {
                    base: Box::new(table.clone()),
                    index: Box::new(ast::Expr::Literal(ast::Literal::Float(
                        f64::from(index) + offset as f64,
                    ))),
                })
                .collect();
            out.push(ast::Stmt::Assignment {
                lhs,
                rhs: self.lower_pack(values)?,
            });
            return Ok(());
        }

        if let nir::PackExpr::Local(local) = values {
            out.push(ast::Stmt::Expression {
                expr: move_packed_values(self.plan.pack(*local)?.expr(), table, index),
            });
            return Ok(());
        }

        let temp = self.plan.names.internal("pack");
        let packed = ast::Expr::FunctionCall {
            func: Box::new(field(global("table"), "pack")),
            args: self.lower_pack(values)?,
        };
        out.push(ast::Stmt::Comment {
            text: "the following code preserves an open table value list".to_string(),
        });
        out.push(ast::Stmt::Do {
            body: ast::Block::with_stmts(vec![
                ast::Stmt::LocalDeclaration {
                    names: vec![ast::Typed::untyped(temp.clone())],
                    values: vec![packed],
                },
                ast::Stmt::Expression {
                    expr: move_packed_values(ast::Expr::Named(temp), table, index),
                },
            ]),
        });
        Ok(())
    }

    /// Lowers one writable NIR place.
    fn lower_place(&mut self, place: &nir::Place) -> Result<ast::Expr> {
        Ok(match place {
            nir::Place::Local(local) => self.plan.local(*local)?.expr(),
            nir::Place::Cell(cell) => self.plan.cell(*cell)?.expr(),
            nir::Place::Global(name) => global_name(name),
            nir::Place::Discard => unreachable!("discard places are never read"),
            nir::Place::Table { table, key } => {
                table_access(self.lower_expr(table)?, key, self.lower_expr(key)?)
            }
        })
    }

    /// Lowers one expression in a context which keeps only one value.
    fn lower_expr(&mut self, expr: &nir::Expr) -> Result<ast::Expr> {
        self.lower_expr_in(expr, ExprContext::Scalar)
    }

    /// Lowers one scalar expression for its surrounding Luau syntax.
    fn lower_expr_in(&mut self, expr: &nir::Expr, context: ExprContext) -> Result<ast::Expr> {
        Ok(match expr {
            nir::Expr::Local(local) => self.plan.local(*local)?.expr(),
            nir::Expr::Constant(value) => constant(value),
            nir::Expr::Closure { proto, captures } => self.lower_closure(*proto, captures)?,
            nir::Expr::GetTable { table, key } => {
                table_access(self.lower_expr(table)?, key, self.lower_expr(key)?)
            }
            nir::Expr::GetGlobal(name) => global_name(name),
            nir::Expr::Binary { lhs, op, rhs } => ast::Expr::Binary {
                lhs: Box::new(self.lower_expr(lhs)?),
                op: *op,
                rhs: Box::new(self.lower_expr(rhs)?),
            },
            nir::Expr::Unary { op, value } => ast::Expr::Unary {
                op: *op,
                expr: Box::new(self.lower_expr(value)?),
            },
            nir::Expr::Concat(values) => {
                let mut values = values.iter().rev();
                let Some(last) = values.next() else {
                    bail!("NIR concat cannot be empty")
                };
                let mut combined = self.lower_expr(last)?;
                for value in values {
                    combined = ast::Expr::Binary {
                        lhs: Box::new(self.lower_expr(value)?),
                        op: BinOp::Concat,
                        rhs: Box::new(combined),
                    };
                }
                combined
            }
            nir::Expr::Select {
                condition,
                then_value,
                else_value,
            } => ast::Expr::IfElse {
                condition: Box::new(self.lower_expr(condition)?),
                then_expr: Box::new(self.lower_expr(then_value)?),
                else_expr: Box::new(self.lower_expr(else_value)?),
            },
            nir::Expr::Table { items } => {
                let mut lowered = Vec::new();
                for item in items {
                    lowered.extend(self.lower_table_item(item)?);
                }
                ast::Expr::Table { items: lowered }
            }
            nir::Expr::Project { pack, index } => self.lower_project(pack, *index, context)?,
            nir::Expr::LoadCell(cell) => self.plan.cell(*cell)?.expr(),
        })
    }

    /// Lowers one closure and maps positional captures to child upvalue cells.
    fn lower_closure(&mut self, proto: ProtoId, captures: &[nir::Capture]) -> Result<ast::Expr> {
        let child_upvalues = &self.functions[proto.0 as usize].upvalues;
        ensure!(
            child_upvalues.len() == captures.len(),
            "closure capture count does not match child upvalues"
        );

        let mut inherited = HashMap::new();
        for (&cell, capture) in child_upvalues.iter().zip(captures) {
            let storage = match capture {
                nir::Capture::Share(parent_cell) => self.plan.cell(*parent_cell)?.clone(),
                nir::Capture::Copy(local) => self.plan.local(*local)?.clone(),
            };
            inherited.insert(cell, storage);
        }

        let child = emit_function(
            self.functions,
            self.options,
            &mut *self.namer,
            proto,
            inherited,
        )?;
        Ok(ast::Expr::AnonymousFunction {
            params: child.params,
            body: child.body,
        })
    }

    /// Lowers one scalar projection from a value pack.
    fn lower_project(
        &mut self,
        pack: &nir::PackExpr,
        index: usize,
        context: ExprContext,
    ) -> Result<ast::Expr> {
        if let nir::PackExpr::Local(local) = pack {
            return Ok(ast::Expr::Index {
                base: Box::new(self.plan.pack(*local)?.expr()),
                index: Box::new(ast::Expr::Literal(ast::Literal::Float((index + 1) as f64))),
            });
        }

        let mut values = self.lower_pack(pack)?;
        if index == 0 && values.len() == 1 {
            let value = values.pop().unwrap();
            return if context == ExprContext::OpenTail {
                Ok(ast::Expr::Parenthesized(Box::new(value)))
            } else {
                Ok(value)
            };
        }
        let mut args = Vec::with_capacity(values.len() + 1);
        args.push(ast::Expr::Literal(ast::Literal::Float((index + 1) as f64)));
        args.extend(values);
        Ok(ast::Expr::FunctionCall {
            func: Box::new(global("select")),
            args,
        })
    }

    /// Lowers one NIR pack into a Luau expression list.
    fn lower_pack(&mut self, pack: &nir::PackExpr) -> Result<Vec<ast::Expr>> {
        Ok(match pack {
            nir::PackExpr::Local(local) => {
                let packed = self.plan.pack(*local)?.expr();
                vec![ast::Expr::FunctionCall {
                    func: Box::new(field(global("table"), "unpack")),
                    args: vec![
                        packed.clone(),
                        ast::Expr::Literal(ast::Literal::Float(1.0)),
                        field(packed, "n"),
                    ],
                }]
            }
            nir::PackExpr::Values { head, tail } => {
                let mut values = Vec::with_capacity(head.len());
                for (index, value) in head.iter().enumerate() {
                    let context = if tail.is_none() && index + 1 == head.len() {
                        ExprContext::OpenTail
                    } else {
                        ExprContext::Scalar
                    };
                    values.push(self.lower_expr_in(value, context)?);
                }
                if let Some(tail) = tail {
                    values.extend(self.lower_pack(tail)?);
                }
                values
            }
            nir::PackExpr::Call { function, args } => vec![ast::Expr::FunctionCall {
                func: Box::new(self.lower_expr(function)?),
                args: self.lower_pack(args)?,
            }],
            nir::PackExpr::MethodCall {
                object,
                method,
                args,
            } => vec![ast::Expr::MethodCall {
                object: Box::new(self.lower_expr(object)?),
                method: ast::Identifier::new(method.clone()),
                args: self.lower_pack(args)?,
            }],
            nir::PackExpr::VarArgs => vec![ast::Expr::Vararg],
        })
    }

    /// Lowers one table item into a vector of AST table items.
    fn lower_table_item(&mut self, item: &nir::TableItem) -> Result<Vec<ast::TableItem>> {
        Ok(match item {
            nir::TableItem::List(pack) => self
                .lower_pack(pack)?
                .into_iter()
                .map(|value| ast::TableItem::Implicit { value })
                .collect(),
            nir::TableItem::Index(key, value) => {
                let value = self.lower_expr(value)?;
                // TODO: `is_valid_luau_identifier` needs to support ByteString (or have a separate method for it.)
                // if let nir::Expr::Constant(fir::Constant::String(s)) = key
                //     && is_valid_luau_identifier(s)
                // {
                //     TableItem::Named {
                //         name: Identifier::new(s.clone()),
                //         value,
                //     }
                // } else {
                //     TableItem::Indexed {
                //         index: self.visit_expr(key),
                //         value,
                //     }
                // }
                vec![ast::TableItem::Indexed {
                    index: self.lower_expr(key)?,
                    value,
                }]
            }
        })
    }
}

/// Returns the compound form of one local or cell binding when it exists.
fn compound_binding<'a>(
    target: &nir::Place,
    value: &'a nir::Expr,
) -> Option<(CompoundBinOp, &'a nir::Expr)> {
    let nir::Expr::Binary { lhs, op, rhs } = value else {
        return None;
    };
    let reads_target = match (target, lhs.as_ref()) {
        (nir::Place::Local(target), nir::Expr::Local(source)) => target == source,
        (nir::Place::Cell(target), nir::Expr::LoadCell(source)) => target == source,
        _ => false,
    };
    if !reads_target {
        return None;
    }
    let op = CompoundBinOp::try_from(*op).ok()?;
    Some((op, rhs.as_ref()))
}

/// Converts one NIR constant into an AST literal.
fn constant(value: &Constant) -> ast::Expr {
    ast::Expr::Literal(match value {
        Constant::Nil => ast::Literal::Nil,
        Constant::Number(Number::Integer(value)) => ast::Literal::Integer(*value),
        Constant::Number(Number::Float(value)) => ast::Literal::Float(*value),
        Constant::String(value) => ast::Literal::String(value.clone()),
        Constant::Bool(value) => ast::Literal::Bool(*value),
    })
}

/// Builds a global read, including names that cannot use identifier syntax.
fn global_name(name: &SmolStr) -> ast::Expr {
    if is_valid_luau_identifier(name) {
        global(name.as_str())
    } else {
        ast::Expr::Index {
            base: Box::new(global("_G")),
            index: Box::new(ast::Expr::Literal(ast::Literal::String(
                name.clone().into(),
            ))),
        }
    }
}

/// Builds a plain global identifier expression.
fn global(name: impl Into<SmolStr>) -> ast::Expr {
    ast::Expr::Named(ast::Identifier::new(name))
}

/// Chooses field syntax when a constant string key permits it.
fn table_access(base: ast::Expr, key: &nir::Expr, lowered_key: ast::Expr) -> ast::Expr {
    if let nir::Expr::Constant(Constant::String(value)) = key
        && let Some(field_name) = value.as_utf8()
        && is_valid_luau_identifier(field_name)
    {
        field(base, field_name)
    } else {
        ast::Expr::Index {
            base: Box::new(base),
            index: Box::new(lowered_key),
        }
    }
}

/// Builds one AST field access.
fn field(base: ast::Expr, name: impl Into<SmolStr>) -> ast::Expr {
    ast::Expr::Field {
        base: Box::new(base),
        field: ast::Identifier::new(name),
    }
}

/// Builds the table.move call used for one counted packed value list.
fn move_packed_values(packed: ast::Expr, table: ast::Expr, index: u32) -> ast::Expr {
    ast::Expr::FunctionCall {
        func: Box::new(field(global("table"), "move")),
        args: vec![
            packed.clone(),
            ast::Expr::Literal(ast::Literal::Float(1.0)),
            field(packed, "n"),
            ast::Expr::Literal(ast::Literal::Float(f64::from(index))),
            table,
        ],
    }
}
