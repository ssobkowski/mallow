//! FIR Shape to NIR Region materialization and inlining.

use std::collections::{HashMap, HashSet};

use anyhow::{bail, ensure, Result};
use id_arena::Arena;

use crate::hil::cflow::graph::{build_graph, AdjGraph, DominatorTree, GraphView};
use crate::hil::cflow::union_find::UnionFind;

use super::inline::inline_control_values;
use super::*;
use crate::ir;
use crate::ir::region::{Predicate, Shape};
use crate::logging::Diagnostics;

/// Recognizes and materializes one FIR function as nested NIR.
pub(crate) fn lower(function: &ir::Function, diagnostics: &Diagnostics) -> Result<Function> {
    let shape = ir::region::structure(function, diagnostics)?;
    materialize(function, shape)
}

/// Converts one verified control shape into materialized NIR.
pub(crate) fn materialize(function: &ir::Function, shape: Shape) -> Result<Function> {
    #[cfg(debug_assertions)]
    {
        function.verify()?;
        shape.verify(function)?;
    }

    let ssa = SsaMeta::build(function)?;
    let initializations = Initializations::build(&ssa, &shape, function.blocks.len());
    Materializer::new(function, &ssa, initializations).materialize(shape)
}

/// Describes SSA destruction for one FIR function.
struct SsaMeta {
    /// Canonical storage for every FIR value.
    storage: HashMap<ValueId, ValueId>,
    /// Storages that receive writes after their first definition.
    mutable: HashSet<ValueId>,
    /// A list of synthetic nil declarations grouped by dominating block.
    declarations: Vec<Vec<ValueId>>,
}

impl SsaMeta {
    /// Unfolds Phi inputs and coalesces their values into mutable storage.
    fn build(function: &ir::Function) -> Result<Self> {
        let (successors, predecessors) =
            build_graph(function.blocks.iter().map(|block| block.exit.targets()));
        let graph = AdjGraph::new(0, &successors, &predecessors);
        let idoms = graph.build_idoms();

        let mut groups = UnionFind::new();
        let mut phi_blocks = Vec::new();
        let mut loop_values = Vec::new();

        for block_index in graph.post_order() {
            let block = &function.blocks[block_index];
            for instr in &block.instrs {
                let ir::Instr::Phi { out, inputs } = instr else {
                    continue;
                };

                phi_blocks.push((*out, block_index));
                for &(predecessor, input) in inputs {
                    // TODO: Is this necessary?
                    let is_loop_header_initializer = match &function.blocks[predecessor].exit {
                        ir::BlockExit::NumericFor {
                            body_block,
                            variable,
                            ..
                        } => *body_block == block_index && variable == out,
                        ir::BlockExit::GenericFor {
                            body_block,
                            variables,
                            ..
                        } => *body_block == block_index && variables.contains(&out),
                        _ => false,
                    };

                    if !is_loop_header_initializer {
                        groups.union(*out, input);
                    }
                }
            }

            match &block.exit {
                ir::BlockExit::NumericFor { variable, .. } => {
                    loop_values.push(*variable);
                }
                ir::BlockExit::GenericFor {
                    loop_block,
                    variables: init_variables,
                    ..
                } => {
                    loop_values.extend(init_variables.iter().copied());
                    let Some(ir::BlockExit::GenericForLoop {
                        variables: body_variables,
                        ..
                    }) = function.blocks.get(*loop_block).map(|b| &b.exit)
                    else {
                        bail!("generic-for target bb{loop_block} is not a generic loop block");
                    };

                    #[cfg(debug_assertions)]
                    ensure!(
                        init_variables.len() == body_variables.len(),
                        "generic-for loop variable counts do not match"
                    );

                    for (entry, body) in init_variables.iter().zip(body_variables) {
                        groups.union(*entry, *body);
                    }
                }
                ir::BlockExit::GenericForLoop { variables, .. } => {
                    loop_values.extend(variables.iter().copied());
                }
                _ => {}
            }
        }

        let storage: HashMap<_, _> = function
            .values
            .iter()
            .map(|(value, _)| (value, groups.find(value)))
            .collect();
        let mutable: HashSet<_> = phi_blocks
            .iter()
            .map(|(out, _)| out)
            .chain(loop_values.iter())
            .map(|value| storage[value])
            .collect();
        let initialized: HashSet<_> = function
            .params
            .iter()
            .chain(loop_values.iter())
            .map(|value| storage[value])
            .collect();

        let mut storage_blocks = HashMap::<ValueId, Vec<usize>>::new();
        for (out, block) in phi_blocks {
            storage_blocks.entry(storage[&out]).or_default().push(block);
        }

        let mut declarations = vec![Vec::new(); graph.len()];
        for (storage_id, blocks) in storage_blocks {
            if initialized.contains(&storage_id) {
                continue;
            }
            let declaration = common_strict_dominator(graph.entry(), &idoms, &blocks);
            declarations[declaration].push(storage_id);
        }

        Ok(Self {
            storage,
            mutable,
            declarations,
        })
    }

    /// Returns the canonical storage for one FIR value.
    #[inline]
    fn storage(&self, value: ValueId) -> ValueId {
        self.storage[&value]
    }

    /// Returns whether one FIR value writes mutable storage.
    #[inline]
    fn is_mutable(&self, value: ValueId) -> bool {
        self.mutable.contains(&self.storage(value))
    }
}

/// Synthetic storage declarations placed in one structured function.
struct Initializations {
    /// Declarations attached to concrete block regions.
    by_block: Vec<Vec<ValueId>>,
    /// Declarations emitted before the function body.
    prologue: Vec<ValueId>,
}

impl Initializations {
    /// Places each storage at its block or in the function prologue.
    fn build(ssa: &SsaMeta, shape: &Shape, block_count: usize) -> Self {
        let mut initialization_blocks = HashSet::new();
        collect_initialization_blocks(shape, &mut initialization_blocks);

        let mut by_block = vec![Vec::new(); block_count];
        let mut prologue = Vec::new();
        for (block, storages) in ssa.declarations.iter().enumerate() {
            if initialization_blocks.contains(&block) {
                by_block[block].extend(storages.iter().copied());
            } else {
                prologue.extend(storages.iter().copied());
            }
        }

        Self { by_block, prologue }
    }
}

/// Returns a common strict dominator for several Phi blocks.
#[inline]
fn common_strict_dominator(entry: usize, idoms: &DominatorTree, blocks: &[usize]) -> usize {
    // Apparently, this could have been written better. I (probably) agree, but this implementation
    // does not cause any meaningful issues for now.

    let Some((first, rest)) = blocks.split_first() else {
        return entry;
    };

    // Graph entry is a dominator of all blocks.
    let mut candidate = idoms.idom(*first).unwrap_or(entry);
    for &block in rest {
        while !idoms.dominates(candidate, block) {
            candidate = idoms.idom(candidate).unwrap_or(entry);
        }
    }
    candidate
}

/// Collects FIR blocks that can receive synthetic declarations.
fn collect_initialization_blocks(shape: &Shape, blocks: &mut HashSet<usize>) {
    match shape {
        Shape::Block { block } => {
            blocks.insert(*block);
        }
        Shape::Sequence { nodes } => {
            for node in nodes {
                collect_initialization_blocks(node, blocks);
            }
        }
        Shape::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_initialization_blocks(then_branch, blocks);
            if let Some(else_branch) = else_branch {
                collect_initialization_blocks(else_branch, blocks);
            }
        }
        Shape::While { body, .. }
        | Shape::RepeatUntil { body, .. }
        | Shape::NumericFor { body, .. }
        | Shape::GenericFor { body, .. } => collect_initialization_blocks(body, blocks),
        Shape::Continue | Shape::Break | Shape::Return { .. } => {}
    }
}

/// State used while converting FIR references into NIR identities.
struct Materializer<'f> {
    /// FIR function being converted.
    function: &'f ir::Function,
    /// SSA metadata used by all value references.
    ssa: &'f SsaMeta,
    /// NIR local arena.
    locals: Arena<Local>,
    /// NIR pack arena.
    packs: Arena<PackLocal>,
    /// FIR value to NIR local mapping.
    values: HashMap<ValueId, LocalId>,
    /// FIR pack to NIR pack mapping.
    pack_values: HashMap<PackId, PackLocalId>,
    /// Synthetic storage declarations for the structured function.
    initializations: Initializations,
}

impl<'a> Materializer<'a> {
    /// Creates stable NIR identities for every FIR storage and pack.
    fn new(function: &'a ir::Function, ssa: &'a SsaMeta, initializations: Initializations) -> Self {
        let mut locals = Arena::new();
        let mut storage_locals = HashMap::new();
        let mut values = HashMap::new();
        for (source, _) in function.values.iter() {
            let storage = ssa.storage(source);
            let local = *storage_locals
                .entry(storage)
                .or_insert_with(|| locals.alloc(Local { source: storage }));
            values.insert(source, local);
        }

        let mut packs = Arena::new();
        let pack_values = function
            .packs
            .iter()
            .map(|(source, _)| (source, packs.alloc(PackLocal { source })))
            .collect();

        Self {
            function,
            ssa,
            locals,
            packs,
            values,
            pack_values,
            initializations,
        }
    }

    /// Materializes the complete shape and verifies instruction ownership.
    fn materialize(self, shape: Shape) -> Result<Function> {
        let params = self
            .function
            .params
            .iter()
            .map(|value| self.local(*value))
            .collect::<Result<_>>()?;
        let prologue = self
            .initializations
            .prologue
            .iter()
            .map(|storage| self.initialization(*storage))
            .collect::<Result<_>>()?;
        let body = self.region(shape)?;
        let mut function = Function {
            locals: self.locals,
            packs: self.packs,
            params,
            prologue,
            body,
        };
        inline_control_values(&mut function.body);

        #[cfg(debug_assertions)]
        function.verify(self.function)?;

        Ok(function)
    }

    /// Creates one synthetic nil declaration for a mutable storage.
    #[inline]
    fn initialization(&self, storage: ValueId) -> Result<Stmt> {
        Ok(Stmt::Let {
            local: self.local(storage)?,
            value: Expr::nil(),
        })
    }

    /// Returns the stable local for one FIR value.
    #[inline]
    fn local(&self, value: ValueId) -> Result<LocalId> {
        self.values
            .get(&value)
            .copied()
            .ok_or_else(|| anyhow::anyhow!("missing NIR local for %v{}", value.index()))
    }

    /// Returns the stable local for one FIR pack.
    #[inline]
    fn pack(&self, pack: PackId) -> Result<PackLocalId> {
        self.pack_values
            .get(&pack)
            .copied()
            .ok_or_else(|| anyhow::anyhow!("missing NIR pack for %q{}", pack.index()))
    }

    /// Creates a local reference for one FIR value.
    #[inline]
    fn value(&self, value: ValueId) -> Result<Expr> {
        Ok(Expr::local(self.local(value)?))
    }

    /// Creates a local reference for one FIR pack.
    #[inline]
    fn pack_value(&self, pack: PackId) -> Result<PackExpr> {
        Ok(PackExpr::local(self.pack(pack)?))
    }

    /// Materializes one structured shape node.
    fn region(&self, shape: Shape) -> Result<Region> {
        Ok(match shape {
            Shape::Block { block } => Region::Block {
                origin: block,
                stmts: self.block(block)?,
            },
            Shape::Sequence { nodes } => Region::Sequence(
                nodes
                    .into_iter()
                    .map(|node| self.region(node))
                    .collect::<Result<_>>()?,
            ),
            Shape::If {
                condition,
                then_branch,
                else_branch,
            } => Region::If {
                condition: self.predicate(condition)?,
                then_branch: Box::new(self.region(*then_branch)?),
                else_branch: else_branch
                    .map(|branch| self.region(*branch).map(Box::new))
                    .transpose()?,
            },
            Shape::While { condition, body } => Region::While {
                condition: self.predicate(condition)?,
                body: Box::new(self.region(*body)?),
            },
            Shape::RepeatUntil { condition, body } => Region::RepeatUntil {
                condition: self.predicate(condition)?,
                body: Box::new(self.region(*body)?),
            },
            Shape::NumericFor {
                variable,
                start,
                end,
                step,
                body,
            } => Region::NumericFor {
                variable: self.local(variable)?,
                start: self.value(start)?,
                end: self.value(end)?,
                step: self.value(step)?,
                body: Box::new(self.region(*body)?),
            },
            Shape::GenericFor {
                variables,
                values,
                body,
            } => Region::GenericFor {
                variables: variables
                    .into_iter()
                    .map(|value| self.local(value))
                    .collect::<Result<_>>()?,
                values: [
                    self.value(values[0])?,
                    self.value(values[1])?,
                    self.value(values[2])?,
                ],
                body: Box::new(self.region(*body)?),
            },
            Shape::Continue => Region::Continue,
            Shape::Break => Region::Break,
            Shape::Return { values } => Region::Return(self.pack_value(values)?),
        })
    }

    /// Materializes every instruction in one FIR block.
    fn block(&self, block: usize) -> Result<Vec<Stmt>> {
        let Some(block_ref) = self.function.blocks.get(block) else {
            bail!("shape references invalid bb{block}")
        };
        let mut stmts: Vec<_> = self
            .initializations
            .by_block
            .get(block)
            .into_iter()
            .flatten()
            .map(|storage| self.initialization(*storage))
            .collect::<Result<_>>()?;
        for (instr, value) in block_ref.instrs.iter().enumerate() {
            if matches!(value, ir::Instr::Phi { .. }) {
                continue;
            }
            stmts.push(self.instr(InstrOrigin { block, instr }, value)?);
        }
        Ok(stmts)
    }

    /// Materializes one FIR instruction without moving it across another instruction.
    fn instr(&self, origin: InstrOrigin, instr: &ir::Instr) -> Result<Stmt> {
        let produced_value = |out, kind| {
            let local = self.local(out)?;
            let value = Expr::produced(origin, kind);
            if self.ssa.is_mutable(out) {
                Ok(Stmt::Assign {
                    origin: None,
                    target: Place::Local(local),
                    value,
                })
            } else {
                Ok(Stmt::Let { local, value })
            }
        };
        let produced_pack = |out, kind| {
            Ok(Stmt::LetPack {
                local: self.pack(out)?,
                value: PackExpr::produced(origin, kind),
            })
        };

        match instr {
            ir::Instr::Const { out, value } => {
                produced_value(*out, ExprKind::Constant(value.clone()))
            }
            ir::Instr::Copy { out, value } => {
                produced_value(*out, ExprKind::Local(self.local(*value)?))
            }
            ir::Instr::Closure {
                out,
                proto,
                captures,
            } => produced_value(
                *out,
                ExprKind::Closure {
                    proto: *proto,
                    captures: captures
                        .iter()
                        .map(|capture| match capture {
                            ir::Capture::Copy(value) => self.local(*value).map(Capture::Copy),
                            ir::Capture::Share(cell) => Ok(Capture::Share(*cell)),
                        })
                        .collect::<Result<_>>()?,
                },
            ),
            ir::Instr::GetTable { out, table, key } => produced_value(
                *out,
                ExprKind::GetTable {
                    table: Box::new(self.value(*table)?),
                    key: Box::new(self.value(*key)?),
                },
            ),
            ir::Instr::SetTable { table, key, value } => Ok(Stmt::Assign {
                origin: Some(origin),
                target: Place::Table {
                    table: self.value(*table)?,
                    key: self.value(*key)?,
                },
                value: self.value(*value)?,
            }),
            ir::Instr::GetGlobal { out, name } => {
                produced_value(*out, ExprKind::GetGlobal(name.clone()))
            }
            ir::Instr::SetGlobal { name, value } => Ok(Stmt::Assign {
                origin: Some(origin),
                target: Place::Global(name.clone()),
                value: self.value(*value)?,
            }),
            ir::Instr::Binary { out, lhs, op, rhs } => produced_value(
                *out,
                ExprKind::Binary {
                    lhs: Box::new(self.value(*lhs)?),
                    op: *op,
                    rhs: Box::new(self.value(*rhs)?),
                },
            ),
            ir::Instr::Unary { out, op, value } => produced_value(
                *out,
                ExprKind::Unary {
                    op: *op,
                    value: Box::new(self.value(*value)?),
                },
            ),
            ir::Instr::Concat { out, operands } => produced_value(
                *out,
                ExprKind::Concat(
                    operands
                        .iter()
                        .map(|value| self.value(*value))
                        .collect::<Result<_>>()?,
                ),
            ),
            ir::Instr::Select {
                out,
                condition,
                then_value,
                else_value,
            } => produced_value(
                *out,
                ExprKind::Select {
                    condition: Box::new(self.value(*condition)?),
                    then_value: Box::new(self.value(*then_value)?),
                    else_value: Box::new(self.value(*else_value)?),
                },
            ),
            ir::Instr::NewTable { out } => produced_value(*out, ExprKind::NewTable),
            ir::Instr::MakePack { out, head, tail } => produced_pack(
                *out,
                PackExprKind::Values {
                    head: head
                        .iter()
                        .map(|value| self.value(*value))
                        .collect::<Result<_>>()?,
                    tail: tail
                        .map(|pack| self.pack_value(pack).map(Box::new))
                        .transpose()?,
                },
            ),
            ir::Instr::Project { out, pack, index } => produced_value(
                *out,
                ExprKind::Project {
                    pack: Box::new(self.pack_value(*pack)?),
                    index: *index,
                },
            ),
            ir::Instr::Call {
                out,
                function,
                args,
            } => produced_pack(
                *out,
                PackExprKind::Call {
                    function: Box::new(self.value(*function)?),
                    args: Box::new(self.pack_value(*args)?),
                },
            ),
            ir::Instr::MethodCall {
                out,
                object,
                method,
                args,
            } => produced_pack(
                *out,
                PackExprKind::MethodCall {
                    object: Box::new(self.value(*object)?),
                    method: method.clone(),
                    args: Box::new(self.pack_value(*args)?),
                },
            ),
            ir::Instr::VarArgs { out } => produced_pack(*out, PackExprKind::VarArgs),
            ir::Instr::OpenCell { cell, value } => Ok(Stmt::OpenCell {
                origin,
                cell: *cell,
                value: self.value(*value)?,
            }),
            ir::Instr::LoadCell { out, cell } => produced_value(*out, ExprKind::LoadCell(*cell)),
            ir::Instr::StoreCell { cell, value } => Ok(Stmt::Assign {
                origin: Some(origin),
                target: Place::Cell(*cell),
                value: self.value(*value)?,
            }),
            ir::Instr::SetList {
                table,
                index,
                values,
            } => Ok(Stmt::SetList {
                origin,
                table: self.value(*table)?,
                index: *index,
                values: self.pack_value(*values)?,
            }),
            ir::Instr::Phi { .. } => bail!(
                "internal error: Phi bb{} instruction {} was not unfolded",
                origin.block,
                origin.instr
            ),
        }
    }

    /// Materializes one predicate without resolving its FIR value references early.
    fn predicate(&self, predicate: Predicate) -> Result<Expr> {
        Ok(match predicate {
            Predicate::Value(value) => self.value(value)?,
            Predicate::True => Expr::boolean(true),
            Predicate::False => Expr::boolean(false),
            Predicate::Not(inner) => Expr {
                origin: None,
                kind: ExprKind::Unary {
                    op: UnOp::Not,
                    value: Box::new(self.predicate(*inner)?),
                },
            },
            Predicate::And(lhs, rhs) => Expr {
                origin: None,
                kind: ExprKind::Binary {
                    lhs: Box::new(self.predicate(*lhs)?),
                    op: BinOp::And,
                    rhs: Box::new(self.predicate(*rhs)?),
                },
            },
            Predicate::Or(lhs, rhs) => Expr {
                origin: None,
                kind: ExprKind::Binary {
                    lhs: Box::new(self.predicate(*lhs)?),
                    op: BinOp::Or,
                    rhs: Box::new(self.predicate(*rhs)?),
                },
            },
            Predicate::Select {
                condition,
                then_predicate,
                else_predicate,
            } => Expr {
                origin: None,
                kind: ExprKind::Select {
                    condition: Box::new(self.predicate(*condition)?),
                    then_value: Box::new(self.predicate(*then_predicate)?),
                    else_value: Box::new(self.predicate(*else_predicate)?),
                },
            },
        })
    }
}
