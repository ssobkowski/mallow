//! FIR Shape to NIR Region materialization and inlining.

use std::collections::{HashMap, HashSet};

use anyhow::{Result, bail};
use id_arena::Arena;

use super::visitor::VisitorMut;
use super::*;
use crate::hil::cflow::graph::{AdjGraph, DominatorTree, GraphView, build_graph};
use crate::hil::cflow::union_find::UnionFind;
use crate::ir::fir;
use crate::ir::fir::PackId;
use crate::ir::fir::region::{Predicate, Shape};
use crate::logging::Diagnostics;

/// Recognizes and materializes one FIR function as nested NIR.
pub(crate) fn lower(function: &fir::Function, diagnostics: &Diagnostics) -> Result<Function> {
    let shape = fir::region::structure(function, diagnostics)?;
    materialize(function, shape)
}

/// Converts one verified control shape into NIR with distinct FIR SSA symbols.
pub(crate) fn materialize(function: &fir::Function, shape: Shape) -> Result<Function> {
    let ssa = SsaMeta::build(function)?;
    let initializations = Initializations::build(function, &ssa, &shape);
    Materializer::new(function, &ssa, initializations).materialize(shape)
}

/// Unifies NIR symbols which point to the same underlying storage.
pub(crate) fn destroy_ssa(function: &mut Function) {
    let mut locals_by_source = HashMap::new();
    let replacements: HashMap<_, _> = function
        .locals
        .iter()
        .map(|(local, data)| {
            let replacement = *locals_by_source.entry(data.source).or_insert(local);
            (local, replacement)
        })
        .collect();

    let mut rewriter = LocalRewriter {
        replacements: &replacements,
    };
    for parameter in &mut function.params {
        rewriter.visit_local(parameter);
    }
    rewriter.visit_stmts(&mut function.prologue);
    rewriter.visit_region(&mut function.body);
}

/// Describes the underlying storage required by one FIR function.
struct SsaMeta {
    /// Canonical storage for every FIR value.
    storage: HashMap<ValueId, ValueId>,
    /// A list of synthetic nil declarations grouped by dominating block.
    declarations: Vec<Vec<ValueId>>,
}

impl SsaMeta {
    /// Groups Phi inputs which will use the same mutable storage.
    fn build(function: &fir::Function) -> Result<Self> {
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
                let fir::Instr::Phi { out, inputs } = instr else {
                    continue;
                };

                phi_blocks.push((*out, block_index));
                for &(predecessor, input) in inputs {
                    // TODO: Is this necessary?
                    let is_loop_header_initializer = match &function.blocks[predecessor].exit {
                        fir::BlockExit::NumericFor {
                            body_block,
                            variable,
                            ..
                        } => *body_block == block_index && variable == out,
                        fir::BlockExit::GenericFor {
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
                fir::BlockExit::NumericFor { variable, .. } => {
                    loop_values.push(*variable);
                }
                fir::BlockExit::GenericFor {
                    loop_block,
                    variables: init_variables,
                    ..
                } => {
                    loop_values.extend(init_variables.iter().copied());
                    let fir::BlockExit::GenericForLoop {
                        variables: body_variables,
                        ..
                    } = &function.blocks[*loop_block].exit
                    else {
                        unreachable!("raw CFG validation guarantees the generic loop target")
                    };

                    for (entry, body) in init_variables.iter().zip(body_variables) {
                        groups.union(*entry, *body);
                    }
                }
                fir::BlockExit::GenericForLoop { variables, .. } => {
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
            declarations,
        })
    }

    /// Returns the canonical storage for one FIR value.
    #[inline]
    fn storage(&self, value: ValueId) -> ValueId {
        self.storage[&value]
    }

    /// Returns whether one concrete instruction defines the storage before it is read.
    fn is_defined_before_use_in_block(
        &self,
        function: &fir::Function,
        block: usize,
        storage: ValueId,
    ) -> bool {
        for instr in &function.blocks[block].instrs {
            if matches!(instr, fir::Instr::Phi { .. }) {
                continue;
            }
            if instr
                .used_values()
                .into_iter()
                .any(|value| self.storage(value) == storage)
            {
                return false;
            }
            if instr
                .defined_value()
                .is_some_and(|value| self.storage(value) == storage)
            {
                return true;
            }
        }

        false
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
    /// Places storage without a concrete definition at its block or in the function prologue.
    fn build(function: &fir::Function, ssa: &SsaMeta, shape: &Shape) -> Self {
        let mut initialization_blocks = HashSet::new();
        collect_initialization_blocks(shape, &mut initialization_blocks);

        let mut by_block = vec![Vec::new(); function.blocks.len()];
        let mut prologue = Vec::new();
        for (block, storages) in ssa.declarations.iter().enumerate() {
            if initialization_blocks.contains(&block) {
                by_block[block].extend(storages.iter().copied().filter(|storage| {
                    !ssa.is_defined_before_use_in_block(function, block, *storage)
                }));
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

    let mut candidate = *first;
    for &block in rest {
        while !idoms.dominates(candidate, block) {
            candidate = idoms.idom(candidate).unwrap_or(entry);
        }
    }
    idoms.idom(candidate).unwrap_or(entry)
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

/// Rewrites SSA local references to their shared storage locals.
struct LocalRewriter<'a> {
    /// Shared storage local for every SSA local.
    replacements: &'a HashMap<LocalId, LocalId>,
}

impl VisitorMut for LocalRewriter<'_> {
    fn visit_local(&mut self, local: &mut LocalId) {
        *local = self.replacements[local];
    }
}

/// State used while converting FIR references into NIR identities.
struct Materializer<'f> {
    /// FIR function being converted.
    function: &'f fir::Function,
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
    /// Creates one stable NIR identity for every FIR SSA value and pack.
    fn new(function: &'a fir::Function, ssa: &SsaMeta, initializations: Initializations) -> Self {
        let mut locals = Arena::new();
        let values = function
            .values
            .iter()
            .map(|(value, _)| {
                let source = ssa.storage(value);
                (value, locals.alloc(Local { source }))
            })
            .collect();

        let mut packs = Arena::new();
        let pack_values = function
            .packs
            .iter()
            .map(|(source, _)| (source, packs.alloc(PackLocal { source })))
            .collect();

        Self {
            function,
            locals,
            packs,
            values,
            pack_values,
            initializations,
        }
    }

    /// Materializes the complete shape.
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
        let function = Function {
            id: self.function.proto,
            locals: self.locals,
            packs: self.packs,
            params,
            is_vararg: self.function.is_vararg,
            upvalues: self.function.upvalues.clone(),
            prologue,
            body,
        };
        Ok(function)
    }

    /// Creates one synthetic nil declaration for mutable storage.
    #[inline]
    fn initialization(&self, storage: ValueId) -> Result<Stmt> {
        Ok(Stmt::Bind {
            target: Place::Local(self.local(storage)?),
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
        for instr in &block_ref.instrs {
            if matches!(instr, fir::Instr::Phi { .. }) {
                continue;
            }
            stmts.push(self.instr(instr)?);
        }
        Ok(stmts)
    }

    /// Materializes one FIR instruction without moving it across another instruction.
    fn instr(&self, instr: &fir::Instr) -> Result<Stmt> {
        let local = |out, value| {
            Ok(Stmt::Bind {
                target: Place::Local(self.local(out)?),
                value,
            })
        };
        let pack = |out, value| {
            Ok(Stmt::BindPack {
                local: self.pack(out)?,
                value,
            })
        };

        match instr {
            fir::Instr::Const { out, value } => local(*out, Expr::Constant(value.clone())),
            fir::Instr::Copy { out, value } => local(*out, Expr::Local(self.local(*value)?)),
            fir::Instr::Closure {
                out,
                proto,
                captures,
            } => local(
                *out,
                Expr::Closure {
                    proto: *proto,
                    captures: captures
                        .iter()
                        .map(|capture| match capture {
                            fir::Capture::Copy(value) => self.local(*value).map(Capture::Copy),
                            fir::Capture::Share(cell) => Ok(Capture::Share(*cell)),
                        })
                        .collect::<Result<_>>()?,
                },
            ),
            fir::Instr::GetTable { out, table, key } => local(
                *out,
                Expr::GetTable {
                    table: Box::new(self.value(*table)?),
                    key: Box::new(self.value(*key)?),
                },
            ),
            fir::Instr::SetTable { table, key, value } => Ok(Stmt::Bind {
                target: Place::Table {
                    table: self.value(*table)?,
                    key: self.value(*key)?,
                },
                value: self.value(*value)?,
            }),
            fir::Instr::GetGlobal { out, name } => local(*out, Expr::GetGlobal(name.clone())),
            fir::Instr::SetGlobal { name, value } => Ok(Stmt::Bind {
                target: Place::Global(name.clone()),
                value: self.value(*value)?,
            }),
            fir::Instr::Binary { out, lhs, op, rhs } => local(
                *out,
                Expr::Binary {
                    lhs: Box::new(self.value(*lhs)?),
                    op: *op,
                    rhs: Box::new(self.value(*rhs)?),
                },
            ),
            fir::Instr::Unary { out, op, value } => local(
                *out,
                Expr::Unary {
                    op: *op,
                    value: Box::new(self.value(*value)?),
                },
            ),
            fir::Instr::Concat { out, operands } => local(
                *out,
                Expr::Concat(
                    operands
                        .iter()
                        .map(|value| self.value(*value))
                        .collect::<Result<_>>()?,
                ),
            ),
            fir::Instr::Select {
                out,
                condition,
                then_value,
                else_value,
            } => local(
                *out,
                Expr::Select {
                    condition: Box::new(self.value(*condition)?),
                    then_value: Box::new(self.value(*then_value)?),
                    else_value: Box::new(self.value(*else_value)?),
                },
            ),
            fir::Instr::NewTable { out } => local(*out, Expr::NewTable),
            fir::Instr::MakePack { out, head, tail } => pack(
                *out,
                PackExpr::Values {
                    head: head
                        .iter()
                        .map(|value| self.value(*value))
                        .collect::<Result<_>>()?,
                    tail: tail
                        .map(|pack| self.pack_value(pack).map(Box::new))
                        .transpose()?,
                },
            ),
            fir::Instr::Project { out, pack, index } => local(
                *out,
                Expr::Project {
                    pack: Box::new(self.pack_value(*pack)?),
                    index: *index,
                },
            ),
            fir::Instr::Call {
                out,
                function,
                args,
            } => pack(
                *out,
                PackExpr::Call {
                    function: Box::new(self.value(*function)?),
                    args: Box::new(self.pack_value(*args)?),
                },
            ),
            fir::Instr::MethodCall {
                out,
                object,
                method,
                args,
            } => pack(
                *out,
                PackExpr::MethodCall {
                    object: Box::new(self.value(*object)?),
                    method: method.clone(),
                    args: Box::new(self.pack_value(*args)?),
                },
            ),
            fir::Instr::VarArgs { out } => pack(*out, PackExpr::VarArgs),
            fir::Instr::OpenCell { cell, value } => Ok(Stmt::OpenCell {
                cell: *cell,
                value: self.value(*value)?,
            }),
            fir::Instr::LoadCell { out, cell } => local(*out, Expr::LoadCell(*cell)),
            fir::Instr::StoreCell { cell, value } => Ok(Stmt::Bind {
                target: Place::Cell(*cell),
                value: self.value(*value)?,
            }),
            fir::Instr::SetList {
                table,
                index,
                values,
            } => Ok(Stmt::SetList {
                table: self.value(*table)?,
                index: *index,
                values: self.pack_value(*values)?,
            }),
            fir::Instr::Phi { .. } => {
                unreachable!("Phi instructions are skipped by block materialization")
            }
        }
    }

    /// Materializes one predicate without resolving its FIR value references early.
    fn predicate(&self, predicate: Predicate) -> Result<Expr> {
        Ok(match predicate {
            Predicate::Value(value) => self.value(value)?,
            Predicate::True => Expr::boolean(true),
            Predicate::False => Expr::boolean(false),
            Predicate::Not(inner) => Expr::Unary {
                op: UnOp::Not,
                value: Box::new(self.predicate(*inner)?),
            },
            Predicate::And(lhs, rhs) => Expr::Binary {
                lhs: Box::new(self.predicate(*lhs)?),
                op: BinOp::And,
                rhs: Box::new(self.predicate(*rhs)?),
            },
            Predicate::Or(lhs, rhs) => Expr::Binary {
                lhs: Box::new(self.predicate(*lhs)?),
                op: BinOp::Or,
                rhs: Box::new(self.predicate(*rhs)?),
            },
            Predicate::Select {
                condition,
                then_predicate,
                else_predicate,
            } => Expr::Select {
                condition: Box::new(self.predicate(*condition)?),
                then_value: Box::new(self.predicate(*then_predicate)?),
                else_value: Box::new(self.predicate(*else_predicate)?),
            },
        })
    }
}
