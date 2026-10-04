//! FIR Shape to NIR Region materialization and inlining.

use crate::collections::{HashMap, HashSet};
use std::cell::RefCell;

use anyhow::{Result, bail};
use id_arena::Arena;

use super::visitor::VisitorMut;
use super::*;
use crate::ir::fir::folding::Folding;
use crate::ir::fir::region::{Predicate, Shape};
use crate::ir::fir::storage::Storage;
use crate::ir::fir::{self, PackId};
use crate::ir::graph::{DominatorTree, GraphView};
use crate::logging::Diagnostics;

/// Structures the FIR function into a control shape, then lifts it to NIR.
pub(crate) fn lift(function: fir::Function, diagnostics: &Diagnostics) -> Result<Function> {
    let storage = Storage::build(&function);
    let folding = Folding::build(&function, &storage);
    let shape = fir::region::structure(&function, &folding, diagnostics)?;
    materialize(function, &storage, &folding, shape)
}

/// Converts one verified control shape into NIR with distinct FIR SSA symbols.
pub(crate) fn materialize(
    function: fir::Function,
    storage: &Storage,
    folding: &Folding,
    shape: Shape,
) -> Result<Function> {
    let mut result = {
        let ssa = SsaMeta::build(&function, storage);
        let initializations = Initializations::build(&function, &ssa, &shape);
        Materializer::new(&function, folding, &ssa, initializations).materialize(shape)?
    };
    for (target, source) in result.bindings.iter_mut().zip(function.bindings) {
        target.cells = source.cells;
    }
    result.debug = function.debug;
    result.upvalues = function.upvalues;
    Ok(result)
}

/// Unifies NIR symbols which point to the same underlying storage.
pub(crate) fn destroy_ssa(function: &mut Function) {
    let mut locals_by_source = HashMap::default();
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
    for local in function.cell_locals.values_mut() {
        rewriter.visit_local(local);
    }
    for binding in &mut function.bindings {
        for local in &mut binding.locals {
            rewriter.visit_local(local);
        }
        binding.locals.sort_unstable_by_key(|local| local.index());
        binding.locals.dedup();
    }
    rewriter.visit_stmts(&mut function.prologue);
    rewriter.visit_region(&mut function.body);
}

/// Describes the underlying storage required by one FIR function.
struct SsaMeta<'s> {
    /// Canonical storage for every FIR value.
    storage: &'s Storage,
    /// A list of synthetic nil declarations grouped by dominating block.
    declarations: Vec<Vec<ValueId>>,
    /// Immediate dominators for every reachable FIR block.
    idoms: DominatorTree<usize>,
}

impl<'s> SsaMeta<'s> {
    /// Places a declaration for every storage assigned through block parameters.
    fn build(function: &fir::Function, storage: &'s Storage) -> Self {
        let cfg = &function.cfg;
        let idoms = cfg.build_idoms();

        let mut storage_blocks: HashMap<_, Vec<_>> = HashMap::default();
        for block in cfg.post_order() {
            for param in &cfg[block].params {
                storage_blocks
                    .entry(storage.of(*param))
                    .or_default()
                    .push(block);
            }
        }

        let params: HashSet<_> = function
            .params
            .iter()
            .map(|value| storage.of(*value))
            .collect();
        let mut declarations = vec![Vec::new(); cfg.len()];
        for (storage_id, blocks) in storage_blocks {
            if params.contains(&storage_id) || storage.is_loop_storage(storage_id) {
                continue;
            }
            let declaration = idoms.common_strict_dominator(cfg.entry(), &blocks);
            declarations[declaration].push(storage_id);
        }

        Self {
            storage,
            declarations,
            idoms,
        }
    }

    /// Returns the canonical storage for one FIR value.
    #[inline]
    fn storage(&self, value: ValueId) -> ValueId {
        self.storage.of(value)
    }

    /// Returns whether concrete code defines the storage before its declaration point.
    fn is_defined_before_use(
        &self,
        function: &fir::Function,
        block: usize,
        storage: ValueId,
    ) -> bool {
        let mut dominator = self.idoms.idom(block);
        while let Some(block) = dominator {
            if self.block_defines_storage(function, block, storage) {
                return true;
            }
            dominator = self.idoms.idom(block);
        }

        for instr in &function.cfg[block].instrs {
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

    /// Returns whether one block contains a concrete definition of the storage.
    #[inline]
    fn block_defines_storage(
        &self,
        function: &fir::Function,
        block: usize,
        storage: ValueId,
    ) -> bool {
        function.cfg[block].instrs.iter().any(|instr| {
            instr
                .defined_value()
                .is_some_and(|value| self.storage(value) == storage)
        })
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
        let mut emitted_blocks = HashSet::default();
        collect_emitted_blocks(shape, &mut emitted_blocks);

        let mut by_block = vec![Vec::new(); function.cfg.len()];
        let mut prologue = Vec::new();
        for (block, storages) in ssa.declarations.iter().enumerate() {
            if emitted_blocks.contains(&block) {
                by_block[block].extend(
                    storages
                        .iter()
                        .copied()
                        .filter(|storage| !ssa.is_defined_before_use(function, block, *storage)),
                );
            } else {
                prologue.extend(storages.iter().copied());
            }
        }

        Self { by_block, prologue }
    }
}

/// Collects FIR blocks which appear anywhere in the shape.
///
/// A block appears as a statement block, as a predicate block whose branch
/// decides part of a condition, or as both. Declarations of statement blocks
/// open the block itself, those of predicate-only blocks are placed right
/// before the structured node testing the predicate. Declarations of blocks
/// which never appear fall back to the function prologue.
fn collect_emitted_blocks(shape: &Shape, blocks: &mut HashSet<usize>) {
    match shape {
        Shape::Block { block } => {
            blocks.insert(*block);
        }
        Shape::Sequence { nodes } => {
            for node in nodes {
                collect_emitted_blocks(node, blocks);
            }
        }
        Shape::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_predicate_blocks(condition, blocks);
            collect_emitted_blocks(then_branch, blocks);
            if let Some(else_branch) = else_branch {
                collect_emitted_blocks(else_branch, blocks);
            }
        }
        Shape::While { condition, body } | Shape::RepeatUntil { condition, body } => {
            collect_predicate_blocks(condition, blocks);
            collect_emitted_blocks(body, blocks);
        }
        Shape::NumericFor { body, .. } | Shape::GenericFor { body, .. } => {
            collect_emitted_blocks(body, blocks);
        }
        Shape::Continue | Shape::Break | Shape::Return { .. } => {}
    }
}

/// Collects FIR blocks whose branch decides part of a predicate.
fn collect_predicate_blocks(predicate: &Predicate, blocks: &mut HashSet<usize>) {
    match predicate {
        Predicate::Value { block, .. } => {
            blocks.insert(*block);
        }
        Predicate::True | Predicate::False => {}
        Predicate::Not(inner) => collect_predicate_blocks(inner, blocks),
        Predicate::And(lhs, rhs) | Predicate::Or(lhs, rhs) => {
            collect_predicate_blocks(lhs, blocks);
            collect_predicate_blocks(rhs, blocks);
        }
        Predicate::Select {
            condition,
            then_predicate,
            else_predicate,
        } => {
            collect_predicate_blocks(condition, blocks);
            collect_predicate_blocks(then_predicate, blocks);
            collect_predicate_blocks(else_predicate, blocks);
        }
    }
}

/// Collects FIR blocks materialized as statement blocks.
fn collect_statement_blocks(shape: &Shape, blocks: &mut HashSet<usize>) {
    match shape {
        Shape::Block { block } => {
            blocks.insert(*block);
        }
        Shape::Sequence { nodes } => {
            for node in nodes {
                collect_statement_blocks(node, blocks);
            }
        }
        Shape::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_statement_blocks(then_branch, blocks);
            if let Some(else_branch) = else_branch {
                collect_statement_blocks(else_branch, blocks);
            }
        }
        Shape::While { body, .. }
        | Shape::RepeatUntil { body, .. }
        | Shape::NumericFor { body, .. }
        | Shape::GenericFor { body, .. } => collect_statement_blocks(body, blocks),
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
    /// Definitions which are materialized at their single use.
    folding: &'f Folding,
    /// Instruction defining every FIR value.
    value_defs: HashMap<ValueId, &'f fir::Instr>,
    /// Instruction defining every FIR pack.
    pack_defs: HashMap<PackId, &'f fir::Instr>,
    /// Folded definitions already materialized at their use.
    emitted: RefCell<Emitted>,
    /// Blocks materialized as statement blocks.
    statement_blocks: HashSet<usize>,
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

/// Folded definitions materialized so far.
#[derive(Debug, Default)]
struct Emitted {
    /// Folded values materialized at their use.
    values: HashSet<ValueId>,
    /// Folded packs materialized at their use.
    packs: HashSet<PackId>,
}

impl<'a> Materializer<'a> {
    /// Creates one stable NIR identity for every FIR SSA value and pack.
    fn new(
        function: &'a fir::Function,
        folding: &'a Folding,
        ssa: &SsaMeta,
        initializations: Initializations,
    ) -> Self {
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

        let mut value_defs = HashMap::default();
        let mut pack_defs = HashMap::default();
        for instr in function.cfg.items().flat_map(|block| block.instrs.iter()) {
            if let Some(value) = instr.defined_value() {
                value_defs.insert(value, instr);
            }
            if let Some(pack) = instr.defined_pack() {
                pack_defs.insert(pack, instr);
            }
        }

        Self {
            function,
            folding,
            value_defs,
            pack_defs,
            emitted: RefCell::default(),
            statement_blocks: HashSet::default(),
            locals,
            packs,
            values,
            pack_values,
            initializations,
        }
    }

    /// Materializes the complete shape.
    fn materialize(mut self, shape: Shape) -> Result<Function> {
        collect_statement_blocks(&shape, &mut self.statement_blocks);
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
        let cell_locals = self.cell_locals()?;
        let bindings = self
            .function
            .bindings
            .iter()
            .map(|binding| {
                let locals = binding
                    .values
                    .iter()
                    .map(|value| self.local(*value))
                    .collect::<Result<_>>()?;
                Ok(DebugBinding {
                    locals,
                    cells: Vec::new(),
                })
            })
            .collect::<Result<_>>()?;
        let body = self.region(shape)?;
        self.verify_folded()?;
        let function = Function {
            id: self.function.id,
            debug: Default::default(),
            bindings,
            locals: self.locals,
            packs: self.packs,
            params,
            is_vararg: self.function.is_vararg,
            upvalues: Vec::new(),
            cell_locals,
            prologue,
            body,
        };
        Ok(function)
    }

    /// Finds the source local which backs every locally opened cell.
    fn cell_locals(&self) -> Result<HashMap<CellId, LocalId>> {
        let mut cell_locals = HashMap::default();
        for instr in self
            .function
            .cfg
            .items()
            .flat_map(|block| block.instrs.iter())
        {
            let fir::Instr::OpenCell { cell, value } = instr else {
                continue;
            };
            let local = self.local(*value)?;
            if let Some(previous) = cell_locals.insert(*cell, local)
                && self.locals[previous].source != self.locals[local].source
            {
                bail!("cell was opened from unrelated source locals");
            }
        }
        Ok(cell_locals)
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

    /// Creates the expression for one FIR value at its use.
    ///
    /// Folded values are rebuilt from their definition, everything else reads its local.
    fn value(&self, value: ValueId) -> Result<Expr> {
        if !self.folding.is_folded(value) {
            return Ok(Expr::local(self.local(value)?));
        }
        // The structurer may duplicate a block, and its trees along with it.
        self.emitted.borrow_mut().values.insert(value);
        let Some(instr) = self.value_defs.get(&value) else {
            bail!("folded %v{} has no defining instruction", value.index());
        };
        self.value_expr(instr)
    }

    /// Creates the pack expression for one FIR pack at its use.
    ///
    /// Folded packs are rebuilt from their definition, everything else reads its pack local.
    fn pack_value(&self, pack: PackId) -> Result<PackExpr> {
        if !self.folding.is_pack_folded(pack) {
            return Ok(PackExpr::local(self.pack(pack)?));
        }
        self.emitted.borrow_mut().packs.insert(pack);
        let Some(instr) = self.pack_defs.get(&pack) else {
            bail!("folded %q{} has no defining instruction", pack.index());
        };
        self.pack_expr(instr)
    }

    /// Checks that every positioned folded definition of a structured block was materialized.
    ///
    /// A folded definition which is never reached would silently drop its evaluation.
    /// Blocks which the structurer replaced by an equivalent block are not checked.
    fn verify_folded(&self) -> Result<()> {
        let emitted = self.emitted.borrow();
        for (block_id, block) in self.function.cfg.items().enumerate() {
            if !self.statement_blocks.contains(&block_id)
                && !self.folding.is_condition_only(block_id)
            {
                continue;
            }
            for instr in &block.instrs {
                if let Some(value) = instr.defined_value()
                    && self.folding.is_folded(value)
                    && !self.folding.is_floating(value)
                    && !emitted.values.contains(&value)
                {
                    bail!(
                        "folded %v{} in @P{} bb{block_id} was never materialized",
                        value.index(),
                        self.function.id.0
                    );
                }
                if let Some(pack) = instr.defined_pack()
                    && self.folding.is_pack_folded(pack)
                    && !emitted.packs.contains(&pack)
                {
                    bail!(
                        "folded %q{} in @P{} bb{block_id} was never materialized",
                        pack.index(),
                        self.function.id.0
                    );
                }
            }
        }
        Ok(())
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
            } => self.with_predicate_declarations(
                &condition,
                Region::If {
                    condition: self.predicate(condition.clone())?,
                    then_branch: Box::new(self.region(*then_branch)?),
                    else_branch: else_branch
                        .map(|branch| self.region(*branch).map(Box::new))
                        .transpose()?,
                },
            )?,
            Shape::While { condition, body } => self.with_predicate_declarations(
                &condition,
                Region::While {
                    condition: self.predicate(condition.clone())?,
                    body: Box::new(self.region(*body)?),
                },
            )?,
            Shape::RepeatUntil { condition, body } => self.with_predicate_declarations(
                &condition,
                Region::RepeatUntil {
                    condition: self.predicate(condition.clone())?,
                    body: Box::new(self.region(*body)?),
                },
            )?,
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

    /// Places declarations of predicate-only blocks right before the node testing them.
    fn with_predicate_declarations(&self, predicate: &Predicate, node: Region) -> Result<Region> {
        let mut blocks = HashSet::default();
        collect_predicate_blocks(predicate, &mut blocks);
        let mut blocks: Vec<_> = blocks
            .into_iter()
            .filter(|block| !self.statement_blocks.contains(block))
            .collect();
        blocks.sort_unstable();

        let mut nodes = Vec::new();
        for block in blocks {
            let stmts = self
                .initializations
                .by_block
                .get(block)
                .into_iter()
                .flatten()
                .map(|storage| self.initialization(*storage))
                .collect::<Result<Vec<_>>>()?;
            if !stmts.is_empty() {
                nodes.push(Region::Block {
                    origin: block,
                    stmts,
                });
            }
        }
        if nodes.is_empty() {
            return Ok(node);
        }
        nodes.push(node);
        Ok(Region::Sequence(nodes))
    }

    /// Materializes every instruction in one FIR block.
    fn block(&self, block: usize) -> Result<Vec<Stmt>> {
        let Some(block_ref) = self.function.cfg.get(block) else {
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
        for (index, instr) in block_ref.instrs.iter().enumerate() {
            if self.folding.is_initializer((block, index)) {
                continue;
            }
            let folded = instr
                .defined_value()
                .is_some_and(|value| self.folding.is_folded(value))
                || instr
                    .defined_pack()
                    .is_some_and(|pack| self.folding.is_pack_folded(pack));
            if !folded {
                stmts.push(self.instr(instr)?);
            }
        }
        Ok(stmts)
    }

    /// Materializes one FIR instruction as a statement.
    fn instr(&self, instr: &fir::Instr) -> Result<Stmt> {
        if let Some(out) = instr.defined_value() {
            return Ok(Stmt::Bind {
                target: Place::Local(self.local(out)?),
                value: self.value_expr(instr)?,
            });
        }
        if let Some(out) = instr.defined_pack() {
            return Ok(Stmt::BindPack {
                local: self.pack(out)?,
                value: self.pack_expr(instr)?,
            });
        }

        match instr {
            fir::Instr::SetTable { table, key, value } => Ok(Stmt::Bind {
                target: Place::Table {
                    table: self.value(*table)?,
                    key: self.value(*key)?,
                },
                value: self.value(*value)?,
            }),
            fir::Instr::SetGlobal { name, value } => Ok(Stmt::Bind {
                target: Place::Global(name.clone()),
                value: self.value(*value)?,
            }),
            fir::Instr::OpenCell { cell, value } => Ok(Stmt::OpenCell {
                cell: *cell,
                value: self.value(*value)?,
            }),
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
            _ => bail!("instruction defines neither a value nor a pack"),
        }
    }

    /// Materializes the expression computed by one value-defining FIR instruction.
    fn value_expr(&self, instr: &fir::Instr) -> Result<Expr> {
        Ok(match instr {
            fir::Instr::Const { value, .. } => Expr::Constant(value.clone()),
            fir::Instr::Copy { value, .. } => self.value(*value)?,
            fir::Instr::Closure {
                proto, captures, ..
            } => Expr::Closure {
                proto: *proto,
                captures: captures
                    .iter()
                    .map(|capture| match capture {
                        fir::Capture::Copy(value) => self.local(*value).map(Capture::Copy),
                        fir::Capture::Share(cell) => Ok(Capture::Share(*cell)),
                    })
                    .collect::<Result<_>>()?,
            },
            fir::Instr::GetTable { table, key, .. } => Expr::GetTable {
                table: Box::new(self.value(*table)?),
                key: Box::new(self.value(*key)?),
            },
            fir::Instr::GetGlobal { name, .. } => Expr::GetGlobal(name.clone()),
            fir::Instr::Binary { out, lhs, op, rhs } => {
                if self.folding.is_mirrored(*out) {
                    // Operands are built in evaluation order, which is right to left here.
                    let rhs = self.value(*rhs)?;
                    let lhs = self.value(*lhs)?;
                    Expr::Binary {
                        lhs: Box::new(rhs),
                        op: match op {
                            BinOp::Lt => BinOp::Gt,
                            BinOp::Lte => BinOp::Gte,
                            _ => bail!("only ordered comparisons can be mirrored"),
                        },
                        rhs: Box::new(lhs),
                    }
                } else {
                    Expr::Binary {
                        lhs: Box::new(self.value(*lhs)?),
                        op: *op,
                        rhs: Box::new(self.value(*rhs)?),
                    }
                }
            }
            fir::Instr::Unary { op, value, .. } => Expr::Unary {
                op: *op,
                value: Box::new(self.value(*value)?),
            },
            fir::Instr::Concat { operands, .. } => Expr::Concat(
                operands
                    .iter()
                    .map(|value| self.value(*value))
                    .collect::<Result<_>>()?,
            ),
            fir::Instr::Select {
                condition,
                then_value,
                else_value,
                ..
            } => Expr::Select {
                condition: Box::new(self.value(*condition)?),
                then_value: Box::new(self.value(*then_value)?),
                else_value: Box::new(self.value(*else_value)?),
            },
            fir::Instr::NewTable { out } => Expr::Table {
                items: match self.folding.constructor(*out) {
                    Some(initializers) => self.table_items(initializers)?,
                    None => Vec::new(),
                },
            },
            fir::Instr::Project { pack, index, .. } => Expr::Project {
                pack: Box::new(self.pack_value(*pack)?),
                index: *index,
            },
            fir::Instr::LoadCell { cell, .. } => Expr::LoadCell(*cell),
            _ => bail!("instruction does not define a value"),
        })
    }

    /// Materializes the initializers of a folded table constructor as table items.
    ///
    /// Array stores which continue the array part become list items, any other
    /// array store becomes explicitly indexed items.
    fn table_items(&self, initializers: &[(usize, usize)]) -> Result<Vec<TableItem>> {
        let mut items = Vec::with_capacity(initializers.len());
        let mut array_len = Some(0usize);
        for &(block, index) in initializers {
            match &self.function.cfg[block].instrs[index] {
                fir::Instr::SetTable { key, value, .. } => {
                    items.push(TableItem::Index(self.value(*key)?, self.value(*value)?));
                }
                fir::Instr::SetList {
                    index: base,
                    values,
                    ..
                } => {
                    let values = self.pack_value(*values)?;
                    if array_len.is_some_and(|len| *base as usize == len + 1) {
                        array_len = values
                            .fixed_len()
                            .and_then(|fixed| array_len.map(|len| len + fixed));
                        items.push(TableItem::List(values));
                    } else {
                        items.extend(values.into_iter().enumerate().map(|(offset, value)| {
                            let key = Expr::Constant(fir::Constant::Number(fir::Number::Float(
                                *base as f64 + offset as f64,
                            )));
                            TableItem::Index(key, value)
                        }));
                    }
                }
                _ => bail!("table constructor initializer is not a table store"),
            }
        }
        Ok(items)
    }

    /// Materializes the pack computed by one pack-defining FIR instruction.
    fn pack_expr(&self, instr: &fir::Instr) -> Result<PackExpr> {
        Ok(match instr {
            fir::Instr::MakePack { head, tail, .. } => PackExpr::Values {
                head: head
                    .iter()
                    .map(|value| self.value(*value))
                    .collect::<Result<_>>()?,
                tail: tail
                    .map(|pack| self.pack_value(pack).map(Box::new))
                    .transpose()?,
            },
            fir::Instr::Call { function, args, .. } => PackExpr::Call {
                function: Box::new(self.value(*function)?),
                args: Box::new(self.pack_value(*args)?),
            },
            fir::Instr::MethodCall {
                object,
                method,
                args,
                ..
            } => PackExpr::MethodCall {
                object: Box::new(self.value(*object)?),
                method: method.clone(),
                args: Box::new(self.pack_value(*args)?),
            },
            fir::Instr::VarArgs { .. } => PackExpr::VarArgs,
            _ => bail!("instruction does not define a pack"),
        })
    }

    /// Materializes one predicate without resolving its FIR value references early.
    fn predicate(&self, predicate: Predicate) -> Result<Expr> {
        Ok(match predicate {
            Predicate::Value { value, .. } => self.value(value)?,
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
