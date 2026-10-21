use std::borrow::Cow;
use std::collections::VecDeque;

use anyhow::{Context, Result, bail, ensure};
use id_arena::Arena;
use smallvec::{SmallVec, smallvec};
use smol_str::{SmolStr, ToSmolStr};

use super::cflow::{Cond, CondRhs, RawBlock, RawBlockExit, build_raw_from_proto};
use super::ssa::Ssa;
use super::{
    self as ir, Block, BlockExit, Capture, DebugBinding, Function, Pack, PackId, Value, ValueId,
};
use crate::collections::{ArenaSet, HashMap, HashSet, IndexMap, IndexSet};
use crate::common::ByteString;
use crate::disasm::Chunk;
use crate::il::{
    self, ChildProtoId, ConstId, Count, DecodedInstr, ImportPath, Proto, ProtoId, ProtoTypeInfo,
    reg_add, reg_range,
};
use crate::ir::fir::{Cell, CellId, CellOrigin, ControlFlowGraph, Edge, Number};
use crate::ir::graph::{GraphView as _, GraphViewMut as _};
use crate::ir::{Debug, DebugLocal, Unit, UserdataTypeMapping};
use crate::operator::{BinOp, UnOp};

pub const CAPTURE_VAL: u8 = 0;
pub const CAPTURE_REF: u8 = 1;
pub const CAPTURE_UPVAL: u8 = 2;

/// A deferred value pack waiting for a variadic consumer.
#[derive(Debug, Clone, Copy)]
enum PendingValues {
    /// Results produced by a call.
    Call { base: u8, pack: PackId },
    /// Values read from the current function's variadic arguments.
    VarArgs { base: u8, pack: PackId },
}

impl PendingValues {
    /// Returns the first register represented by this pack.
    const fn base(self) -> u8 {
        match self {
            Self::Call { base, .. } | Self::VarArgs { base, .. } => base,
        }
    }

    /// Returns the deferred IR pack.
    const fn pack(self) -> PackId {
        match self {
            Self::Call { pack, .. } | Self::VarArgs { pack, .. } => pack,
        }
    }
}

/// A register value that can be projected from an open pack when needed.
#[derive(Debug, Clone, Copy)]
struct DeferredValue {
    /// Pack that contains the value.
    pack: PackId,
    /// Zero-based position in the pack.
    index: usize,
}

/// Identifies a place where a cell is first opened.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
enum OpenSite {
    /// A reference capture that found its register closed.
    Capture { block: usize, instr: usize },
    /// A cell forced open at the end of a block, before the block's exit.
    Hoisted { block: usize, reg: u8 },
}

/// Capture storage state for physical registers.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CaptureState {
    /// Site that opened each captured register's cell.
    open: Box<[Option<OpenSite>]>,
}

impl CaptureState {
    /// Creates a new capture state with the given amount of register slots.
    fn new(slots: u8) -> Self {
        Self {
            open: vec![None; slots as usize].into_boxed_slice(),
        }
    }

    /// Returns the site that opened one register's cell.
    fn open_site(&self, reg: u8) -> Option<OpenSite> {
        self.open[reg as usize]
    }

    /// Opens one register's cell at a site unless it is already open.
    ///
    /// Returns whether this site opened the cell.
    fn open_at(&mut self, reg: u8, site: OpenSite) -> bool {
        let slot = &mut self.open[reg as usize];
        let opened = slot.is_none();
        slot.get_or_insert(site);
        opened
    }

    /// Closes captured registers.
    fn close(&mut self, from_reg: u8) {
        self.open[from_reg as usize..].fill(None);
    }

    /// Merges a predecessor's exit state into this state.
    ///
    /// # Returns
    ///
    /// Returns registers whose predecessors have a conflict for whether
    /// this cell should be opened or closed.
    fn merge(&mut self, other: &Self) -> SmallVec<[u8; 4]> {
        let mut conflicts = SmallVec::new();
        for (reg, (this, other)) in self.open.iter_mut().zip(&other.open).enumerate() {
            if this != other {
                if this.is_some() || other.is_some() {
                    conflicts.push(reg as u8);
                }
                *this = None;
            }
        }
        conflicts
    }

    /// Merges the exit states of a block's predecessors into its entry state.
    ///
    /// # Returns
    ///
    /// Returns the merged state and the registers its predecessors disagree on.
    /// A block without predecessors starts with every register closed.
    fn merged<'a>(
        slots: u8,
        inputs: impl IntoIterator<Item = &'a Self>,
    ) -> (Self, SmallVec<[u8; 4]>) {
        let mut inputs = inputs.into_iter();
        let Some(first) = inputs.next() else {
            return (Self::new(slots), SmallVec::new());
        };

        let mut state = first.clone();
        let mut conflicts = SmallVec::new();
        for input in inputs {
            for reg in state.merge(input) {
                // This is quadratic in theory but probably small enough to not cause issues.
                // If it does, see RegSet.
                if !conflicts.contains(&reg) {
                    conflicts.push(reg);
                }
            }
        }
        (state, conflicts)
    }

    /// Applies one block's captures, closes, and hoisted cells to this state.
    ///
    /// Calls `on_open` with each site that opens a cell and its register.
    fn apply_block(
        &mut self,
        block: usize,
        raw: &RawBlock<'_>,
        hoists: &[u8],
        mut on_open: impl FnMut(OpenSite, u8),
    ) {
        for (instr, decoded) in raw.instrs.iter().enumerate() {
            match decoded.instr {
                il::Instr::Capture {
                    capture_type: CAPTURE_REF,
                    reg,
                } => {
                    let site = OpenSite::Capture { block, instr };
                    if self.open_at(reg, site) {
                        on_open(site, reg);
                    }
                }
                il::Instr::CloseUpvals { reg } => self.close(reg),
                _ => {}
            }
        }
        for &reg in hoists {
            let site = OpenSite::Hoisted { block, reg };
            if self.open_at(reg, site) {
                on_open(site, reg);
            }
        }
    }
}

/// Function-wide facts about reference-captured registers.
struct FunctionCaptures {
    /// Cell for each site that opens one.
    register_cells: HashMap<OpenSite, CellId>,
    /// Capture state at each raw block entry.
    block_states: Box<[CaptureState]>,
    /// Registers forced open at the end of each raw block.
    block_hoists: Box<[SmallVec<[u8; 4]>]>,
}

impl FunctionCaptures {
    /// Finds which cell backs each captured register at every block entry.
    ///
    /// Capture states flow along control-flow edges. When predecessors of a join disagree
    /// about a register's cell, the cell is hoisted to the end of the join's immediate
    /// dominator so that every path into the join shares it, and the analysis reruns.
    fn analyze(
        slots: u8,
        cfg: &ControlFlowGraph<RawBlock<'_>>,
        cells: &mut Arena<Cell>,
    ) -> Result<Self> {
        let idoms = cfg.build_idoms();
        let mut block_hoists = vec![SmallVec::new(); cfg.len()].into_boxed_slice();
        let mut hoisted = HashSet::default();

        loop {
            let (block_states, conflicts, sites) = Self::propagate(slots, cfg, &block_hoists);
            if conflicts.is_empty() {
                // Allocation does not make a cell active. Opening sites activate it while lifting.
                let register_cells = sites
                    .into_iter()
                    .map(|(site, reg)| {
                        let cell = cells.alloc(Cell {
                            origin: CellOrigin::CapturedRegister { reg },
                        });
                        (site, cell)
                    })
                    .collect();

                return Ok(Self {
                    register_cells,
                    block_states,
                    block_hoists,
                });
            }

            for (join, reg) in conflicts {
                ensure!(
                    hoisted.insert((join, reg)),
                    "captured R{reg} still disagrees at bb{join} after hoisting its cell"
                );
                let dominator = idoms
                    .idom(join)
                    .with_context(|| format!("captured R{reg} disagrees at entry bb{join}"))?;
                block_hoists[dominator].push(reg);
            }
        }
    }

    /// Runs the capture dataflow to a fixed point for one set of hoisted cells.
    ///
    /// Returns the entry state of each block, every `(join, reg)` whose predecessors
    /// disagree, and each opening site with its register in reverse post order.
    #[allow(clippy::type_complexity)]
    fn propagate(
        slots: u8,
        cfg: &ControlFlowGraph<RawBlock<'_>>,
        block_hoists: &[SmallVec<[u8; 4]>],
    ) -> (Box<[CaptureState]>, Vec<(usize, u8)>, Vec<(OpenSite, u8)>) {
        let order: Vec<_> = cfg.reverse_post_order().collect();
        let mut exits: Vec<Option<CaptureState>> = vec![None; cfg.len()];
        let mut entries = vec![CaptureState::new(slots); cfg.len()].into_boxed_slice();

        // Predecessors that have not been visited yet are skipped.
        let entry_state = |block: usize, exits: &[Option<CaptureState>]| {
            CaptureState::merged(
                slots,
                cfg.predecessors(block)
                    .filter_map(|predecessor| exits[predecessor].as_ref()),
            )
        };

        // Merging only ever closes registers, so this terminates.
        let mut changed = true;
        while changed {
            changed = false;
            for &block in &order {
                let (entry, _) = entry_state(block, &exits);
                let mut exit = entry.clone();
                exit.apply_block(block, &cfg[block], &block_hoists[block], |_, _| {});
                entries[block] = entry;
                if exits[block].as_ref() != Some(&exit) {
                    exits[block] = Some(exit);
                    changed = true;
                }
            }
        }

        let mut conflicts = Vec::new();
        let mut sites = Vec::new();
        for &block in &order {
            let (mut state, block_conflicts) = entry_state(block, &exits);
            conflicts.extend(block_conflicts.into_iter().map(|reg| (block, reg)));
            state.apply_block(block, &cfg[block], &block_hoists[block], |site, reg| {
                sites.push((site, reg));
            });
        }

        (entries, conflicts, sites)
    }

    /// Returns the cell opened at one site.
    fn cell(&self, site: OpenSite) -> Option<CellId> {
        self.register_cells.get(&site).copied()
    }
}

/// Mutable state for lifting one function directly into flat IR.
struct FunctionLifter<'c> {
    /// Proto currently being lifted.
    proto: &'c Proto,
    /// Chunk that owns constants and child protos.
    chunk: &'c Chunk,
    /// A control flow graph over the raw blocks.
    graph: ControlFlowGraph<RawBlock<'c>>,
    /// Mutable cells owned by the function.
    cells: Arena<Cell>,
    /// Cell for each declared upvalue.
    upvalues: Vec<CellId>,
    /// Function-wide reference capture facts.
    captures: FunctionCaptures,
}

impl<'c> FunctionLifter<'c> {
    /// Creates lifting state for one already analyzed raw function.
    fn new(
        proto: &'c Proto,
        chunk: &'c Chunk,
        graph: ControlFlowGraph<RawBlock<'c>>,
    ) -> Result<Self> {
        let mut cells = Arena::new();
        let upvalues = (0..proto.num_upvals)
            .map(|index| {
                cells.alloc(Cell {
                    origin: CellOrigin::Upvalue(index),
                })
            })
            .collect();
        let captures = FunctionCaptures::analyze(proto.max_stack_size, &graph, &mut cells)?;

        Ok(Self {
            proto,
            chunk,
            graph,
            cells,
            upvalues,
            captures,
        })
    }

    /// Lifts blocks, seals SSA, resolves aliases, and verifies the function.
    fn lift(self, type_info: ProtoTypeInfo) -> Result<Function> {
        let mut ssa = Ssa::new(&self.graph, self.proto.max_stack_size);
        let mut packs = Arena::new();
        let mut bindings = vec![DebugBinding::default(); self.proto.locals.len()];
        let mut close_loads = Vec::new();

        let mut params: Vec<_> = (0..self.proto.num_params)
            .map(|reg| {
                let value = ssa.alloc();
                ssa.write_entry(reg, value);
                if let Some(index) = self.proto.local_index_at(reg, 0) {
                    bindings[index].values.push(value);
                }
                value
            })
            .collect();

        let mut blocks = vec![None; self.graph.len()];
        for block_index in self.graph.reverse_post_order() {
            blocks[block_index] = Some(self.lift_block(
                block_index,
                &mut ssa,
                &mut packs,
                &mut bindings,
                &mut close_loads,
            )?);
        }

        for (block_index, block) in blocks.iter().enumerate() {
            if block.is_none() {
                anyhow::bail!("reachable bb{block_index} was not lifted");
            }
        }

        let mut cfg = ControlFlowGraph::from_nodes_and_exits(blocks.into_iter().map(|block| {
            let block = block.expect("validated above");
            let targets = block.exit.targets();
            (block, targets)
        }));

        let (values, aliases, entry) = ssa.finish(&mut cfg);

        let read = resolve_aliases(&mut cfg, &values, &aliases);
        for p in &mut params {
            *p = resolve_alias(*p, &aliases)
        }

        // Closing a cell loads its value back into the register, which is dead
        // when the register is never read again, as at the end of a scope.
        let mut dead_loads = ArenaSet::new(&values);
        dead_loads.extend(
            close_loads
                .iter()
                .map(|value| resolve_alias(*value, &aliases))
                .filter(|value| !read.contains(*value)),
        );
        for block in cfg.items_mut() {
            block.instrs.retain(|instr| {
                !matches!(instr, ir::Instr::LoadCell { out, .. } if dead_loads.contains(*out))
            });
        }

        cfg = fold_select_diamonds(cfg);

        for binding in &mut bindings {
            for value in &mut binding.values {
                *value = resolve_alias(*value, &aliases);
            }
            binding.values.retain(|value| !dead_loads.contains(*value));
            binding.values.sort_unstable_by_key(|value| value.index());
            binding.values.dedup();
            binding.cells.sort_unstable_by_key(|cell| cell.index());
            binding.cells.dedup();
        }

        let function = Function {
            id: self.proto.id,
            debug: resolve_debug(self.proto, self.chunk)?,
            type_info,
            bindings,
            params,
            entry,
            is_vararg: self.proto.is_vararg,
            upvalues: self.upvalues,
            values,
            packs,
            cells: self.cells,
            cfg,
        };

        #[cfg(debug_assertions)]
        function.verify()?;

        Ok(function)
    }

    /// Lifts one complete bytecode block.
    fn lift_block<'l, 'g>(
        &'l self,
        block: usize,
        ssa: &'l mut Ssa<'g, ControlFlowGraph<RawBlock<'c>>>,
        packs: &'l mut Arena<Pack>,
        bindings: &'l mut [DebugBinding],
        close_loads: &'l mut Vec<ValueId>,
    ) -> Result<Block> {
        BlockLifter::new(self, ssa, packs, bindings, close_loads, block)?.lift()
    }
}

/// Mutable state for lifting one complete basic block.
struct BlockLifter<'l, 'c, 'g> {
    /// Function-wide lifting state.
    function: &'l FunctionLifter<'c>,
    /// Function SSA state.
    ssa: &'l mut Ssa<'g, ControlFlowGraph<RawBlock<'c>>>,
    /// Function pack arena.
    packs: &'l mut Arena<Pack>,
    /// FIR identities associated with source debug locals.
    bindings: &'l mut [DebugBinding],
    /// Values loaded back into registers when their cells are closed.
    close_loads: &'l mut Vec<ValueId>,

    /// Block currently being lifted.
    block: usize,
    /// Current instruction cursor relative to [`instr_range`].
    cursor: usize,

    /// Flat instructions emitted for this block.
    emitted: Vec<ir::Instr>,
    /// Pack available to an immediate variadic consumer.
    pending: Option<PendingValues>,
    /// Register values projected only when they are read.
    deferred: Box<[Option<DeferredValue>]>,
    /// Capture state at the current instruction.
    capture_state: CaptureState,
}

impl<'l, 'c, 'g> BlockLifter<'l, 'c, 'g> {
    /// Creates a lifter for one raw bytecode block.
    fn new(
        function: &'l FunctionLifter<'c>,
        ssa: &'l mut Ssa<'g, ControlFlowGraph<RawBlock<'c>>>,
        packs: &'l mut Arena<Pack>,
        bindings: &'l mut [DebugBinding],
        close_loads: &'l mut Vec<ValueId>,
        block: usize,
    ) -> Result<Self> {
        let capture_state = function.captures.block_states[block].clone();
        Ok(Self {
            function,
            ssa,
            packs,
            bindings,
            close_loads,
            block,
            cursor: 0,
            emitted: Vec::new(),
            pending: None,
            deferred: vec![None; function.proto.max_stack_size as usize].into_boxed_slice(),
            capture_state,
        })
    }

    /// Lifts the block body and its exit.
    fn lift(mut self) -> Result<Block> {
        while let Some(instr) = self.next() {
            self.flush_pending_before(instr)?;
            self.lift_instr(instr)?;
        }

        // Cells shared by paths that join later are opened before the block's exit.
        for &reg in &self.function.captures.block_hoists[self.block] {
            self.open_cell_at(
                reg,
                OpenSite::Hoisted {
                    block: self.block,
                    reg,
                },
            )?;
        }

        self.ssa.mark_filled(self.block);

        let (exit, outputs) = self.lift_exit()?;

        Ok(Block {
            // Block params will be filled by ssa.finish()
            params: Vec::new(),
            outputs,
            instrs: self.emitted,
            exit,
        })
    }

    /// Returns the instructions for the current block.
    fn instrs(&self) -> &[DecodedInstr] {
        &self.function.graph[self.block].instrs
    }

    /// Returns the instruction at a given position.
    fn instr_at(&self, pos: usize) -> Option<DecodedInstr> {
        self.instrs().get(pos).copied()
    }

    /// Returns the next bytecode instruction and advances the cursor.
    fn next(&mut self) -> Option<il::Instr> {
        let instr = self.instr_at(self.cursor)?.instr;
        self.cursor += 1;
        Some(instr)
    }

    /// Returns the next bytecode instruction without advancing the cursor.
    fn peek(&self) -> Option<il::Instr> {
        Some(self.instr_at(self.cursor)?.instr)
    }

    /// Returns the current bytecode program counter.
    fn current_pc(&self) -> Option<u32> {
        Some(self.instr_at(self.cursor.saturating_sub(1))?.word_pc)
    }

    /// Allocates a immutable value identity.
    #[must_use]
    fn value(&mut self) -> ValueId {
        self.ssa.alloc()
    }

    /// Allocates a value pack identity.
    #[must_use]
    fn pack(&mut self) -> PackId {
        self.packs.alloc(Pack)
    }

    /// Emits a fixed value pack.
    #[must_use]
    fn fixed_pack(&mut self, head: Vec<ValueId>) -> PackId {
        let out = self.pack();
        self.emitted.push(ir::Instr::MakePack {
            out,
            head,
            tail: None,
        });
        out
    }

    /// Emits a pack with a fixed prefix and open tail.
    #[must_use]
    fn open_pack(&mut self, head: Vec<ValueId>, tail: PackId) -> PackId {
        let out = self.pack();
        self.emitted.push(ir::Instr::MakePack {
            out,
            head,
            tail: Some(tail),
        });
        out
    }

    /// Returns the active cell for a captured register.
    fn open_cell(&self, reg: u8) -> Option<CellId> {
        let site = self.capture_state.open_site(reg)?;
        self.function.captures.cell(site)
    }

    /// Projects a deferred register into its current storage.
    fn materialize_deferred(&mut self, reg: u8) -> Option<ValueId> {
        let deferred = self.deferred[reg as usize].take()?;
        let out = self.value();
        self.emitted.push(ir::Instr::Project {
            out,
            pack: deferred.pack,
            index: deferred.index,
        });
        self.write_reg(reg, out);
        Some(out)
    }

    /// Records all register values represented by an open pack.
    fn defer_pack(&mut self, base: u8, pack: PackId) {
        for reg in base..self.function.proto.max_stack_size {
            self.deferred[reg as usize] = Some(DeferredValue {
                pack,
                index: (reg - base) as usize,
            });
            if self.open_cell(reg).is_some() {
                self.materialize_deferred(reg);
            }
        }
    }

    /// Associates a read value with the declaration active at this instruction.
    fn record_debug_read(&mut self, reg: u8, value: ValueId) {
        if let Some(pc) = self.current_pc()
            && let Some(index) = self.function.proto.local_index_at(reg, pc)
        {
            self.bindings[index].values.push(value);
        }
    }

    /// Associates a written value with the declaration visible after this instruction.
    fn record_debug_write(&mut self, reg: u8, value: ValueId) {
        if let Some(pc) = self.current_pc()
            && let Some(index) = self.function.proto.local_index_after(reg, pc)
        {
            self.bindings[index].values.push(value);
        }
    }

    /// Associates a read cell with the declaration active at this instruction.
    fn record_debug_cell_read(&mut self, reg: u8, cell: CellId) {
        if let Some(pc) = self.current_pc()
            && let Some(index) = self.function.proto.local_index_at(reg, pc)
        {
            self.bindings[index].cells.push(cell);
        }
    }

    /// Associates a written cell with the declaration visible after this instruction.
    fn record_debug_cell_write(&mut self, reg: u8, cell: CellId) {
        if let Some(pc) = self.current_pc()
            && let Some(index) = self.function.proto.local_index_after(reg, pc)
        {
            self.bindings[index].cells.push(cell);
        }
    }

    /// Reads a register and emits a cell load when its storage is captured.
    fn read_reg(&mut self, reg: u8) -> ValueId {
        if let Some(value) = self.materialize_deferred(reg) {
            self.record_debug_read(reg, value);
            return value;
        }

        let value = match self.open_cell(reg) {
            Some(cell) => {
                self.record_debug_cell_read(reg, cell);
                let out = self.value();
                self.emitted.push(ir::Instr::LoadCell { out, cell });
                out
            }
            None => self.ssa.read_reg(self.block, reg),
        };
        self.record_debug_read(reg, value);
        value
    }

    /// Reads a register version from another block.
    fn read_reg_in(&mut self, block: usize, reg: u8) -> ValueId {
        let value = self.ssa.read_reg(block, reg);
        self.record_debug_read(reg, value);
        value
    }

    /// Reads a fixed register range in order.
    #[must_use]
    fn read_regs(&mut self, start: u8, count: u8) -> Vec<ValueId> {
        reg_range(start, count)
            .map(|reg| self.read_reg(reg))
            .collect()
    }

    /// Defines a register from an already emitted immutable value.
    fn write_reg(&mut self, reg: u8, value: ValueId) {
        self.deferred[reg as usize] = None;
        self.record_debug_write(reg, value);
        match self.open_cell(reg) {
            Some(cell) => {
                self.record_debug_cell_write(reg, cell);
                self.emitted.push(ir::Instr::StoreCell { cell, value });
            }
            None => self.ssa.write_reg(self.block, reg, value),
        }
    }

    /// Defines a register with a fresh copy identity.
    fn copy_reg(&mut self, reg: u8, value: ValueId) {
        let out = self.value();
        self.emitted.push(ir::Instr::Copy { out, value });
        self.write_reg(reg, out);
    }

    /// Projects fixed results from a pack into consecutive registers.
    fn write_pack(&mut self, start: u8, count: u8, pack: PackId) {
        for (index, reg) in reg_range(start, count).enumerate() {
            let out = self.value();
            self.emitted.push(ir::Instr::Project { out, pack, index });
            self.write_reg(reg, out);
        }
    }

    /// Emits one literal constant.
    #[must_use]
    fn constant(&mut self, value: ir::Constant) -> ValueId {
        let out = self.value();
        self.emitted.push(ir::Instr::Const { out, value });
        out
    }

    /// Emits a global read.
    #[must_use]
    fn global(&mut self, name: SmolStr) -> ValueId {
        let out = self.value();
        self.emitted.push(ir::Instr::GetGlobal { out, name });
        out
    }

    /// Emits a binary operation.
    #[must_use]
    fn binary(&mut self, lhs: ValueId, op: BinOp, rhs: ValueId) -> ValueId {
        let out = self.value();
        self.emitted.push(ir::Instr::Binary { out, lhs, op, rhs });
        out
    }

    /// Emits a string-keyed table read without changing the key bytes.
    #[must_use]
    fn string_access(&mut self, table: ValueId, key: ByteString) -> ValueId {
        let key = self.constant(ir::Constant::String(key));
        let out = self.value();
        self.emitted.push(ir::Instr::GetTable { out, table, key });
        out
    }

    /// Emits a string-keyed table write without changing the key bytes.
    fn string_store(&mut self, table: ValueId, key: ByteString, value: ValueId) {
        let key = self.constant(ir::Constant::String(key));
        self.emitted.push(ir::Instr::SetTable { table, key, value });
    }

    /// Returns the [`OpenSite`] for the instruction that was just consumed.
    fn capture_site(&self) -> OpenSite {
        OpenSite::Capture {
            block: self.block,
            instr: self.cursor - 1,
        }
    }

    /// Marks one register's cell open at a site without initializing it.
    fn activate_cell(&mut self, reg: u8, site: OpenSite) -> Result<CellId> {
        let cell = self
            .function
            .captures
            .cell(site)
            .with_context(|| format!("R{reg} has no cell opened at {site:?}"))?;
        self.capture_state.open_at(reg, site);
        Ok(cell)
    }

    /// Opens one captured register at a site and returns its cell.
    fn open_cell_at(&mut self, reg: u8, site: OpenSite) -> Result<CellId> {
        if let Some(cell) = self.open_cell(reg) {
            return Ok(cell);
        }

        let value = self.read_reg(reg);
        let cell = self.activate_cell(reg, site)?;
        self.record_debug_cell_read(reg, cell);
        self.emitted.push(ir::Instr::OpenCell { cell, value });
        Ok(cell)
    }

    /// Closes captured cells and moves their values back into registers.
    fn close_cells(&mut self, from_reg: u8) -> Result<()> {
        for reg in from_reg..self.function.proto.max_stack_size {
            let Some(cell) = self.open_cell(reg) else {
                continue;
            };
            self.materialize_deferred(reg);
            let value = self.value();
            self.emitted.push(ir::Instr::LoadCell { out: value, cell });
            self.close_loads.push(value);
            self.record_debug_cell_read(reg, cell);
            self.record_debug_read(reg, value);
            self.ssa.write_reg(self.block, reg, value);
        }

        self.capture_state.close(from_reg);
        Ok(())
    }

    /// Marks an open pack as unavailable to later variadic consumers.
    fn flush_pending(&mut self) {
        self.pending = None;
    }

    /// Flushes deferred values unless this instruction preserves or consumes them.
    fn flush_pending_before(&mut self, instr: il::Instr) -> Result<()> {
        let Some(pending) = self.pending else {
            return Ok(());
        };

        let base = pending.base();
        let consumed = match instr {
            il::Instr::Call {
                func, arg_count, ..
            } if Count::from(arg_count).is_variadic() => base >= reg_add(func, 1),
            il::Instr::SetList {
                base: values,
                count,
                ..
            } if Count::from(count).is_variadic() => base >= values,
            il::Instr::NameCall { .. } | il::Instr::NameCallUData { .. } => match self.peek() {
                Some(il::Instr::Call {
                    func, arg_count, ..
                }) if Count::from(arg_count).is_variadic() && base >= reg_add(func, 2) => true,
                _ => bail!(
                    "malformed bytecode: NAMECALL at {:?} is not followed by CALL",
                    self.current_pc()
                ),
            },
            _ => false,
        };

        let preserves = match instr {
            il::Instr::FastCall1 { .. }
            | il::Instr::FastCall2 { .. }
            | il::Instr::FastCall2K { .. }
            | il::Instr::FastCall3 { .. }
            | il::Instr::FastCall { .. }
            | il::Instr::CloseUpvals { .. } => true,
            il::Instr::GetImport { dest, .. }
            | il::Instr::GetGlobal { dest, .. }
            | il::Instr::GetUpval { dest, .. }
            | il::Instr::Move { dest, .. } => dest < base,
            _ => false,
        };

        if !consumed && !preserves {
            self.flush_pending();
        }

        Ok(())
    }

    /// Takes a pending open pack and prefixes earlier fixed registers.
    fn take_variadic_from(&mut self, first: u8) -> Result<PackId> {
        let pending = self
            .pending
            .take()
            .context("variadic consumer without open values")?;
        ensure!(
            pending.base() >= first,
            "open values start before variadic consumer base"
        );

        let head = self.read_regs(first, pending.base() - first);
        Ok(if head.is_empty() {
            pending.pack()
        } else {
            self.open_pack(head, pending.pack())
        })
    }

    /// Resolves one byte-string constant.
    fn const_string(&self, id: ConstId) -> Result<ByteString> {
        let constant = self
            .function
            .proto
            .get_constant(id)
            .with_context(|| format!("missing constant at {id:?}"))?;
        let il::Constant::String(string) = constant else {
            bail!("expected string constant at {id:?}, got {constant:?}");
        };
        self.function
            .chunk
            .get_string(*string)
            .with_context(|| format!("invalid string id {string:?}"))
    }

    /// Resolves one UTF-8 name constant.
    fn const_name(&self, id: ConstId) -> Result<SmolStr> {
        let string = self.const_string(id)?;
        string
            .as_utf8()
            .map(ToSmolStr::to_smolstr)
            .with_context(|| format!("string constant {id:?} is not valid UTF-8"))
    }

    /// Emits a numeric constant required by an arithmetic opcode.
    fn emit_const_number(&mut self, id: ConstId) -> Result<ValueId> {
        let value = match self.function.proto.get_constant(id) {
            Some(il::Constant::Number(value)) => *value,
            _ => bail!("arithmetic constant {id:?} is not a number"),
        };
        Ok(self.constant(ir::Constant::Number(Number::Float(value))))
    }

    /// Emits one proto constant and all instructions needed to construct it.
    fn emit_constant(&mut self, id: ConstId) -> Result<ValueId> {
        let constant = self
            .function
            .proto
            .get_constant(id)
            .with_context(|| format!("missing constant at {id:?}"))?;

        Ok(match constant {
            il::Constant::Nil => self.constant(ir::Constant::Nil),
            il::Constant::Boolean(value) => self.constant(ir::Constant::Bool(*value)),
            il::Constant::Number(value) => {
                self.constant(ir::Constant::Number(Number::Float(*value)))
            }
            il::Constant::Integer(value) => {
                self.constant(ir::Constant::Number(Number::Integer(*value)))
            }
            il::Constant::String(string) => {
                let value = self
                    .function
                    .chunk
                    .get_string(*string)
                    .with_context(|| format!("invalid string id {string:?}"))?;
                self.constant(ir::Constant::String(value))
            }
            il::Constant::Import(path) => self.emit_import(*path)?,
            il::Constant::Table => {
                let out = self.value();
                self.emitted.push(ir::Instr::NewTable { out });
                out
            }
            il::Constant::TableWithConstants(entries) => {
                let table = self.value();
                self.emitted.push(ir::Instr::NewTable { out: table });
                for (key, value) in entries {
                    let Some(value) = value else {
                        continue;
                    };
                    let key = self.emit_constant(*key)?;
                    let value = self.emit_constant(*value)?;
                    self.emitted.push(ir::Instr::SetTable { table, key, value });
                }
                table
            }
            il::Constant::Vector { x, y, z, w } => {
                let vector = self.global("vector".into());
                let key = self.constant(ir::Constant::String(ByteString::from("create")));
                let function = self.value();
                self.emitted.push(ir::Instr::GetTable {
                    out: function,
                    table: vector,
                    key,
                });

                let args = [x, y, z, w]
                    .into_iter()
                    .map(|value| self.constant(ir::Constant::Number(Number::Float(*value as f64))))
                    .collect();
                let args = self.fixed_pack(args);
                let results = self.pack();
                self.emitted.push(ir::Instr::Call {
                    out: results,
                    function,
                    args,
                });

                let out = self.value();
                self.emitted.push(ir::Instr::Project {
                    out,
                    pack: results,
                    index: 0,
                });
                out
            }
            il::Constant::Closure(_) => bail!("closure constant requires DUPCLOSURE"),
        })
    }

    /// Emits a packed import path as a global followed by table reads.
    fn emit_import(&mut self, path: ImportPath) -> Result<ValueId> {
        let mut names = Vec::new();
        for id in path.const_ids()? {
            let Some(il::Constant::String(string)) = self.function.proto.get_constant(id) else {
                bail!("import path component {id:?} is not a string constant");
            };
            let name = self
                .function
                .chunk
                .get_string(*string)
                .with_context(|| format!("invalid import string id {string:?}"))?;
            names.push(name);
        }

        let mut names = names.into_iter();
        let first = names.next().context("import path is empty")?;
        let first = first
            .as_utf8()
            .context("first import path component is not valid UTF-8")?
            .to_smolstr();

        let mut value = self.global(first);
        for field in names {
            value = self.string_access(value, field);
        }
        Ok(value)
    }

    /// Emits one ordinary call instruction.
    fn lift_call(&mut self, function_reg: u8, arg_count: u8, result_count: u8) -> Result<()> {
        let first_arg = reg_add(function_reg, 1);
        let args = match Count::from(arg_count) {
            Count::Number(count) => {
                let values = self.read_regs(first_arg, count);
                self.fixed_pack(values)
            }
            Count::Variadic => self.take_variadic_from(first_arg)?,
        };

        let function = self.read_reg(function_reg);
        let results = self.pack();
        self.emitted.push(ir::Instr::Call {
            out: results,
            function,
            args,
        });

        self.handle_call_results(function_reg, result_count, results)
    }

    /// Emits a method call and consumes its following CALL instruction.
    fn lift_namecall(&mut self, dest: u8, object: u8, method: u32) -> Result<()> {
        let namecall_pc = self.current_pc();
        let Some(il::Instr::Call {
            func,
            arg_count,
            ret_count,
        }) = self.next()
        else {
            bail!(
                "malformed bytecode: NAMECALL at {:?} is not followed by CALL",
                namecall_pc
            );
        };

        ensure!(
            func == dest,
            "NAMECALL destination does not match CALL function"
        );

        let first_arg = reg_add(func, 2);
        let args = match Count::from(arg_count) {
            Count::Number(count) if count > 1 => {
                let values = self.read_regs(first_arg, count - 1);
                self.fixed_pack(values)
            }
            Count::Variadic => self.take_variadic_from(first_arg)?,
            Count::Number(_) => self.fixed_pack(Vec::new()),
        };

        let object = self.read_reg(object);
        let method = self.const_name(ConstId(method))?;
        let results = self.pack();
        self.emitted.push(ir::Instr::MethodCall {
            out: results,
            object,
            method,
            args,
        });

        self.handle_call_results(func, ret_count, results)
    }

    /// Writes fixed call results or records open call results.
    fn handle_call_results(&mut self, dest: u8, count: u8, pack: PackId) -> Result<()> {
        match Count::from(count) {
            Count::Number(count) => self.write_pack(dest, count, pack),
            Count::Variadic => {
                ensure!(
                    self.pending.is_none(),
                    "call overwrites pending open values"
                );
                self.defer_pack(dest, pack);
                self.pending = Some(PendingValues::Call { base: dest, pack });
            }
        }
        Ok(())
    }

    /// Emits one closure and consumes its capture instructions.
    fn lift_closure(&mut self, dest: u8, proto: ProtoId) -> Result<()> {
        let capture_count = self
            .function
            .chunk
            .get_proto(proto)
            .with_context(|| format!("missing child proto {proto:?}"))?
            .num_upvals;

        let out = self.value();
        let (captures, recursive_cell) = self.consume_captures(capture_count, dest, out)?;
        self.emitted.push(ir::Instr::Closure {
            out,
            proto,
            captures,
        });
        if let Some(cell) = recursive_cell {
            self.deferred[dest as usize] = None;
            self.emitted.push(ir::Instr::OpenCell { cell, value: out });
        } else {
            self.write_reg(dest, out);
        }

        Ok(())
    }

    /// Consumes the CAPTURE instructions following a closure opcode.
    fn consume_captures(
        &mut self,
        count: u8,
        closure_reg: u8,
        closure: ValueId,
    ) -> Result<(Vec<Capture>, Option<CellId>)> {
        let mut captures = Vec::with_capacity(count as usize);
        let mut recursive_cell = None;
        for capture_index in 0..count {
            let Some(il::Instr::Capture { capture_type, reg }) = self.next() else {
                bail!("malformed bytecode: missing CAPTURE #{capture_index}");
            };

            let capture = match capture_type {
                CAPTURE_VAL if reg == closure_reg => Capture::Copy(closure),
                CAPTURE_VAL => Capture::Copy(self.read_reg(reg)),
                CAPTURE_REF if reg == closure_reg && self.open_cell(reg).is_none() => {
                    let cell = self.activate_cell(reg, self.capture_site())?;
                    recursive_cell = Some(cell);
                    Capture::Share(cell)
                }
                CAPTURE_REF => Capture::Share(self.open_cell_at(reg, self.capture_site())?),
                CAPTURE_UPVAL => {
                    let cell = self
                        .function
                        .upvalues
                        .get(reg as usize)
                        .copied()
                        .with_context(|| format!("invalid captured upvalue {reg}"))?;
                    Capture::Share(cell)
                }
                _ => bail!("unknown capture type {capture_type}"),
            };
            captures.push(capture);
        }
        Ok((captures, recursive_cell))
    }

    /// Emits SETLIST with a fixed or open value pack.
    fn lift_setlist(&mut self, table: u8, base: u8, count: u8, index: u32) -> Result<()> {
        let values = match Count::from(count) {
            Count::Number(count) => {
                let values = self.read_regs(base, count);
                self.fixed_pack(values)
            }
            Count::Variadic => self.take_variadic_from(base)?,
        };

        let table = self.read_reg(table);
        self.emitted.push(ir::Instr::SetList {
            table,
            index,
            values,
        });

        Ok(())
    }

    /// Lifts one bytecode instruction into explicit flat instructions.
    fn lift_instr(&mut self, instr: il::Instr) -> Result<()> {
        match instr {
            il::Instr::Nop => {}
            il::Instr::LoadNil { reg } => {
                let value = self.constant(ir::Constant::Nil);
                self.write_reg(reg, value);
            }
            il::Instr::LoadB { reg, value, .. } => {
                let value = self.constant(ir::Constant::Bool(value));
                self.write_reg(reg, value);
            }
            il::Instr::LoadN { reg, value } => {
                let value = self.constant(ir::Constant::Number(Number::Float(value as f64)));
                self.write_reg(reg, value);
            }
            il::Instr::LoadK { reg, index } => {
                let value = self.emit_constant(ConstId(index as u32))?;
                self.write_reg(reg, value);
            }
            il::Instr::LoadKX { reg, index } => {
                let value = self.emit_constant(ConstId(index))?;
                self.write_reg(reg, value);
            }
            il::Instr::Move { dest, src } => {
                let value = self.read_reg(src);
                self.copy_reg(dest, value);
            }
            il::Instr::GetGlobal { dest, key, .. } => {
                let name = self.const_name(ConstId(key))?;
                let value = self.global(name);
                self.write_reg(dest, value);
            }
            il::Instr::SetGlobal { src, key, .. } => {
                let name = self.const_name(ConstId(key))?;
                let value = self.read_reg(src);
                self.emitted.push(ir::Instr::SetGlobal { name, value });
            }
            il::Instr::GetUpval { dest, upval } => {
                let cell = self
                    .function
                    .upvalues
                    .get(upval as usize)
                    .copied()
                    .with_context(|| format!("invalid upvalue {upval}"))?;
                let out = self.value();
                self.emitted.push(ir::Instr::LoadCell { out, cell });
                self.write_reg(dest, out);
            }
            il::Instr::SetUpval { src, upval } => {
                let cell = self
                    .function
                    .upvalues
                    .get(upval as usize)
                    .copied()
                    .with_context(|| format!("invalid upvalue {upval}"))?;
                let value = self.read_reg(src);
                self.emitted.push(ir::Instr::StoreCell { cell, value });
            }
            il::Instr::GetImport { dest, path, .. } => {
                let value = self.emit_import(ImportPath(path))?;
                self.write_reg(dest, value);
            }
            il::Instr::NameCall {
                dest,
                object,
                method,
                ..
            } => self.lift_namecall(dest, object, method)?,
            il::Instr::NameCallUData {
                dest,
                object,
                method,
                ..
            } => self.lift_namecall(dest, object, method as u32)?,
            il::Instr::Call {
                func,
                arg_count,
                ret_count,
            } => self.lift_call(func, arg_count, ret_count)?,
            il::Instr::GetTableKS {
                dest, table, key, ..
            } => {
                let table = self.read_reg(table);
                let key = self.const_string(ConstId(key))?;
                let value = self.string_access(table, key);
                self.write_reg(dest, value);
            }
            il::Instr::GetUDataKS {
                dest,
                userdata,
                key,
                ..
            } => {
                let table = self.read_reg(userdata);
                let key = self.const_string(ConstId(key as u32))?;
                let value = self.string_access(table, key);
                self.write_reg(dest, value);
            }
            il::Instr::GetTable { dest, table, key } => {
                let table = self.read_reg(table);
                let key = self.read_reg(key);
                let out = self.value();
                self.emitted.push(ir::Instr::GetTable { out, table, key });
                self.write_reg(dest, out);
            }
            il::Instr::GetTableN { dest, table, index } => {
                let table = self.read_reg(table);
                let key = self.constant(ir::Constant::Number(Number::Float(index as f64)));
                let out = self.value();
                self.emitted.push(ir::Instr::GetTable { out, table, key });
                self.write_reg(dest, out);
            }
            il::Instr::SetTableKS {
                src, table, key, ..
            } => {
                let table = self.read_reg(table);
                let value = self.read_reg(src);
                let key = self.const_string(ConstId(key))?;
                self.string_store(table, key, value);
            }
            il::Instr::SetUDataKS {
                src, userdata, key, ..
            } => {
                let table = self.read_reg(userdata);
                let value = self.read_reg(src);
                let key = self.const_string(ConstId(key as u32))?;
                self.string_store(table, key, value);
            }
            il::Instr::SetTableN { src, table, index } => {
                let table = self.read_reg(table);
                let value = self.read_reg(src);
                let key = self.constant(ir::Constant::Number(Number::Float(index as f64)));
                self.emitted.push(ir::Instr::SetTable { table, key, value });
            }
            il::Instr::SetTable { src, table, key } => {
                let table = self.read_reg(table);
                let key = self.read_reg(key);
                let value = self.read_reg(src);
                self.emitted.push(ir::Instr::SetTable { table, key, value });
            }
            il::Instr::Add { dest, a, b }
            | il::Instr::Sub { dest, a, b }
            | il::Instr::Mul { dest, a, b }
            | il::Instr::Div { dest, a, b }
            | il::Instr::IDiv { dest, a, b }
            | il::Instr::Mod { dest, a, b }
            | il::Instr::Pow { dest, a, b }
            | il::Instr::And { dest, a, b }
            | il::Instr::Or { dest, a, b } => {
                let lhs = self.read_reg(a);
                let rhs = self.read_reg(b);
                let value = self.binary(lhs, binop_for_instr(instr), rhs);
                self.write_reg(dest, value);
            }
            il::Instr::AddK { dest, reg, k }
            | il::Instr::SubK { dest, reg, k }
            | il::Instr::MulK { dest, reg, k }
            | il::Instr::DivK { dest, reg, k }
            | il::Instr::IDivK { dest, reg, k }
            | il::Instr::ModK { dest, reg, k }
            | il::Instr::PowK { dest, reg, k } => {
                let lhs = self.read_reg(reg);
                let rhs = self.emit_const_number(ConstId(k as u32))?;
                let value = self.binary(lhs, binop_for_instr(instr), rhs);
                self.write_reg(dest, value);
            }
            il::Instr::SubRK { dest, k, reg } | il::Instr::DivRK { dest, k, reg } => {
                let lhs = self.emit_const_number(ConstId(k as u32))?;
                let rhs = self.read_reg(reg);
                let value = self.binary(lhs, binop_for_instr(instr), rhs);
                self.write_reg(dest, value);
            }
            il::Instr::AndK { dest, reg, k } | il::Instr::OrK { dest, reg, k } => {
                let lhs = self.read_reg(reg);
                let rhs = self.emit_constant(ConstId(k as u32))?;
                let value = self.binary(lhs, binop_for_instr(instr), rhs);
                self.write_reg(dest, value);
            }
            il::Instr::Concat { dest, a, b } => {
                ensure!(a < b, "concat must have at least two operands");
                let operands = (a..=b).map(|reg| self.read_reg(reg)).collect();
                let out = self.value();
                self.emitted.push(ir::Instr::Concat { out, operands });
                self.write_reg(dest, out);
            }
            il::Instr::Not { dest, reg }
            | il::Instr::Minus { dest, reg }
            | il::Instr::Length { dest, reg } => {
                let value = self.read_reg(reg);
                let out = self.value();
                self.emitted.push(ir::Instr::Unary {
                    out,
                    op: unop_for_instr(instr),
                    value,
                });
                self.write_reg(dest, out);
            }
            il::Instr::NewTable { dest, .. } => {
                let out = self.value();
                self.emitted.push(ir::Instr::NewTable { out });
                self.write_reg(dest, out);
            }
            il::Instr::DupTable { dest, k } => {
                let value = self.emit_constant(ConstId(k as u32))?;
                self.write_reg(dest, value);
            }
            il::Instr::SetList {
                table,
                base,
                count,
                index,
            } => self.lift_setlist(table, base, count, index)?,
            il::Instr::NewClosure { dest, proto } => {
                let proto = self
                    .function
                    .proto
                    .get_child_proto(ChildProtoId(proto))
                    .with_context(|| format!("missing child proto {proto}"))?;
                self.lift_closure(dest, proto)?;
            }
            il::Instr::DupClosure { dest, k } => {
                let proto = match self.function.proto.get_constant(ConstId(k as u32)) {
                    Some(il::Constant::Closure(proto)) => *proto,
                    _ => bail!("DUPCLOSURE constant {k} is not a closure"),
                };
                self.lift_closure(dest, proto)?;
            }
            il::Instr::CloseUpvals { reg } => self.close_cells(reg)?,
            il::Instr::GetVarArgs { dest, count } => {
                let pack = self.pack();
                self.emitted.push(ir::Instr::VarArgs { out: pack });

                match Count::from(count) {
                    Count::Number(count) => self.write_pack(dest, count, pack),
                    Count::Variadic => {
                        ensure!(
                            self.pending.is_none(),
                            "varargs overwrite pending open values"
                        );
                        self.defer_pack(dest, pack);
                        self.pending = Some(PendingValues::VarArgs { base: dest, pack });
                    }
                }
            }
            il::Instr::FastCall1 { .. }
            | il::Instr::FastCall2 { .. }
            | il::Instr::FastCall2K { .. }
            | il::Instr::FastCall3 { .. }
            | il::Instr::FastCall { .. }
            | il::Instr::PrepVarArgs { .. }
            | il::Instr::Break
            | il::Instr::Jump { .. }
            | il::Instr::JumpBack { .. }
            | il::Instr::JumpIf { .. }
            | il::Instr::JumpIfNot { .. }
            | il::Instr::JumpX { .. }
            | il::Instr::JumpIfEq { .. }
            | il::Instr::JumpIfLe { .. }
            | il::Instr::JumpIfLt { .. }
            | il::Instr::JumpIfNotEq { .. }
            | il::Instr::JumpIfNotLe { .. }
            | il::Instr::JumpIfNotLt { .. }
            | il::Instr::JumpXEqKNil { .. }
            | il::Instr::JumpXEqKB { .. }
            | il::Instr::JumpXEqKN { .. }
            | il::Instr::JumpXEqKS { .. }
            | il::Instr::FornPrep { .. }
            | il::Instr::ForgPrep { .. }
            | il::Instr::ForgPrepInext { .. }
            | il::Instr::ForgPrepNext { .. }
            | il::Instr::FornLoop { .. }
            | il::Instr::ForgLoop { .. }
            | il::Instr::Coverage
            | il::Instr::NativeCall => { /* not relevant to the lifter */ }
            il::Instr::Return { .. } => {
                bail!("RETURN remained in the raw block body")
            }
            il::Instr::Capture { .. } => {
                bail!("CAPTURE was not consumed by closure lifting")
            }
        }
        Ok(())
    }

    /// Lifts a [`RawBlockExit`] to a [`BlockExit`] after its body has been lifted.
    ///
    /// Returns a tuple of the lifted [`BlockExit`] and a vector of output values.
    fn lift_exit(&mut self) -> Result<(BlockExit, Vec<ValueId>)> {
        let raw = &self.function.graph[self.block];
        let mut outputs = Vec::new();
        let exit = match &raw.exit {
            RawBlockExit::Jump(target) => {
                self.flush_pending();
                self.apply_exit_writes(raw, &mut outputs);
                BlockExit::Jump(Edge::empty(*target))
            }
            RawBlockExit::Fallthrough(target) => {
                self.flush_pending();
                self.apply_exit_writes(raw, &mut outputs);
                BlockExit::Fallthrough(Edge::empty(*target))
            }
            RawBlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } => {
                self.flush_pending();
                let condition = match cond {
                    Cond::Unary(reg) => self.read_reg(*reg),
                    Cond::Binary { lhs, op, rhs } => {
                        let lhs = self.read_reg(*lhs);
                        let rhs = match rhs {
                            CondRhs::Reg(reg) => self.read_reg(*reg),
                            CondRhs::Const(index) => self.emit_constant(ConstId(*index))?,
                            CondRhs::Nil => self.constant(ir::Constant::Nil),
                            CondRhs::Bool(value) => self.constant(ir::Constant::Bool(*value)),
                        };
                        self.binary(lhs, *op, rhs)
                    }
                };
                self.apply_exit_writes(raw, &mut outputs);
                BlockExit::Branch {
                    condition,
                    then_edge: Edge::empty(*then_block),
                    else_edge: Edge::empty(*else_block),
                }
            }
            RawBlockExit::FornPrep {
                base,
                body_block,
                exit_block,
            } => {
                self.flush_pending();
                let start = self.read_reg(reg_add(*base, 2));
                let end = self.read_reg(*base);
                let step = self.read_reg(reg_add(*base, 1));
                self.apply_exit_writes(raw, &mut outputs);
                let variable = self.read_reg_in(*body_block, reg_add(*base, 2));
                BlockExit::NumericFor {
                    body_edge: Edge::empty(*body_block),
                    exit_edge: Edge::empty(*exit_block),
                    variable,
                    start,
                    end,
                    step,
                }
            }
            RawBlockExit::FornLoop {
                body_block,
                exit_block,
                ..
            } => {
                self.flush_pending();
                self.apply_exit_writes(raw, &mut outputs);
                BlockExit::NumericForLoop {
                    body_edge: Edge::empty(*body_block),
                    exit_edge: Edge::empty(*exit_block),
                }
            }
            RawBlockExit::ForgPrep {
                base,
                body_block,
                exit_block,
            } => {
                self.flush_pending();
                let values = [
                    self.read_reg(*base),
                    self.read_reg(reg_add(*base, 1)),
                    self.read_reg(reg_add(*base, 2)),
                ];
                self.apply_exit_writes(raw, &mut outputs);
                let variables = raw
                    .exit_writes
                    .iter()
                    .map(|reg| self.read_reg_in(*body_block, *reg))
                    .collect();
                BlockExit::GenericFor {
                    body_edge: Edge::empty(*body_block),
                    loop_block: *exit_block,
                    variables,
                    values,
                }
            }
            RawBlockExit::ForgLoop {
                base,
                body_block,
                exit_block,
                result_count,
            } => {
                self.flush_pending();
                self.apply_exit_writes(raw, &mut outputs);
                let variables = (0..*result_count)
                    .map(|index| {
                        let reg = reg_add(reg_add(*base, 3), index as u8);
                        self.read_reg_in(*body_block, reg)
                    })
                    .collect();
                BlockExit::GenericForLoop {
                    body_edge: Edge::empty(*body_block),
                    exit_edge: Edge::empty(*exit_block),
                    variables,
                }
            }
            RawBlockExit::Return { base, count } => match Count::from(*count) {
                Count::Number(count) => {
                    self.flush_pending();
                    let values = self.read_regs(*base, count);
                    BlockExit::Return(self.fixed_pack(values))
                }
                Count::Variadic => {
                    let pack = self.take_variadic_from(*base)?;
                    BlockExit::Return(pack)
                }
            },
        };
        Ok((exit, outputs))
    }

    /// Applies register definitions produced by a bytecode block exit.
    fn apply_exit_writes(&mut self, raw: &RawBlock, outputs: &mut Vec<ValueId>) {
        for &reg in &raw.exit_writes {
            let value = self.value();
            self.write_reg(reg, value);
            outputs.push(value);
        }
    }
}

/// Returns the binary operator encoded by an arithmetic instruction.
const fn binop_for_instr(instr: il::Instr) -> BinOp {
    match instr {
        il::Instr::Add { .. } | il::Instr::AddK { .. } => BinOp::Add,
        il::Instr::Sub { .. } | il::Instr::SubK { .. } | il::Instr::SubRK { .. } => BinOp::Sub,
        il::Instr::Mul { .. } | il::Instr::MulK { .. } => BinOp::Mul,
        il::Instr::Div { .. } | il::Instr::DivK { .. } | il::Instr::DivRK { .. } => BinOp::Div,
        il::Instr::IDiv { .. } | il::Instr::IDivK { .. } => BinOp::IDiv,
        il::Instr::Mod { .. } | il::Instr::ModK { .. } => BinOp::Mod,
        il::Instr::Pow { .. } | il::Instr::PowK { .. } => BinOp::Pow,
        il::Instr::And { .. } | il::Instr::AndK { .. } => BinOp::And,
        il::Instr::Or { .. } | il::Instr::OrK { .. } => BinOp::Or,
        _ => panic!("instruction is not a binary operator"),
    }
}

/// Returns the unary operator encoded by an instruction.
const fn unop_for_instr(instr: il::Instr) -> UnOp {
    match instr {
        il::Instr::Not { .. } => UnOp::Not,
        il::Instr::Minus { .. } => UnOp::Minus,
        il::Instr::Length { .. } => UnOp::Length,
        _ => panic!("instruction is not a unary operator"),
    }
}

/// Resolves one value through the trivial-Phi alias map.
fn resolve_alias(mut value: ValueId, aliases: &IndexMap<ValueId, ValueId>) -> ValueId {
    while let Some(&alias) = aliases.get(value) {
        value = alias;
    }
    value
}

/// Rewrites all block references to surviving SSA values.
///
/// Returns every value read by an instruction, a block exit, or an edge.
fn resolve_aliases(
    cfg: &mut ControlFlowGraph<Block>,
    values: &Arena<Value>,
    aliases: &IndexMap<ValueId, ValueId>,
) -> ArenaSet<Value> {
    let mut read = ArenaSet::new(values);
    for block in cfg.items_mut() {
        for output in &mut block.outputs {
            *output = resolve_alias(*output, aliases);
        }
        block.outputs.sort_unstable();
        block.outputs.dedup();
        for instr in &mut block.instrs {
            resolve_instr(instr, aliases);
            read.extend(instr.used_values());
        }
        resolve_exit(&mut block.exit, aliases);
        read.extend(block.exit.used_values());
        for edge in block.exit.edges() {
            read.extend(edge.params.iter().copied());
        }
    }
    read
}

/// Rewrites value references in an IR instruction.
fn resolve_instr(instr: &mut ir::Instr, aliases: &IndexMap<ValueId, ValueId>) {
    let resolve = |value: &mut ValueId| *value = resolve_alias(*value, aliases);
    match instr {
        ir::Instr::Const { out, .. }
        | ir::Instr::GetGlobal { out, .. }
        | ir::Instr::NewTable { out } => resolve(out),
        ir::Instr::VarArgs { .. } => {}
        ir::Instr::Copy { out, value } | ir::Instr::Unary { out, value, .. } => {
            resolve(out);
            resolve(value);
        }
        ir::Instr::Closure { out, captures, .. } => {
            resolve(out);
            for capture in captures {
                if let Capture::Copy(value) = capture {
                    resolve(value);
                }
            }
        }
        ir::Instr::GetTable { out, table, key } => {
            resolve(out);
            resolve(table);
            resolve(key);
        }
        ir::Instr::SetTable { table, key, value } => {
            resolve(table);
            resolve(key);
            resolve(value);
        }
        ir::Instr::SetGlobal { value, .. } => resolve(value),
        ir::Instr::Binary { out, lhs, rhs, .. } => {
            resolve(out);
            resolve(lhs);
            resolve(rhs);
        }
        ir::Instr::Concat { out, operands } => {
            resolve(out);
            operands.iter_mut().for_each(resolve)
        }
        ir::Instr::Select {
            out,
            condition,
            then_value,
            else_value,
        } => {
            resolve(out);
            resolve(condition);
            resolve(then_value);
            resolve(else_value);
        }
        ir::Instr::MakePack { head, .. } => head.iter_mut().for_each(resolve),
        ir::Instr::Project { out, .. } | ir::Instr::LoadCell { out, .. } => resolve(out),
        ir::Instr::Call { function, .. } => resolve(function),
        ir::Instr::MethodCall { object, .. } => resolve(object),
        ir::Instr::OpenCell { value, .. } | ir::Instr::StoreCell { value, .. } => resolve(value),
        ir::Instr::SetList { table, .. } => resolve(table),
    }
}

/// Rewrites value references in a block exit.
fn resolve_exit(exit: &mut BlockExit, aliases: &IndexMap<ValueId, ValueId>) {
    let resolve = |value: &mut ValueId| *value = resolve_alias(*value, aliases);
    match exit {
        BlockExit::Fallthrough(_)
        | BlockExit::Jump(_)
        | BlockExit::NumericForLoop { .. }
        | BlockExit::Return(_) => {}
        BlockExit::Branch { condition, .. } => resolve(condition),
        BlockExit::NumericFor {
            variable,
            start,
            end,
            step,
            ..
        } => {
            resolve(variable);
            resolve(start);
            resolve(end);
            resolve(step);
        }
        BlockExit::GenericFor {
            variables, values, ..
        } => {
            variables.iter_mut().for_each(resolve);
            values.iter_mut().for_each(resolve);
        }
        BlockExit::GenericForLoop { variables, .. } => {
            variables.iter_mut().for_each(resolve);
        }
    }
}

/// Returns the first target after a chain of empty unconditional blocks.
///
/// A cyclic chain is left unchanged so threading cannot choose an arbitrary
/// block from the cycle.
fn threaded_target(blocks: &[RawBlock], target: usize) -> usize {
    let mut current = target;
    let mut visited = IndexSet::default();

    while visited.insert(current) {
        let block = &blocks[current];
        if !block.instrs.is_empty() || !block.exit_writes.is_empty() {
            return current;
        }

        current = match block.exit {
            RawBlockExit::Jump(next) | RawBlockExit::Fallthrough(next) if next != current => next,
            _ => return current,
        };
    }

    target
}

/// Rewrites actual CFG successors through precomputed empty-block targets.
fn thread_raw_exit(exit: &mut RawBlockExit, targets: &[usize]) {
    let thread = |target: &mut usize| *target = targets[*target];

    match exit {
        RawBlockExit::Jump(target) | RawBlockExit::Fallthrough(target) => thread(target),
        RawBlockExit::CondJump {
            then_block,
            else_block,
            ..
        }
        | RawBlockExit::FornPrep {
            body_block: then_block,
            exit_block: else_block,
            ..
        }
        | RawBlockExit::FornLoop {
            body_block: then_block,
            exit_block: else_block,
        }
        | RawBlockExit::ForgLoop {
            body_block: then_block,
            exit_block: else_block,
            ..
        } => {
            thread(then_block);
            thread(else_block);
        }
        RawBlockExit::ForgPrep { body_block, .. } => thread(body_block),
        RawBlockExit::Return { .. } => {}
    }
}

/// Threads every raw CFG edge through empty unconditional blocks.
fn thread_raw_jumps(blocks: &mut [RawBlock]) {
    let targets: Vec<_> = (0..blocks.len())
        .map(|target| threaded_target(blocks, target))
        .collect();

    for block in blocks {
        thread_raw_exit(&mut block.exit, &targets);
    }
}

/// Rewrites raw block targets after blocks are removed or merged.
fn remap_raw_exit(exit: &mut RawBlockExit, old_to_new: &[Option<usize>]) {
    for target in raw_exit_references_mut(exit) {
        *target = old_to_new[*target].expect("referenced raw block must have a dense index");
    }
}

/// Returns every block referenced by a raw exit.
///
/// Unlike [RawBlockExit::targets], this includes the loop block of a `FORGPREP`,
/// which is not one of its CFG successors as this function returns the mechanical
/// exits.
fn raw_exit_references_mut(exit: &mut RawBlockExit) -> SmallVec<[&mut usize; 2]> {
    match exit {
        RawBlockExit::Jump(target) | RawBlockExit::Fallthrough(target) => smallvec![target],
        RawBlockExit::CondJump {
            then_block,
            else_block,
            ..
        }
        | RawBlockExit::FornPrep {
            body_block: then_block,
            exit_block: else_block,
            ..
        }
        | RawBlockExit::FornLoop {
            body_block: then_block,
            exit_block: else_block,
            ..
        }
        | RawBlockExit::ForgPrep {
            body_block: then_block,
            exit_block: else_block,
            ..
        }
        | RawBlockExit::ForgLoop {
            body_block: then_block,
            exit_block: else_block,
            ..
        } => smallvec![then_block, else_block],
        RawBlockExit::Return { .. } => SmallVec::new(),
    }
}

/// Merges each block into its predecessor when it has no other way in and
/// directly follows that predecessor in bytecode order.
fn merge_raw_chains(blocks: &mut Vec<RawBlock<'_>>) {
    // luau-compile producing V5 bytecode will generate a jump when it inlines
    // a function, even though the two blocks could have been one block.

    // The entry is referenced by the function itself.
    let mut references = vec![0usize; blocks.len()];
    references[0] = 1;
    for block in blocks.iter_mut() {
        for target in raw_exit_references_mut(&mut block.exit) {
            references[*target] += 1;
        }
    }

    let mut write = 0;
    let mut old_to_new = vec![None; blocks.len()];
    for read in 0..blocks.len() {
        // We're avoiding borrow checking or allocs by splitting.
        let (kept, rest) = blocks.split_at_mut(read);
        let block = &mut rest[0];

        if let Some(previous) = kept[..write].last_mut()
            && let RawBlockExit::Jump(target) | RawBlockExit::Fallthrough(target) = previous.exit
            && target == read
            && previous.exit_writes.is_empty()
            && references[read] == 1
        {
            previous.instrs.to_mut().extend_from_slice(&block.instrs);
            // `block` is dead after this and gets truncated away, so swapping
            // avoids needing `Default` or `Clone` on these fields.
            std::mem::swap(&mut previous.exit_writes, &mut block.exit_writes);
            std::mem::swap(&mut previous.exit, &mut block.exit);
        } else {
            old_to_new[read] = Some(write);
            blocks.swap(write, read);
            write += 1;
        }
    }
    blocks.truncate(write);

    for block in blocks.iter_mut() {
        remap_raw_exit(&mut block.exit, &old_to_new);
    }
}

/// Removes unreachable raw blocks and merges straight-line chains while retaining bytecode order.
fn reachable_raw_blocks<'p>(proto: &'p Proto) -> Result<Vec<RawBlock<'p>>> {
    let mut raw_blocks = build_raw_from_proto(proto)?;
    ensure!(!raw_blocks.is_empty(), "function contains no basic blocks");

    for (block, raw) in raw_blocks.iter().enumerate() {
        for target in raw.exit.targets() {
            ensure!(
                target < raw_blocks.len(),
                "raw bb{block} targets invalid bb{target}"
            );
        }
    }

    thread_raw_jumps(&mut raw_blocks);

    let mut reachable = IndexSet::default();
    let mut pending = VecDeque::from([0]);
    while let Some(block) = pending.pop_front() {
        if reachable.insert(block) {
            pending.extend(raw_blocks[block].exit.targets());
        }
    }

    let mut old_to_new = vec![None; raw_blocks.len()];
    let mut next = 0;
    for (old, item) in old_to_new.iter_mut().enumerate() {
        if reachable.contains(old) {
            *item = Some(next);
            next += 1;
        }
    }

    let mut raw_blocks = raw_blocks
        .into_iter()
        .enumerate()
        .filter_map(|(old, mut block)| {
            reachable.contains(old).then(|| {
                remap_raw_exit(&mut block.exit, &old_to_new);
                block
            })
        })
        .collect();

    merge_raw_chains(&mut raw_blocks);

    // Give a looping entry block a preheader, so that the function entry has no
    // predecessors and every join has an immediate dominator to open shared cells in.
    if raw_blocks
        .iter()
        .any(|block| block.exit.targets().contains(&0))
    {
        for block in &mut raw_blocks {
            for target in raw_exit_references_mut(&mut block.exit) {
                *target += 1;
            }
        }
        raw_blocks.insert(
            0,
            RawBlock {
                instrs: Cow::Borrowed(&[]),
                exit_writes: SmallVec::new(),
                exit: RawBlockExit::Fallthrough(1),
            },
        );
    }

    Ok(raw_blocks)
}

/// Folds the diamond that Luau emits for a comparison used as a value into
/// one [Select](ir::Instr::Select) instruction.
///
/// Luau writes such a value with a conditional jump into the pair
/// `LOADB R false +1` and `LOADB R true`. After lifting, each `LOADB` is an
/// arm that holds one boolean constant and passes it to the same join.
/// That is the only shape this folds. Diamonds with any other arms, such as
/// if-expressions, stay as they are.
///
/// # The problem
/// Under normal circumstances such shapes are handled fine, through
/// the `folding` module. However, because LOADB can jump on its own,
/// it creates more blocks. Because `folding` does not work cross-block,
/// this effectively forces the region structurer to later (possibly)
/// miss some conditions or decisions and duplicate blocks as a result.
///
/// # Example
///
/// ```text
/// bb1(%v9, %v20):
///     %v7 = copy %v3
///     %v8 = const 5
///     %v10 = lt %v9, %v8
///     branch %v10, bb3, bb2
///
/// bb2:
///     %v11 = const false
///     jump bb4(%v11)
///
/// bb3:
///     %v12 = const true
///     fallthrough bb4(%v12)
///
/// bb4(%v13):
///     %q2 = pack [%v13]
///     %q3 = call %v7(%q2)
///     %v15 = project %q3, 0
///     branch %v15, bb5, bb9
/// ```
///
/// Above FIR snippet is somewhat equivalent to this:
///
/// ```luau
/// if v7(v9 < 5) then
/// ```
///
/// If this were to appear as a loop guard, it wouldn't be structured
/// prettily. The intended shape after this transformation is:
///
/// ```text
/// bb1(%v9, %v20):
///     %v7 = copy %v3
///     %v8 = const 5
///     %v10 = lt %v9, %v8
///     %v11 = const false
///     %v12 = const true
///     %v13 = select %v10, %v12, %v11
///     %q2 = pack [%v13]
///     %q3 = call %v7(%q2)
///     %v15 = project %q3, 0
///     branch %v15, bb5, bb9
/// ```
///
/// The diamond was replaced with a single select.
fn fold_select_diamonds(cfg: ControlFlowGraph<Block>) -> ControlFlowGraph<Block> {
    let mut predecessors: Vec<SmallVec<[usize; 2]>> = cfg
        .nodes()
        .map(|block| cfg.predecessors(block).collect())
        .collect();
    let mut blocks: Vec<Option<Block>> = cfg.into_items().map(Some).collect();

    for head in 0..blocks.len() {
        // The head takes over the exit of the join, which can branch into
        // another diamond, as in `f(a < b, c < d)`.
        while let Some(diamond) = SelectDiamond::find(&blocks, &predecessors, head) {
            diamond.fold(&mut blocks, &mut predecessors);
        }
    }

    // The folds leave the graph out of date in two ways.
    //
    // `ControlFlowGraph` computes its successor and predecessor lists once,
    // when it is built, and keeps them in dense, immutable storage (CSR) for
    // speed. Each fold gave its head the successors of the join, and those
    // successors are now reached from the head. Only a new graph has the
    // right lists.
    //
    // The folded arms and joins are unreachable now. The passes after
    // lifting expect every block to be reachable and every predecessor to
    // be a real way into its block. `Storage`, `Folding` and materialization
    // walk every block, and the region structurer reads every predecessor.
    // So the new graph holds only the kept blocks, renumbered.
    compact_blocks(blocks)
}

/// A `LOADB` diamond found by [`fold_select_diamonds`].
struct SelectDiamond {
    head: usize,
    then_arm: BoolArm,
    else_arm: BoolArm,
    join: usize,
}

impl SelectDiamond {
    /// Returns the diamond that `head` branches into, if there is one.
    fn find(
        blocks: &[Option<Block>],
        predecessors: &[SmallVec<[usize; 2]>],
        head: usize,
    ) -> Option<Self> {
        let BlockExit::Branch {
            then_edge,
            else_edge,
            ..
        } = &blocks[head].as_ref()?.exit
        else {
            return None;
        };
        let then_arm = BoolArm::find(blocks, predecessors, head, then_edge.target)?;
        let else_arm = BoolArm::find(blocks, predecessors, head, else_edge.target)?;

        let join = then_arm.join;
        let join_predecessors = &predecessors[join];
        let is_diamond = then_arm.block != else_arm.block
            && else_arm.join == join
            && then_arm.constant != else_arm.constant
            && join != head
            && blocks[join].as_ref()?.params.len() == 1
            && join_predecessors.len() == 2
            && join_predecessors.contains(&then_arm.block)
            && join_predecessors.contains(&else_arm.block);

        is_diamond.then_some(Self {
            head,
            then_arm,
            else_arm,
            join,
        })
    }

    /// Moves both arms and the join into the head, with the join param
    /// defined by a select over the two constants.
    fn fold(self, blocks: &mut [Option<Block>], predecessors: &mut [SmallVec<[usize; 2]>]) {
        let then_arm = blocks[self.then_arm.block].take().expect("found above");
        let else_arm = blocks[self.else_arm.block].take().expect("found above");
        let join = blocks[self.join].take().expect("found above");
        let head = blocks[self.head].as_mut().expect("found above");

        let BlockExit::Branch { condition, .. } = &head.exit else {
            unreachable!("the head of a diamond branches");
        };
        let select = ir::Instr::Select {
            out: join.params[0],
            condition: *condition,
            then_value: self.then_arm.out,
            else_value: self.else_arm.out,
        };

        head.instrs.extend(then_arm.instrs);
        head.instrs.extend(else_arm.instrs);
        head.instrs.push(select);
        head.instrs.extend(join.instrs);
        head.outputs.extend(join.outputs);
        head.exit = join.exit;

        for target in head.exit.targets() {
            for predecessor in &mut predecessors[target] {
                if *predecessor == self.join {
                    *predecessor = self.head;
                }
            }
        }
    }
}

/// An arm of a [`SelectDiamond`]. It is a lifted `LOADB`.
struct BoolArm {
    block: usize,
    out: ValueId,
    constant: bool,
    join: usize,
}

impl BoolArm {
    /// Returns the arm at `block` if it only loads one boolean constant and
    /// passes it on, and `head` is the only way into it.
    fn find(
        blocks: &[Option<Block>],
        predecessors: &[SmallVec<[usize; 2]>],
        head: usize,
        block: usize,
    ) -> Option<Self> {
        let arm = blocks[block].as_ref()?;
        let [
            ir::Instr::Const {
                out,
                value: ir::Constant::Bool(constant),
            },
        ] = arm.instrs.as_slice()
        else {
            return None;
        };
        let (BlockExit::Jump(edge) | BlockExit::Fallthrough(edge)) = &arm.exit else {
            return None;
        };

        let is_arm = predecessors[block].as_slice() == [head]
            && arm.params.is_empty()
            && arm.outputs.is_empty()
            && edge.params == [*out];

        is_arm.then_some(Self {
            block,
            out: *out,
            constant: *constant,
            join: edge.target,
        })
    }
}

/// Drops the folded blocks and renumbers the edges of the rest.
fn compact_blocks(blocks: Vec<Option<Block>>) -> ControlFlowGraph<Block> {
    let mut renumbered = vec![None; blocks.len()];
    let mut kept = Vec::with_capacity(blocks.len());
    for (old, block) in blocks.into_iter().enumerate() {
        if let Some(block) = block {
            renumbered[old] = Some(kept.len());
            kept.push(block);
        }
    }

    let renumber = |target: &mut usize| {
        *target = renumbered[*target].expect("edges only reach kept blocks");
    };
    for block in &mut kept {
        for edge in block.exit.edges_mut() {
            renumber(&mut edge.target);
        }
        if let BlockExit::GenericFor { loop_block, .. } = &mut block.exit {
            renumber(loop_block);
        }
    }

    ControlFlowGraph::from_nodes_and_exits(kept.into_iter().map(|block| {
        let targets = block.exit.targets();
        (block, targets)
    }))
}

/// Resolves one proto's debug strings from its disassembled chunk.
fn resolve_debug(proto: &Proto, chunk: &Chunk) -> Result<Debug> {
    let name = proto
        .debug_name
        .map(|name| {
            chunk
                .get_string(name)
                .with_context(|| format!("missing debug name string {}", name.0))
        })
        .transpose()?;
    let locals = proto
        .locals
        .iter()
        .map(|local| {
            Ok(DebugLocal {
                name: chunk
                    .get_string(local.name)
                    .with_context(|| format!("missing local name string {}", local.name.0))?,
                register: local.register,
                start_pc: local.start_pc,
                end_pc: local.end_pc,
            })
        })
        .collect::<Result<_>>()?;
    let upvalues = proto
        .upvalue_names
        .iter()
        .map(|name| {
            name.map(|name| {
                chunk
                    .get_string(name)
                    .with_context(|| format!("missing upvalue name string {}", name.0))
            })
            .transpose()
        })
        .collect::<Result<_>>()?;

    Ok(Debug {
        name,
        locals,
        upvalues,
    })
}

/// Mutable state for lifting a [`Chunk`].
struct UnitLifter {
    chunk: Chunk,
}

impl UnitLifter {
    fn new(chunk: Chunk) -> Self {
        Self { chunk }
    }

    fn lift(mut self) -> Result<Unit<Function>> {
        let functions = self.lift_functions()?;
        let userdata_names = self.take_userdata_names();

        Ok(Unit::from_vec(
            self.chunk.entry_proto,
            functions,
            userdata_names,
        ))
    }

    fn lift_functions(&mut self) -> Result<Vec<Function>> {
        let mut functions = Vec::with_capacity(self.chunk.protos.len());
        for index in 0..self.chunk.protos.len() {
            let proto = &mut self.chunk.protos[index];
            let type_info = std::mem::take(&mut proto.type_info);
            functions.push(self.lift_function(index, type_info)?);
        }
        Ok(functions)
    }

    fn lift_function(&self, index: usize, type_info: ProtoTypeInfo) -> Result<Function> {
        let proto = &self.chunk.protos[index];
        let raw_blocks = reachable_raw_blocks(proto)?;
        let cfg = ControlFlowGraph::from_nodes_and_exits(raw_blocks.into_iter().map(|block| {
            let targets = block.exit.targets();
            (block, targets)
        }));
        FunctionLifter::new(proto, &self.chunk, cfg)?.lift(type_info)
    }

    fn take_userdata_names(&mut self) -> Option<Vec<UserdataTypeMapping>> {
        self.chunk.userdata_type_mappings.take().map(|names| {
            names
                .into_iter()
                .map(|mapping| UserdataTypeMapping {
                    index: mapping.index,
                    name: mapping.name.and_then(|id| self.chunk.get_string(id)),
                })
                .collect()
        })
    }
}

/// Lifts every proto in one disassembled chunk into a flat IR unit.
pub(crate) fn lift(chunk: Chunk) -> Result<Unit<Function>> {
    UnitLifter::new(chunk).lift()
}
