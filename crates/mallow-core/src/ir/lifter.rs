use std::collections::{HashMap, HashSet, VecDeque};
use std::ops::Range;

use anyhow::{Context, Result, bail, ensure};
use id_arena::Arena;
use smol_str::{SmolStr, ToSmolStr};

use super::ssa::Ssa;
use super::{self as ir, Block, BlockExit, Capture, Function, Pack, PackId, ValueId};
use crate::common::ByteString;
use crate::disasm::Chunk;
use crate::hil::cflow::cfg::{Cond, CondRhs, RawBlock, RawBlockExit, build_raw_from_proto};
use crate::hil::cflow::graph::{AdjGraph, GraphView, build_graph};
use crate::hil::ir::{Cell, CellId, CellOrigin, Number};
use crate::hil::lifter::common::{CAPTURE_REF, CAPTURE_UPVAL, CAPTURE_VAL};
use crate::il::{
    self, ChildProtoId, ConstId, Count, ImportPath, Proto, ProtoId, reg_add, reg_range,
};
use crate::operator::{BinOp, UnOp};

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

/// Storage generation numbers for physical registers.
#[derive(Debug, Clone)]
struct CaptureGenerations([u16; 256]);

impl Default for CaptureGenerations {
    fn default() -> Self {
        Self([0; 256])
    }
}

impl CaptureGenerations {
    /// Returns the current generation of one register.
    fn get(&self, reg: u8) -> u16 {
        self.0[reg as usize]
    }

    /// Starts new generations for registers closed by `CLOSEUPVALS`.
    fn close(&mut self, from_reg: u8) -> Result<()> {
        for generation in &mut self.0[from_reg as usize..] {
            *generation = generation
                .checked_add(1)
                .context("capture generation overflow")?;
        }
        Ok(())
    }
}

/// Function-wide facts about reference-captured registers.
struct FunctionCaptures {
    /// Cell for each captured register generation.
    register_cells: HashMap<(u8, u16), CellId>,
    /// A list of captured registers
    captured_registers: Vec<u8>,
    /// Storage generations at each raw block entry.
    block_generations: Vec<CaptureGenerations>,
}

impl FunctionCaptures {
    /// Finds captured register generations and allocates their cells in bytecode order.
    fn analyze(proto: &Proto, raw_blocks: &[RawBlock], cells: &mut Arena<Cell>) -> Result<Self> {
        let mut generations = CaptureGenerations::default();
        let mut block_generations = vec![CaptureGenerations::default(); raw_blocks.len()];

        let mut seen = HashSet::new();
        let mut capture_order = Vec::new();

        for (block_index, block) in raw_blocks.iter().enumerate() {
            block_generations[block_index] = generations.clone();

            for decoded in &proto.instrs[block.instr_range.clone()] {
                if let il::Instr::Capture {
                    capture_type: CAPTURE_REF,
                    reg,
                } = decoded.instr
                {
                    let key = (reg, generations.get(reg));
                    if seen.insert(key) {
                        capture_order.push(key);
                    }
                }

                if let il::Instr::CloseUpvals { reg } = decoded.instr {
                    generations.close(reg)?;
                }
            }
        }

        let register_cells: HashMap<_, _> = capture_order
            .into_iter()
            .map(|(reg, generation)| {
                let cell = cells.alloc(Cell {
                    origin: CellOrigin::CapturedRegister { reg, generation },
                });
                ((reg, generation), cell)
            })
            .collect();

        let mut captured_registers: Vec<_> = register_cells.keys().map(|(reg, _)| *reg).collect();
        captured_registers.sort_unstable();
        captured_registers.dedup();

        Ok(Self {
            register_cells,
            captured_registers,
            block_generations,
        })
    }

    /// Returns the cell for one captured register generation.
    #[inline]
    #[must_use]
    fn cell(&self, reg: u8, generation: u16) -> Option<CellId> {
        self.register_cells.get(&(reg, generation)).copied()
    }

    /// Returns every physical register that is captured in any generation.
    fn captured_registers(&self) -> impl Iterator<Item = u8> {
        self.captured_registers.iter().copied()
    }

    /// Returns captured cells for one generation in register order.
    fn cells_in<'a>(
        &'a self,
        generations: &'a CaptureGenerations,
    ) -> impl Iterator<Item = (u8, CellId)> {
        self.captured_registers
            .iter()
            .copied()
            .filter_map(|reg| self.cell(reg, generations.get(reg)).map(|cell| (reg, cell)))
    }
}

/// Mutable state for lifting one function directly into flat IR.
struct FunctionLifter<'a, 'g> {
    /// Proto currently being lifted.
    proto: &'a Proto,
    /// Chunk that owns constants and child protos.
    chunk: &'a Chunk,
    /// Raw bytecode blocks in instruction order.
    raw_blocks: &'a [RawBlock],
    /// Graph used to construct register SSA.
    graph: &'g AdjGraph<'g>,
    /// Mutable cells owned by the function.
    cells: Arena<Cell>,
    /// Cell for each declared upvalue.
    upvalues: Vec<CellId>,
    /// Function-wide reference capture facts.
    captures: FunctionCaptures,
}

impl<'a, 'g> FunctionLifter<'a, 'g> {
    /// Creates lifting state for one already analyzed raw function.
    fn new(
        proto: &'a Proto,
        chunk: &'a Chunk,
        raw_blocks: &'a [RawBlock],
        graph: &'g AdjGraph<'g>,
    ) -> Result<Self> {
        let mut cells = Arena::new();
        let upvalues = (0..proto.num_upvals)
            .map(|index| {
                cells.alloc(Cell {
                    origin: CellOrigin::Upvalue(index),
                })
            })
            .collect();
        let captures = FunctionCaptures::analyze(proto, raw_blocks, &mut cells)?;

        Ok(Self {
            proto,
            chunk,
            raw_blocks,
            graph,
            cells,
            upvalues,
            captures,
        })
    }

    /// Lifts blocks, seals SSA, resolves aliases, and verifies the function.
    fn lift(mut self) -> Result<Function> {
        let mut ssa = Ssa::new(self.graph, self.proto.max_stack_size);
        let mut packs = Arena::new();

        let mut params: Vec<_> = (0..self.proto.num_params)
            .map(|reg| {
                let value = ssa.alloc();
                ssa.write_reg(self.graph.entry(), reg, value);
                value
            })
            .collect();

        let mut blocks = vec![None; self.raw_blocks.len()];
        for block_index in self.graph.reverse_post_order() {
            blocks[block_index] = Some(self.lift_block(block_index, &mut ssa, &mut packs)?);
            ssa.mark_filled(block_index);
        }

        let mut blocks: Vec<_> = blocks
            .into_iter()
            .enumerate()
            .map(|(block, value)| {
                value.with_context(|| format!("reachable bb{block} was not lifted"))
            })
            .collect::<Result<_>>()?;
        let (values, aliases) = ssa.finish(&mut blocks);
        resolve_aliases(&mut blocks, &aliases);
        for p in &mut params {
            *p = resolve_alias(*p, &aliases)
        }

        let function = Function {
            proto: self.proto.id,
            params,
            is_vararg: self.proto.is_vararg,
            upvalues: self.upvalues,
            values,
            packs,
            cells: self.cells,
            blocks,
        };
        function
            .verify()
            .with_context(|| format!("invalid direct IR for proto {}", function.proto.0))?;
        Ok(function)
    }

    /// Lifts one complete bytecode block.
    fn lift_block(
        &mut self,
        block: usize,
        ssa: &mut Ssa<'g, AdjGraph<'g>>,
        packs: &mut Arena<Pack>,
    ) -> Result<Block> {
        BlockLifter::new(self, ssa, packs, block)?.lift()
    }
}

/// Mutable state for lifting one complete basic block.
struct BlockLifter<'lift, 'source, 'graph> {
    /// Function-wide lifting state.
    function: &'lift mut FunctionLifter<'source, 'graph>,
    /// Function SSA state.
    ssa: &'lift mut Ssa<'graph, AdjGraph<'graph>>,
    /// Function pack arena.
    packs: &'lift mut Arena<Pack>,

    /// Block currently being lifted.
    block: usize,
    /// Range of instructions in the block.
    instr_range: Range<usize>,
    /// Current instruction cursor relative to [`instr_range`].
    cursor: usize,

    /// Flat instructions emitted for this block.
    emitted: Vec<ir::Instr>,
    /// Pack available to an immediate variadic consumer.
    pending: Option<PendingValues>,
    /// Register values projected only when they are read.
    deferred: [Option<DeferredValue>; 256],
    /// Capture generations at the current instruction.
    generations: CaptureGenerations,
}

impl<'lift, 'source, 'graph> BlockLifter<'lift, 'source, 'graph> {
    /// Creates a lifter for one raw bytecode block.
    fn new(
        function: &'lift mut FunctionLifter<'source, 'graph>,
        ssa: &'lift mut Ssa<'graph, AdjGraph<'graph>>,
        packs: &'lift mut Arena<Pack>,
        block: usize,
    ) -> Result<Self> {
        let instr_range = function.raw_blocks[block].instr_range.clone();
        let generations = function.captures.block_generations[block].clone();
        let mut lifter = Self {
            function,
            ssa,
            packs,
            block,
            instr_range,
            cursor: 0,
            emitted: Vec::new(),
            pending: None,
            deferred: [None; 256],
            generations,
        };

        if block == lifter.function.graph.entry() {
            let mut nil = None;
            for reg in lifter.function.captures.captured_registers() {
                if reg < lifter.function.proto.num_params {
                    continue;
                }

                let value = *nil.get_or_insert_with(|| {
                    let value = lifter.ssa.alloc();
                    lifter.emitted.push(ir::Instr::Const {
                        out: value,
                        value: ir::Constant::Nil,
                    });
                    value
                });
                lifter.ssa.write_reg(block, reg, value);
            }

            for (reg, cell) in lifter.function.captures.cells_in(&lifter.generations) {
                let value = lifter.ssa.read_reg(block, reg);
                lifter.emitted.push(ir::Instr::OpenCell { cell, value });
            }
        }

        Ok(lifter)
    }

    /// Lifts the block body and its exit.
    fn lift(mut self) -> Result<Block> {
        while let Some(instr) = self.next() {
            self.flush_pending_before(instr)?;
            self.lift_instr(instr)?;
        }

        let mut outputs = Vec::new();
        let exit = lower_exit(
            &self.function.raw_blocks[self.block],
            &mut self,
            &mut outputs,
        )?;

        Ok(Block {
            outputs,
            instrs: self.emitted,
            exit,
        })
    }

    /// Returns the next bytecode instruction and advances the cursor.
    fn next(&mut self) -> Option<il::Instr> {
        let idx = self.instr_range.start + self.cursor;
        if idx >= self.instr_range.end {
            return None;
        }
        let instr = self.function.proto.instrs.get(idx)?.instr;
        self.cursor += 1;
        Some(instr)
    }

    /// Returns the current bytecode instruction index.
    #[inline]
    fn current_ip(&self) -> usize {
        self.instr_range.start + self.cursor.saturating_sub(1)
    }

    /// Returns the current bytecode program counter.
    #[inline]
    fn current_pc(&self) -> u32 {
        self.function.proto.instrs[self.current_ip()].word_pc
    }

    /// Allocates one immutable value identity.
    #[inline]
    fn value(&mut self) -> ValueId {
        self.ssa.alloc()
    }

    /// Allocates one value pack identity.
    #[inline]
    fn pack(&mut self) -> PackId {
        self.packs.alloc(Pack)
    }

    /// Emits one fixed value pack.
    #[inline]
    fn fixed_pack(&mut self, head: Vec<ValueId>) -> PackId {
        let out = self.pack();
        self.emitted.push(ir::Instr::MakePack {
            out,
            head,
            tail: None,
        });
        out
    }

    /// Emits one pack with a fixed prefix and open tail.
    #[inline]
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
    #[inline]
    fn open_cell(&self, reg: u8) -> Option<CellId> {
        self.function.captures.cell(reg, self.generations.get(reg))
    }

    /// Projects a deferred register into its current storage.
    #[inline]
    fn materialize_deferred(&mut self, reg: u8) -> Option<ValueId> {
        let deferred = self.deferred[reg as usize].take()?;
        let out = self.value();
        self.emitted.push(ir::Instr::Project {
            out,
            pack: deferred.pack,
            index: deferred.index,
        });
        if let Some(cell) = self.open_cell(reg) {
            self.emitted.push(ir::Instr::StoreCell { cell, value: out });
        } else {
            self.ssa.write_reg(self.block, reg, out);
        }
        Some(out)
    }

    /// Records all register values represented by an open pack.
    #[inline]
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

    /// Reads one register and emits a cell load when its storage is captured.
    #[inline]
    fn read_reg(&mut self, reg: u8) -> ValueId {
        if let Some(value) = self.materialize_deferred(reg) {
            return value;
        }

        match self.open_cell(reg) {
            Some(cell) => {
                let out = self.value();
                self.emitted.push(ir::Instr::LoadCell { out, cell });
                out
            }
            None => self.ssa.read_reg(self.block, reg),
        }
    }

    /// Reads a fixed register range in order.
    #[inline]
    #[must_use]
    fn read_regs(&mut self, start: u8, count: u8) -> Vec<ValueId> {
        reg_range(start, count)
            .map(|reg| self.read_reg(reg))
            .collect()
    }

    /// Defines one register from an already emitted immutable value.
    #[inline]
    fn write_reg(&mut self, reg: u8, value: ValueId) {
        self.deferred[reg as usize] = None;
        match self.open_cell(reg) {
            Some(cell) => self.emitted.push(ir::Instr::StoreCell { cell, value }),
            None => self.ssa.write_reg(self.block, reg, value),
        }
    }

    /// Defines a register with a fresh copy identity.
    #[inline]
    fn copy_reg(&mut self, reg: u8, value: ValueId) {
        let out = self.value();
        self.emitted.push(ir::Instr::Copy { out, value });
        self.write_reg(reg, out);
    }

    /// Projects fixed results from a pack into consecutive registers.
    #[inline]
    fn write_pack(&mut self, start: u8, count: u8, pack: PackId) {
        for (index, reg) in reg_range(start, count).enumerate() {
            let out = self.value();
            self.emitted.push(ir::Instr::Project { out, pack, index });
            self.write_reg(reg, out);
        }
    }

    /// Emits one literal constant.
    #[inline]
    fn constant(&mut self, value: ir::Constant) -> ValueId {
        let out = self.value();
        self.emitted.push(ir::Instr::Const { out, value });
        out
    }

    /// Emits a global read.
    #[inline]
    fn global(&mut self, name: SmolStr) -> ValueId {
        let out = self.value();
        self.emitted.push(ir::Instr::GetGlobal { out, name });
        out
    }

    /// Emits a binary operation.
    #[inline]
    fn binary(&mut self, lhs: ValueId, op: BinOp, rhs: ValueId) -> ValueId {
        let out = self.value();
        self.emitted.push(ir::Instr::Binary { out, lhs, op, rhs });
        out
    }

    /// Emits a string-keyed table read without changing the key bytes.
    #[inline]
    fn string_access(&mut self, table: ValueId, key: ByteString) -> ValueId {
        let key = self.constant(ir::Constant::String(key));
        let out = self.value();
        self.emitted.push(ir::Instr::GetTable { out, table, key });
        out
    }

    /// Emits a string-keyed table write without changing the key bytes.
    #[inline]
    fn string_store(&mut self, table: ValueId, key: ByteString, value: ValueId) {
        let key = self.constant(ir::Constant::String(key));
        self.emitted.push(ir::Instr::SetTable { table, key, value });
    }

    /// Returns the cell already allocated for one reference capture.
    #[inline]
    fn capture_cell(&self, reg: u8) -> Result<CellId> {
        let generation = self.generations.get(reg);
        self.open_cell(reg).with_context(|| {
            format!("reference capture has no cell for R{reg} generation {generation}")
        })
    }

    /// Closes captured cells and opens storage required by later generations.
    #[inline]
    fn close_cells(&mut self, from_reg: u8) -> Result<()> {
        let mut next_generations = self.generations.clone();
        next_generations.close(from_reg)?;

        let next_registers: Vec<_> = self
            .function
            .captures
            .cells_in(&next_generations)
            .filter_map(|(reg, _)| (reg >= from_reg).then_some(reg))
            .collect();
        for reg in next_registers {
            self.materialize_deferred(reg);
        }

        for reg in from_reg..self.function.proto.max_stack_size {
            let Some(cell) = self.open_cell(reg) else {
                continue;
            };
            let value = self.value();
            self.emitted.push(ir::Instr::LoadCell { out: value, cell });
            self.ssa.write_reg(self.block, reg, value);
        }

        self.generations = next_generations;
        let cells = self
            .function
            .captures
            .cells_in(&self.generations)
            .filter(|(reg, _)| *reg >= from_reg);
        for (reg, cell) in cells {
            let value = self.ssa.read_reg(self.block, reg);
            self.emitted.push(ir::Instr::OpenCell { cell, value });
        }

        Ok(())
    }

    /// Marks an open pack as unavailable to later variadic consumers.
    #[inline]
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
            il::Instr::NameCall { .. } | il::Instr::NameCallUData { .. } => {
                match self
                    .function
                    .proto
                    .instrs
                    .get(self.instr_range.start + self.cursor)
                    .map(|decoded| decoded.instr)
                {
                    Some(il::Instr::Call {
                        func, arg_count, ..
                    }) if Count::from(arg_count).is_variadic() && base >= reg_add(func, 2) => true,
                    _ => bail!(
                        "malformed bytecode: NAMECALL at {} is not followed by CALL",
                        self.current_pc()
                    ),
                }
            }
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
    #[inline]
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
    #[inline]
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
    #[inline]
    fn const_name(&self, id: ConstId) -> Result<SmolStr> {
        let string = self.const_string(id)?;
        string
            .as_utf8()
            .map(ToSmolStr::to_smolstr)
            .with_context(|| format!("string constant {id:?} is not valid UTF-8"))
    }

    /// Emits a numeric constant required by an arithmetic opcode.
    #[inline]
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
            bail!("malformed bytecode: NAMECALL at {namecall_pc} is not followed by CALL");
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
    #[inline]
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
        let captures = self.consume_captures(capture_count, dest, out)?;
        self.emitted.push(ir::Instr::Closure {
            out,
            proto,
            captures,
        });
        self.write_reg(dest, out);

        Ok(())
    }

    /// Consumes the CAPTURE instructions following a closure opcode.
    fn consume_captures(
        &mut self,
        count: u8,
        closure_reg: u8,
        closure: ValueId,
    ) -> Result<Vec<Capture>> {
        let mut captures = Vec::with_capacity(count as usize);
        for capture_index in 0..count {
            let Some(il::Instr::Capture { capture_type, reg }) = self.next() else {
                bail!("malformed bytecode: missing CAPTURE #{capture_index}");
            };

            let capture = match capture_type {
                CAPTURE_VAL if reg == closure_reg => Capture::Copy(closure),
                CAPTURE_VAL => Capture::Copy(self.read_reg(reg)),
                CAPTURE_REF => Capture::Share(self.capture_cell(reg)?),
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
        Ok(captures)
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
    #[inline]
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
                let operands = (a..b).rev().map(|reg| self.read_reg(reg)).collect();
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
}

/// Returns the binary operator encoded by an arithmetic instruction.
#[inline]
fn binop_for_instr(instr: il::Instr) -> BinOp {
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
        _ => unreachable!("instruction is not a binary operator"),
    }
}

/// Returns the unary operator encoded by an instruction.
#[inline]
fn unop_for_instr(instr: il::Instr) -> UnOp {
    match instr {
        il::Instr::Not { .. } => UnOp::Not,
        il::Instr::Minus { .. } => UnOp::Minus,
        il::Instr::Length { .. } => UnOp::Length,
        _ => unreachable!("instruction is not a unary operator"),
    }
}

/// Lowers one raw block exit after its body has been lifted.
fn lower_exit(
    raw: &RawBlock,
    lifter: &mut BlockLifter<'_, '_, '_>,
    outputs: &mut Vec<ValueId>,
) -> Result<BlockExit> {
    let exit = match &raw.exit {
        RawBlockExit::Jump(target) => {
            lifter.flush_pending();
            apply_exit_writes(raw, lifter, outputs);
            BlockExit::Jump(*target)
        }
        RawBlockExit::Fallthrough(target) => {
            lifter.flush_pending();
            apply_exit_writes(raw, lifter, outputs);
            BlockExit::Fallthrough(*target)
        }
        RawBlockExit::CondJump {
            cond,
            then_block,
            else_block,
        } => {
            lifter.flush_pending();
            let condition = match cond {
                Cond::Unary(reg) => lifter.read_reg(*reg),
                Cond::Binary { lhs, op, rhs } => {
                    let lhs = lifter.read_reg(*lhs);
                    let rhs = match rhs {
                        CondRhs::Reg(reg) => lifter.read_reg(*reg),
                        CondRhs::Const(index) => lifter.emit_constant(ConstId(*index))?,
                        CondRhs::Nil => lifter.constant(ir::Constant::Nil),
                        CondRhs::Bool(value) => lifter.constant(ir::Constant::Bool(*value)),
                    };
                    lifter.binary(lhs, *op, rhs)
                }
            };
            apply_exit_writes(raw, lifter, outputs);
            BlockExit::Branch {
                condition,
                then_block: *then_block,
                else_block: *else_block,
            }
        }
        RawBlockExit::FornPrep {
            base,
            body_block,
            exit_block,
        } => {
            lifter.flush_pending();
            let start = lifter.read_reg(reg_add(*base, 2));
            let end = lifter.read_reg(*base);
            let step = lifter.read_reg(reg_add(*base, 1));
            apply_exit_writes(raw, lifter, outputs);
            let variable = lifter.ssa.read_reg(*body_block, reg_add(*base, 2));
            BlockExit::NumericFor {
                body_block: *body_block,
                exit_block: *exit_block,
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
            lifter.flush_pending();
            apply_exit_writes(raw, lifter, outputs);
            BlockExit::NumericForLoop {
                body_block: *body_block,
                exit_block: *exit_block,
            }
        }
        RawBlockExit::ForgPrep {
            base,
            body_block,
            exit_block,
        } => {
            lifter.flush_pending();
            let values = [
                lifter.read_reg(*base),
                lifter.read_reg(reg_add(*base, 1)),
                lifter.read_reg(reg_add(*base, 2)),
            ];
            apply_exit_writes(raw, lifter, outputs);
            let variables = raw
                .exit_writes
                .iter()
                .map(|reg| lifter.ssa.read_reg(*body_block, *reg))
                .collect();
            BlockExit::GenericFor {
                body_block: *body_block,
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
            lifter.flush_pending();
            apply_exit_writes(raw, lifter, outputs);
            let variables = (0..*result_count)
                .map(|index| {
                    let reg = reg_add(reg_add(*base, 3), index as u8);
                    lifter.ssa.read_reg(*body_block, reg)
                })
                .collect();
            BlockExit::GenericForLoop {
                body_block: *body_block,
                exit_block: *exit_block,
                variables,
            }
        }
        RawBlockExit::Return { base, count } => match Count::from(*count) {
            Count::Number(count) => {
                lifter.flush_pending();
                let values = lifter.read_regs(*base, count);
                BlockExit::Return(lifter.fixed_pack(values))
            }
            Count::Variadic => {
                let pack = lifter.take_variadic_from(*base)?;
                BlockExit::Return(pack)
            }
        },
    };
    Ok(exit)
}

/// Applies register definitions produced by a bytecode block exit.
fn apply_exit_writes(
    raw: &RawBlock,
    lifter: &mut BlockLifter<'_, '_, '_>,
    outputs: &mut Vec<ValueId>,
) {
    for &reg in &raw.exit_writes {
        let value = lifter.value();
        lifter.ssa.write_reg(lifter.block, reg, value);
        outputs.push(value);
    }
}

/// Lowers one raw branch condition into an immutable value.
fn lower_condition(cond: &Cond, lifter: &mut BlockLifter<'_, '_, '_>) -> Result<ValueId> {
    Ok(match cond {
        Cond::Unary(reg) => lifter.read_reg(*reg),
        Cond::Binary { lhs, op, rhs } => {
            let lhs = lifter.read_reg(*lhs);
            let rhs = match rhs {
                CondRhs::Reg(reg) => lifter.read_reg(*reg),
                CondRhs::Const(index) => lifter.emit_constant(ConstId(*index))?,
                CondRhs::Nil => lifter.constant(ir::Constant::Nil),
                CondRhs::Bool(value) => lifter.constant(ir::Constant::Bool(*value)),
            };
            lifter.binary(lhs, *op, rhs)
        }
    })
}

/// Resolves one value through the trivial-Phi alias map.
fn resolve_alias(mut value: ValueId, aliases: &HashMap<ValueId, ValueId>) -> ValueId {
    while let Some(&alias) = aliases.get(&value) {
        value = alias;
    }
    value
}

/// Rewrites all block references to surviving SSA values.
fn resolve_aliases(blocks: &mut [Block], aliases: &HashMap<ValueId, ValueId>) {
    for block in blocks {
        for output in &mut block.outputs {
            *output = resolve_alias(*output, aliases);
        }
        block.outputs.sort_unstable();
        block.outputs.dedup();
        for instr in &mut block.instrs {
            resolve_instr(instr, aliases);
        }
        resolve_exit(&mut block.exit, aliases);
    }
}

/// Rewrites value references in an IR instruction.
fn resolve_instr(instr: &mut ir::Instr, aliases: &HashMap<ValueId, ValueId>) {
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
        ir::Instr::Phi { out, inputs } => {
            resolve(out);
            for (_, value) in inputs {
                resolve(value);
            }
        }
    }
}

/// Rewrites value references in a block exit.
fn resolve_exit(exit: &mut BlockExit, aliases: &HashMap<ValueId, ValueId>) {
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

/// Rewrites raw block targets after unreachable blocks are removed.
#[inline]
fn remap_raw_exit(exit: &mut RawBlockExit, old_to_new: &[Option<usize>]) {
    let remap = |target: &mut usize| {
        *target = old_to_new[*target].expect("reachable raw block target must have a dense index")
    };

    match exit {
        RawBlockExit::Jump(target) | RawBlockExit::Fallthrough(target) => remap(target),
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
        } => {
            remap(then_block);
            remap(else_block);
        }
        RawBlockExit::Return { .. } => {}
    }
}

/// Removes unreachable raw blocks while retaining bytecode order.
fn reachable_raw_blocks(proto: &Proto) -> Result<Vec<RawBlock>> {
    let raw_blocks = build_raw_from_proto(proto)?;
    ensure!(!raw_blocks.is_empty(), "function contains no basic blocks");

    for (block, raw) in raw_blocks.iter().enumerate() {
        for target in raw.exit.targets() {
            ensure!(
                target < raw_blocks.len(),
                "raw bb{block} targets invalid bb{target}"
            );
        }
    }

    let mut reachable = HashSet::new();
    let mut pending = VecDeque::from([0]);
    while let Some(block) = pending.pop_front() {
        if reachable.insert(block) {
            pending.extend(raw_blocks[block].exit.targets());
        }
    }

    let mut old_to_new = vec![None; raw_blocks.len()];
    let mut next = 0;
    for old in 0..raw_blocks.len() {
        if reachable.contains(&old) {
            old_to_new[old] = Some(next);
            next += 1;
        }
    }

    raw_blocks
        .into_iter()
        .enumerate()
        .filter_map(|(old, mut block)| {
            reachable.contains(&old).then(|| {
                remap_raw_exit(&mut block.exit, &old_to_new);
                Ok(block)
            })
        })
        .collect()
}

/// Lifts every proto in one disassembled chunk into flat IR.
#[inline]
pub(crate) fn lift(chunk: &Chunk) -> Result<Vec<Function>> {
    let functions = chunk
        .protos
        .iter()
        .map(|proto| {
            let raw_blocks = reachable_raw_blocks(proto)?;
            let (successors, predecessors) =
                build_graph(raw_blocks.iter().map(|block| block.exit.targets()));
            let graph = AdjGraph::new(0, &successors, &predecessors);
            FunctionLifter::new(proto, chunk, &raw_blocks, &graph)?.lift()
        })
        .collect::<Result<_>>()?;
    Ok(functions)
}
