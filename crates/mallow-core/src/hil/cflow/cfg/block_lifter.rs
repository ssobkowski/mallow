use std::collections::{BTreeMap, HashMap, HashSet};

use anyhow::{Context, Result, bail, ensure};

use super::{Block, BlockExit, Cond, CondRhs, RawBlock, RawBlockExit};
use crate::disasm::Chunk;
use crate::hil::cflow::graph::GraphView;
use crate::hil::cflow::reg_set::RegSet;
use crate::hil::ir::{Capture, Expr, PhiNode, Stmt, ValuePack};
use crate::hil::lifter::ssa::{FunctionSymbols, NamedLocal, Ssa, Symbol, SymbolId, SymbolKind};
use crate::hil::lifter::{CaptureState, LiftContext, MultiRet, flush_multiret, lift};
use crate::hil::ty::bytecode::ProtoTypeContext;
use crate::hil::ty::canonical::TypeId;
use crate::hil::ty::store::TypeStore;
use crate::hil::visitor::{Visitor, VisitorMut};
use crate::il::{ConstId, Count, Proto, reg_add, reg_range};

/// Blocks and SSA metadata produced by one block-lifting run.
pub(super) struct BuildResult {
    /// Lifted blocks with explicit nontrivial Phi statements.
    pub blocks: Vec<Block>,
    /// Symbols and storage links found while building SSA.
    pub symbols: FunctionSymbols,
    /// Bytecode type facts for the surviving SSA versions.
    pub symbol_types: HashMap<SymbolId, TypeId>,
    /// Type graph that owns the IDs in `symbol_types`.
    pub type_store: TypeStore,
}

/// Lifts raw blocks into HIL blocks while preserving nontrivial SSA versions.
///
/// This phase owns the mutable SSA algorithm because block lifting, synthetic
/// terminator writes, and loop-carried repairs depend on its block state.
pub(super) fn lift_blocks<G: GraphView>(
    proto: &Proto,
    chunk: &Chunk,
    raw_blocks: &[RawBlock],
    graph: &G,
) -> Result<BuildResult> {
    BlockLifter::new(proto, chunk, raw_blocks, graph).build()
}

/// Finds the capture state at each basic block entry.
fn capture_states_at_block_entries(proto: &Proto, raw_blocks: &[RawBlock]) -> Vec<CaptureState> {
    let mut states = Vec::with_capacity(raw_blocks.len());
    let mut state = CaptureState::default();
    let mut instr_index = 0;

    for block in raw_blocks {
        assert!(
            instr_index <= block.instr_range.start,
            "raw blocks must be ordered by instruction index"
        );
        for decoded in &proto.instrs[instr_index..block.instr_range.start] {
            state.note_instruction(decoded.instr);
        }
        instr_index = block.instr_range.start;
        states.push(state);
    }

    states
}

/// Mutable state for the SSA-backed CFG block lifting phase.
struct BlockLifter<'a, G: GraphView> {
    proto: &'a Proto,
    chunk: &'a Chunk,
    raw_blocks: &'a [RawBlock],
    graph: &'a G,
    type_store: TypeStore,
    type_context: ProtoTypeContext,
    blocks: Vec<Block>,
    ssa: Ssa<'a, G>,
    params: Vec<SymbolId>,
    upvalues: Vec<SymbolId>,
    loop_carried_links: Vec<(SymbolId, SymbolId)>,
    capture_states: Vec<CaptureState>,
}

impl<'a, G: GraphView> BlockLifter<'a, G> {
    fn new(proto: &'a Proto, chunk: &'a Chunk, raw_blocks: &'a [RawBlock], graph: &'a G) -> Self {
        let mut type_store = TypeStore::new();
        let type_context = ProtoTypeContext::from_proto(proto, chunk, &mut type_store);
        let capture_states = capture_states_at_block_entries(proto, raw_blocks);

        Self {
            proto,
            chunk,
            raw_blocks,
            graph,
            type_store,
            type_context,
            blocks: vec![Block::dummy(); raw_blocks.len()],
            ssa: Ssa::new(graph, proto.max_stack_size, proto.num_upvals),
            params: Vec::with_capacity(proto.num_params as usize),
            upvalues: Vec::with_capacity(proto.num_upvals as usize),
            loop_carried_links: Vec::new(),
            capture_states,
        }
    }

    /// Runs SSA-backed lifting through non-destructive alias resolution.
    fn build(mut self) -> Result<BuildResult> {
        self.initialize_entry_symbols();
        self.lift_blocks()?;
        self.collect_loop_carried_links();
        let symbol_types = self.finish_ssa();
        let named_locals = self.named_locals();
        let (upvalue_storage, captured_storage) = self.storage_members();

        let symbols = FunctionSymbols::new(
            self.params,
            self.upvalues,
            named_locals,
            upvalue_storage,
            captured_storage,
            self.loop_carried_links,
        );

        Ok(BuildResult {
            blocks: self.blocks,
            symbols,
            symbol_types,
            type_store: self.type_store,
        })
    }

    /// Seeds entry-block SSA state for parameters and declared upvalues.
    fn initialize_entry_symbols(&mut self) {
        for i in 0..self.proto.num_params {
            let sym = self.ssa.alloc_symbol(
                Symbol::param(i)
                    .with_type(self.type_context.param(i))
                    .with_local_index(self.proto.local_index_at(i, 0)),
            );
            self.ssa.write_reg(self.graph.entry(), i, sym);
            self.params.push(sym);
        }

        for i in 0..self.proto.num_upvals {
            let sym = self
                .ssa
                .alloc_symbol(Symbol::upval(i).with_type(self.type_context.upvalue(i)));
            self.ssa.write_upval(self.graph.entry(), i, sym);
            self.upvalues.push(sym);
        }
    }

    /// Lifts reachable raw blocks in reverse postorder.
    fn lift_blocks(&mut self) -> Result<()> {
        for block_id in self.graph.reverse_post_order() {
            self.lift_block(block_id)?;
        }
        Ok(())
    }

    /// Lifts one raw block body and lowers its raw terminator into a HIL exit.
    fn lift_block(&mut self, block_id: usize) -> Result<()> {
        let raw_block = &self.raw_blocks[block_id];
        let (mut stmts, mut pending_multiret) = lift(LiftContext {
            instrs: &self.proto.instrs[raw_block.instr_range.clone()],
            chunk: self.chunk,
            proto: self.proto,
            type_context: &self.type_context,
            ssa: &mut self.ssa,
            block_idx: block_id,
            capture_state: self.capture_states[block_id],
        })?;

        let exit = self.lower_exit(block_id, &mut stmts, &mut pending_multiret)?;

        debug_assert!(
            pending_multiret.is_none(),
            "non-variadic exit lowering must consume or flush pending multiret"
        );

        self.blocks[block_id] = Block { stmts, exit };
        self.ssa.mark_filled(block_id);
        Ok(())
    }

    /// Converts a raw terminator into a lifted exit, reading any needed SSA values.
    fn lower_exit(
        &mut self,
        block_id: usize,
        stmts: &mut Vec<Stmt>,
        pending_multiret: &mut Option<MultiRet>,
    ) -> Result<BlockExit> {
        // Exit lowering has three distinct phases:
        //
        // 1. Flush a pending multiret before ordinary exit reads.
        //    Variadic return is the only exception; it consumes the pending multiret
        //    directly instead of flushing it.
        //
        // 2. Read operands from the current block before applying synthetic exit writes.
        //    Examples: return values, branch conditions, for-prep bounds.
        //
        // 3. Apply synthetic exit writes before reading values from successor/body blocks.
        //    Examples: loop body variables created by FORNPREP/FORGLOOP.

        let exit = &self.raw_blocks[block_id].exit;
        let exit_writes = &self.raw_blocks[block_id].exit_writes;
        let exit_pc = self.raw_blocks[block_id].exit_pc;
        match *exit {
            RawBlockExit::Jump(t) => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                self.apply_exit_writes(block_id, exit_pc, exit_writes);
                Ok(BlockExit::Jump(t))
            }
            RawBlockExit::Fallthrough(t) => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                self.apply_exit_writes(block_id, exit_pc, exit_writes);
                Ok(BlockExit::Fallthrough(t))
            }
            RawBlockExit::CondJump {
                ref cond,
                then_block,
                else_block,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                let cond = self.lower_cond(block_id, cond)?;
                self.apply_exit_writes(block_id, exit_pc, exit_writes);
                Ok(BlockExit::CondJump {
                    cond,
                    then_block,
                    else_block,
                })
            }
            RawBlockExit::FornPrep {
                base,
                body_block,
                exit_block,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);

                // These are current-block reads. They must happen before exit_writes.
                let start = self.ssa.read_reg(block_id, reg_add(base, 2));
                let end = self.ssa.read_reg(block_id, reg_add(base, 0));
                let step = self.ssa.read_reg(block_id, reg_add(base, 1));

                // These are terminator/edge writes.
                self.apply_exit_writes(block_id, exit_pc, exit_writes);

                // This is a successor/body-block read. It must happen after exit_writes.
                let var = self.ssa.read_reg(body_block, reg_add(base, 2));

                Ok(BlockExit::FornPrep {
                    base,
                    body_block,
                    exit_block,
                    var,
                    start: Expr::Symbol(start),
                    end: Expr::Symbol(end),
                    step: Expr::Symbol(step),
                })
            }
            RawBlockExit::FornLoop {
                base,
                body_block,
                exit_block,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                self.apply_exit_writes(block_id, exit_pc, exit_writes);
                Ok(BlockExit::FornLoop {
                    base,
                    body_block,
                    exit_block,
                })
            }
            RawBlockExit::ForgPrep {
                base,
                body_block,
                exit_block,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                let exprs = [
                    Expr::Symbol(self.ssa.read_reg(block_id, reg_add(base, 0))),
                    Expr::Symbol(self.ssa.read_reg(block_id, reg_add(base, 1))),
                    Expr::Symbol(self.ssa.read_reg(block_id, reg_add(base, 2))),
                ];
                self.apply_exit_writes(block_id, exit_pc, exit_writes);
                // Capture entry versions before the loop body can assign to them.
                let vars = exit_writes
                    .iter()
                    .map(|reg| self.ssa.read_reg(body_block, *reg))
                    .collect();
                Ok(BlockExit::ForgPrep {
                    base,
                    body_block,
                    exit_block,
                    vars,
                    exprs,
                })
            }
            RawBlockExit::ForgLoop {
                base,
                body_block,
                exit_block,
                result_count,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                self.apply_exit_writes(block_id, exit_pc, exit_writes);
                Ok(BlockExit::ForgLoop {
                    base,
                    body_block,
                    exit_block,
                    vars: (0..result_count)
                        .map(|i| {
                            self.ssa
                                .read_reg(body_block, reg_add(reg_add(base, 3), i as u8))
                        })
                        .collect(),
                })
            }
            RawBlockExit::Return { base, count } => {
                assert!(
                    exit_writes.is_empty(),
                    "RETURN must not have synthetic exit writes: {exit_writes:?}"
                );

                match Count::from(count) {
                    Count::Variadic => {
                        assert!(
                            exit_writes.is_empty(),
                            "variadic return should not have synthetic exit writes"
                        );

                        let Some(multiret) = pending_multiret.take() else {
                            bail!("variadic return without pending multiret");
                        };

                        ensure!(
                            multiret.base >= base,
                            "pending multiret base {} is before variadic return base {}",
                            multiret.base,
                            base
                        );

                        let mut head = Vec::new();
                        for i in base..multiret.base {
                            head.push(Expr::Symbol(self.ssa.read_reg(block_id, i)));
                        }

                        Ok(BlockExit::Return(ValuePack::Open {
                            head,
                            tail: Box::new(multiret.expr),
                        }))
                    }
                    Count::Number(n) => {
                        self.flush_pending_multiret(block_id, stmts, pending_multiret);

                        assert!(
                            exit_writes.is_empty(),
                            "fixed return should not have synthetic exit writes"
                        );

                        let rets = ValuePack::Fixed(
                            reg_range(base, n)
                                .map(|i| Expr::Symbol(self.ssa.read_reg(block_id, i)))
                                .collect(),
                        );

                        Ok(BlockExit::Return(rets))
                    }
                }
            }
        }
    }

    /// Converts a raw register/constant condition into a HIL expression.
    fn lower_cond(&mut self, block_id: usize, cond: &Cond) -> Result<Expr> {
        Ok(match cond {
            Cond::Unary(reg) => Expr::Symbol(self.ssa.read_reg(block_id, *reg)),
            Cond::Binary { lhs, op, rhs } => {
                let lhs = Expr::Symbol(self.ssa.read_reg(block_id, *lhs));
                let rhs = match rhs {
                    CondRhs::Reg(reg) => Expr::Symbol(self.ssa.read_reg(block_id, *reg)),
                    CondRhs::Const(idx) => Expr::from_constant(
                        self.proto
                            .get_constant(ConstId(*idx))
                            .with_context(|| format!("invalid constant id {idx}"))?,
                        self.chunk,
                        self.proto,
                    )?,
                    CondRhs::Nil => Expr::Nil,
                    CondRhs::Bool(value) => Expr::Bool(*value),
                };

                Expr::Binary {
                    lhs: Box::new(lhs),
                    op: *op,
                    rhs: Box::new(rhs),
                }
            }
        })
    }

    /// Materializes an unconsumed multiret before an exit reads registers.
    fn flush_pending_multiret(
        &mut self,
        block_id: usize,
        stmts: &mut Vec<Stmt>,
        pending_multiret: &mut Option<MultiRet>,
    ) {
        let Some(multiret) = pending_multiret.take() else {
            return;
        };

        flush_multiret(multiret, block_id, &mut self.ssa, stmts);
    }

    /// Finds loop-carried register symbols that should canonicalize together.
    fn collect_loop_carried_links(&mut self) {
        let live_in_regs =
            compute_live_in_registers(&self.blocks, self.raw_blocks, self.graph, &self.ssa);

        for (src, targets) in self.graph.iter().map(|n| (n, self.graph.successors(n))) {
            for &target in targets {
                // Luau bytecode is emitted in block order, so loop backedges target an
                // earlier/equal block. Forward edges cannot introduce loop-carried versions.
                if target > src {
                    continue;
                }

                if matches!(
                    &self.raw_blocks[src].exit,
                    RawBlockExit::FornLoop { .. } | RawBlockExit::ForgLoop { .. }
                ) {
                    continue;
                }

                let loop_body = self.collect_loop_body(src, target);
                let written_regs = self.collect_loop_written_regs(&loop_body);
                let loop_live_out =
                    compute_loop_live_out_regs(&loop_body, &self.graph, &live_in_regs);

                for u in 0..self.proto.num_upvals {
                    let _ = self.ssa.read_upval(target, u);
                }

                for reg in written_regs.iter() {
                    if live_in_regs[target].contains(reg)
                        || loop_live_out.contains(reg)
                        || (target == 0 && reg < self.proto.num_params)
                    {
                        let target_sym = self.ssa.read_reg(target, reg);
                        let source_sym = self.ssa.read_reg(src, reg);
                        if target_sym != source_sym {
                            self.loop_carried_links.push((target_sym, source_sym));
                        }
                    }
                }
            }
        }
    }

    /// Collects the natural loop body for a back edge from `src` to `target`.
    fn collect_loop_body(&self, src: usize, target: usize) -> HashSet<usize> {
        let mut loop_body = HashSet::new();
        loop_body.insert(target);
        let mut worklist = vec![src];
        while let Some(b) = worklist.pop() {
            if loop_body.insert(b) {
                worklist.extend(self.graph.predecessors(b));
            }
        }
        loop_body
    }

    /// Finds physical registers written anywhere in a loop body.
    fn collect_loop_written_regs(&self, loop_body: &HashSet<usize>) -> RegSet {
        let mut written_regs = RegSet::new();
        for &block_id in loop_body {
            for decoded in &self.proto.instrs[self.raw_blocks[block_id].instr_range.clone()] {
                written_regs.extend(decoded.instr.written_registers());
            }
            written_regs.extend(self.raw_blocks[block_id].exit_writes.clone());
        }
        written_regs
    }

    /// Seals SSA, emits nontrivial Phi nodes, resolves trivial aliases, and
    /// returns bytecode facts keyed by the surviving SSA versions.
    fn finish_ssa(&mut self) -> HashMap<SymbolId, TypeId> {
        self.ssa.seal_blocks();
        self.ssa.finish(&mut self.blocks);
        resolve_ssa_aliases(&mut self.blocks, &self.ssa);

        for symbol in &mut self.params {
            *symbol = self.ssa.resolve(*symbol);
        }
        for symbol in &mut self.upvalues {
            *symbol = self.ssa.resolve(*symbol);
        }
        for (target, source) in &mut self.loop_carried_links {
            *target = self.ssa.resolve(*target);
            *source = self.ssa.resolve(*source);
        }
        self.loop_carried_links
            .retain(|(target, source)| target != source);

        self.ssa
            .arena()
            .iter()
            .filter_map(|(id, symbol)| symbol.ty.map(|ty| (self.ssa.resolve(id), ty)))
            .fold(HashMap::new(), |mut facts, (symbol, ty)| {
                facts
                    .entry(symbol)
                    .and_modify(|existing| *existing = self.type_store.union(*existing, ty))
                    .or_insert(ty);
                facts
            })
    }

    /// Builds named locals from debug records and their surviving SSA versions.
    fn named_locals(&self) -> Vec<NamedLocal> {
        let mut symbols_by_local = vec![Vec::new(); self.proto.locals.len()];
        for (id, symbol) in self.ssa.arena().iter() {
            let Some(local_index) = symbol.local_index else {
                continue;
            };
            let resolved = self.ssa.resolve(id);
            if !symbols_by_local[local_index].contains(&resolved) {
                symbols_by_local[local_index].push(resolved);
            }
        }

        self.proto
            .locals
            .iter()
            .zip(symbols_by_local)
            .filter_map(|(local, symbols)| {
                let name = self.chunk.get_string(local.name)?;
                let name = name.as_utf8()?;
                Some(NamedLocal {
                    name: name.to_owned(),
                    start_pc: local.start_pc,
                    end_pc: local.end_pc,
                    symbols,
                })
            })
            .collect()
    }

    /// Finds surviving symbols that share declared-upvalue or captured-register storage.
    fn storage_members(&self) -> (Vec<Vec<SymbolId>>, Vec<Vec<SymbolId>>) {
        let mut upvalue_storage: BTreeMap<u8, Vec<_>> = BTreeMap::new();
        let mut captured_storage: BTreeMap<(u8, u16), Vec<_>> = BTreeMap::new();

        for (id, symbol) in self.ssa.arena().iter() {
            let resolved = self.ssa.resolve(id);
            let members = match symbol.kind {
                SymbolKind::Upvalue(index) => upvalue_storage.entry(index).or_default(),
                SymbolKind::CapturedRegister { reg, generation } => {
                    captured_storage.entry((reg, generation)).or_default()
                }
                SymbolKind::Register(_) | SymbolKind::Param(_) => continue,
            };
            if !members.contains(&resolved) {
                members.push(resolved);
            }
        }

        let upvalue_storage = upvalue_storage
            .into_values()
            .filter(|members| members.len() > 1)
            .collect();
        let captured_storage = captured_storage
            .into_values()
            .filter(|members| members.len() > 1)
            .collect();
        (upvalue_storage, captured_storage)
    }

    /// Applies exit writes to the SSA block, writing each register in `exit_writes` to a fresh symbol.
    fn apply_exit_writes(&mut self, block_id: usize, exit_pc: Option<u32>, exit_writes: &[u8]) {
        for &reg in exit_writes {
            let ty = exit_pc.and_then(|pc| self.type_context.local_at(reg, pc));
            let local_index = exit_pc.and_then(|pc| self.proto.local_index_after(reg, pc));
            let sym = self
                .ssa
                .alloc_symbol(Symbol::reg(reg).with_type(ty).with_local_index(local_index));
            self.ssa.write_reg(block_id, reg, sym);
        }
    }
}

/// Rewrites every CFG reference through the trivial-alias relation owned by SSA.
fn resolve_ssa_aliases<G: GraphView>(blocks: &mut [Block], ssa: &Ssa<'_, G>) {
    let mut resolver = SsaAliasResolver { ssa };
    for block in blocks {
        resolver.visit_block(block);
    }
}

/// Visitor that removes temporary IDs belonging to trivial Phi nodes.
struct SsaAliasResolver<'ssa, 'cfg, G: GraphView> {
    /// Completed SSA state containing the trivial-alias relation.
    ssa: &'ssa Ssa<'cfg, G>,
}

impl<G: GraphView> VisitorMut for SsaAliasResolver<'_, '_, G> {
    /// Resolves one symbol without coalescing distinct nontrivial versions.
    fn visit_symbol(&mut self, symbol: &mut SymbolId) {
        *symbol = self.ssa.resolve(*symbol);
    }

    /// Resolves a closure capture owned by the enclosing function.
    fn visit_capture(&mut self, _index: usize, capture: &mut Capture) {
        self.visit_symbol(capture.symbol_mut());
    }

    /// Resolves the target and operands of a synthetic Phi statement.
    fn visit_phi(&mut self, phi: &mut PhiNode) {
        self.visit_symbol(&mut phi.target);
        for (_, operand) in &mut phi.operands {
            self.visit_symbol(operand);
        }
    }
}

/// Builds a lookup from SSA symbols to their original physical register.
fn symbol_register_map<G: GraphView>(ssa: &Ssa<'_, G>) -> HashMap<SymbolId, u8> {
    ssa.arena()
        .iter()
        .filter_map(|(id, sym)| match sym.kind {
            SymbolKind::Register(reg) | SymbolKind::CapturedRegister { reg, .. } => Some((id, reg)),
            _ => None,
        })
        .collect()
}

/// Visitor that records register reads before any same-block definition.
struct RegUseCollector<'a, 'b> {
    reg_of: &'a HashMap<SymbolId, u8>,
    uses: &'b mut RegSet,
    seen_defs: &'a RegSet,
}

impl Visitor for RegUseCollector<'_, '_> {
    /// Records exit operands that are reads while ignoring loop-produced definitions.
    fn visit_block_exit(&mut self, exit: &BlockExit) {
        match exit {
            BlockExit::CondJump { cond, .. } => self.visit_expr(cond),
            BlockExit::FornPrep {
                start, end, step, ..
            } => {
                self.visit_expr(start);
                self.visit_expr(end);
                self.visit_expr(step);
            }
            BlockExit::ForgPrep { exprs, .. } => {
                for expr in exprs {
                    self.visit_expr(expr);
                }
            }
            BlockExit::Return(values) => self.visit_value_pack(values),
            BlockExit::Jump(_)
            | BlockExit::Fallthrough(_)
            | BlockExit::FornLoop { .. }
            | BlockExit::ForgLoop { .. } => {}
        }
    }

    fn visit_symbol(&mut self, sym: SymbolId) {
        if let Some(&reg) = self.reg_of.get(&sym)
            && !self.seen_defs.contains(reg)
        {
            self.uses.set(reg);
        }
    }

    fn visit_capture(&mut self, _index: usize, capture: Capture) {
        self.visit_symbol(capture.symbol());
    }
}

/// Visitor that records statement-level register uses and definitions.
struct RegUseDefCollector<'a, 'b, 'c> {
    reg_of: &'a HashMap<SymbolId, u8>,
    uses: &'b mut RegSet,
    defs: &'b mut RegSet,
    seen_defs: &'c mut RegSet,
}

impl RegUseDefCollector<'_, '_, '_> {
    /// Records a register use unless that register was already defined locally.
    fn note_use(&mut self, sym: SymbolId) {
        if let Some(&reg) = self.reg_of.get(&sym)
            && !self.seen_defs.contains(reg)
        {
            self.uses.set(reg);
        }
    }

    /// Records a register definition and suppresses later same-block live-in uses.
    fn note_def(&mut self, sym: SymbolId) {
        if let Some(&reg) = self.reg_of.get(&sym) {
            self.defs.set(reg);
            self.seen_defs.set(reg);
        }
    }

    /// Treats plain symbol lvalues as definitions and complex lvalues as reads.
    fn visit_lvalue_def(&mut self, lvalue: &Expr) {
        match lvalue {
            Expr::Symbol(sym) => self.note_def(*sym),
            other => self.visit_expr(other),
        }
    }
}

impl Visitor for RegUseDefCollector<'_, '_, '_> {
    /// Records ordinary symbol occurrences as reads.
    fn visit_symbol(&mut self, sym: SymbolId) {
        self.note_use(sym);
    }

    /// Captures read their captured symbol for live-in purposes.
    fn visit_capture(&mut self, _index: usize, capture: Capture) {
        self.note_use(capture.symbol());
    }

    /// Applies statement-level use/def ordering before expression traversal.
    fn visit_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assign { left, value } => {
                self.visit_expr(value);
                self.visit_lvalue_def(left);
            }
            Stmt::AssignMany { left, values } => {
                self.visit_value_pack(values);
                for lvalue in left {
                    self.visit_lvalue_def(lvalue);
                }
            }
            Stmt::Call(expr) => self.visit_expr(expr),
            Stmt::SetList { table, values, .. } => {
                self.note_use(*table);
                self.visit_value_pack(values);
            }
            Stmt::Phi(phi) => self.note_def(phi.target),
        }
    }
}

/// Records register reads performed by a block exit.
fn collect_exit_reg_uses(
    exit: &BlockExit,
    reg_of: &HashMap<SymbolId, u8>,
    uses: &mut RegSet,
    seen_defs: &RegSet,
) {
    RegUseCollector {
        reg_of,
        uses,
        seen_defs,
    }
    .visit_block_exit(exit);
}

/// Computes the registers each lifted block needs on entry.
fn compute_live_in_registers<G: GraphView>(
    blocks: &[Block],
    raw_blocks: &[RawBlock],
    graph: &G,
    ssa: &Ssa<'_, G>,
) -> Vec<RegSet> {
    let reg_of = symbol_register_map(ssa);

    let mut block_uses = vec![RegSet::new(); blocks.len()];
    let mut block_defs = vec![RegSet::new(); blocks.len()];

    for (block_idx, block) in blocks.iter().enumerate() {
        let mut seen_defs = RegSet::new();

        for stmt in &block.stmts {
            RegUseDefCollector {
                reg_of: &reg_of,
                uses: &mut block_uses[block_idx],
                defs: &mut block_defs[block_idx],
                seen_defs: &mut seen_defs,
            }
            .visit_stmt(stmt);
        }

        collect_exit_reg_uses(&block.exit, &reg_of, &mut block_uses[block_idx], &seen_defs);

        block_defs[block_idx].extend(raw_blocks[block_idx].exit_writes.iter().copied());
    }

    let mut live_in = vec![RegSet::new(); blocks.len()];
    let mut live_out = vec![RegSet::new(); blocks.len()];

    let mut changed = true;
    while changed {
        changed = false;

        for block_idx in (0..blocks.len()).rev() {
            let mut new_out = RegSet::new();
            for &succ in graph.successors(block_idx) {
                new_out |= &live_in[succ];
            }

            let mut new_in = block_uses[block_idx].clone();
            new_in.extend(
                new_out
                    .iter()
                    .filter(|&reg| !block_defs[block_idx].contains(reg)),
            );

            if new_out != live_out[block_idx] || new_in != live_in[block_idx] {
                live_out[block_idx] = new_out;
                live_in[block_idx] = new_in;
                changed = true;
            }
        }
    }

    live_in
}

fn compute_loop_live_out_regs<G: GraphView>(
    loop_body: &HashSet<usize>,
    graph: &G,
    live_in_regs: &[RegSet],
) -> RegSet {
    let mut live_out = RegSet::new();

    for &block_id in loop_body {
        for &succ in graph.successors(block_id) {
            if !loop_body.contains(&succ) {
                live_out |= &live_in_regs[succ];
            }
        }
    }

    live_out
}
