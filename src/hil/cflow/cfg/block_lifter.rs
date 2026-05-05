use std::collections::{HashMap, HashSet};

use smallvec::SmallVec;

use crate::{
    common::Spanned,
    disasm::Proto,
    hil::{
        cflow::{
            common::RegSet,
            graph::{AdjGraph, GraphView},
            union_find::UnionFind,
        },
        common::{const_expr, decoded_count, reg_add, reg_range},
        ir::{HilExpr, HilStmt, PhiNode},
        lifter::{
            LiftContext, MultiRet, flush_multiret, lift,
            ssa::{Ssa as LifterSsa, Symbol, SymbolId, SymbolKind},
        },
        visitor::{Visitor, VisitorMut},
    },
    il::Count,
};

use super::{Block, BlockExit, Cond, CondRhs, RawBlock, RawBlockExit};

/// Blocks, parameter symbols, and upvalue symbols produced by SSA construction.
pub(super) struct BuildResult {
    pub blocks: Vec<Block>,
    pub params: Vec<SymbolId>,
    pub upvalues: Vec<SymbolId>,
}

/// Lifts raw blocks into HIL blocks and resolves temporary SSA versions.
///
/// This phase owns the mutable SSA algorithm because block lifting, synthetic
/// terminator writes, loop-carried repairs, and final symbol canonicalization
/// are tightly coupled.
pub(super) fn build_blocks(
    proto: &Proto,
    all_protos: &[Proto],
    raw_blocks: &[RawBlock],
    successors: &[Vec<usize>],
    predecessors: &[Vec<usize>],
) -> BuildResult {
    BlockBuilder::new(proto, all_protos, raw_blocks, successors, predecessors).build()
}

/// Mutable state for the SSA-backed CFG block lifting phase.
struct BlockBuilder<'a> {
    proto: &'a Proto,
    all_protos: &'a [Proto],
    raw_blocks: &'a [RawBlock],
    successors: &'a [Vec<usize>],
    predecessors: &'a [Vec<usize>],
    blocks: Vec<Block>,
    ssa: LifterSsa<'a>,
    params: Vec<SymbolId>,
    upvalues: Vec<SymbolId>,
    loop_carried_versions: Vec<(SymbolId, SymbolId)>,
}

impl<'a> BlockBuilder<'a> {
    /// Creates the phase state around immutable CFG inputs and fresh SSA state.
    fn new(
        proto: &'a Proto,
        all_protos: &'a [Proto],
        raw_blocks: &'a [RawBlock],
        successors: &'a [Vec<usize>],
        predecessors: &'a [Vec<usize>],
    ) -> Self {
        Self {
            proto,
            all_protos,
            raw_blocks,
            successors,
            predecessors,
            blocks: vec![Block::dummy(); raw_blocks.len()],
            ssa: LifterSsa::new(predecessors),
            params: Vec::with_capacity(proto.num_params as usize),
            upvalues: Vec::with_capacity(proto.num_upvals as usize),
            loop_carried_versions: Vec::new(),
        }
    }

    /// Runs SSA-backed lifting through final symbol canonicalization.
    fn build(mut self) -> BuildResult {
        self.initialize_entry_symbols();
        self.lift_blocks();
        self.collect_loop_carried_versions();
        self.finalize();

        BuildResult {
            blocks: self.blocks,
            params: self.params,
            upvalues: self.upvalues,
        }
    }

    /// Seeds entry-block SSA state for parameters and declared upvalues.
    fn initialize_entry_symbols(&mut self) {
        for i in 0..self.proto.num_params {
            let sym = self.ssa.alloc_symbol(Symbol::param(i));
            self.ssa.write_reg(0, i, sym);
            self.params.push(sym);
        }

        for i in 0..self.proto.num_upvals {
            let sym = self.ssa.alloc_symbol(Symbol::upval(i));
            self.ssa.write_upval(0, i, sym);
            self.upvalues.push(sym);
        }
    }

    /// Lifts reachable raw blocks in reverse postorder.
    fn lift_blocks(&mut self) {
        let graph = AdjGraph::new(0, self.successors, self.predecessors);

        for block_id in graph.compute_rpo() {
            self.lift_block(block_id);
        }
    }

    /// Lifts one raw block body and lowers its raw terminator into a HIL exit.
    fn lift_block(&mut self, block_id: usize) {
        let raw_block = &self.raw_blocks[block_id];
        let (mut stmts, mut pending_multiret) = lift(LiftContext {
            instrs: &self.proto.instrs[raw_block.instr_range.clone()],
            consts: &self.proto.consts,
            parent_proto: self.proto,
            protos: self.all_protos,
            ssa: &mut self.ssa,
            block_idx: block_id,
        });

        let exit = self.lower_exit(block_id, &mut stmts, &mut pending_multiret);

        debug_assert!(
            pending_multiret.is_none(),
            "non-variadic exit lowering must consume or flush pending multiret"
        );

        self.blocks[block_id] = Block { stmts, exit };
        self.ssa.mark_filled(block_id);
    }

    /// Converts a raw terminator into a lifted exit, reading any needed SSA values.
    fn lower_exit(
        &mut self,
        block_id: usize,
        stmts: &mut Vec<Spanned<HilStmt>>,
        pending_multiret: &mut Option<MultiRet>,
    ) -> BlockExit {
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
        match exit {
            RawBlockExit::Jump(t) => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                self.apply_exit_writes(block_id, exit_writes);
                BlockExit::Jump(*t)
            }
            RawBlockExit::Fallthrough(t) => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                self.apply_exit_writes(block_id, exit_writes);
                BlockExit::Fallthrough(*t)
            }
            RawBlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                let cond = self.lower_cond(block_id, cond);
                self.apply_exit_writes(block_id, exit_writes);
                BlockExit::CondJump {
                    cond,
                    then_block: *then_block,
                    else_block: *else_block,
                }
            }
            RawBlockExit::FornPrep {
                base,
                body_block,
                exit_block,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);

                // These are current-block reads. They must happen before exit_writes.
                let start = self.ssa.read_reg(block_id, reg_add(*base, 2));
                let end = self.ssa.read_reg(block_id, reg_add(*base, 0));
                let step = self.ssa.read_reg(block_id, reg_add(*base, 1));

                // These are terminator/edge writes.
                self.apply_exit_writes(block_id, exit_writes);

                // This is a successor/body-block read. It must happen after exit_writes.
                let var = self.ssa.read_reg(*body_block, reg_add(*base, 2));

                BlockExit::FornPrep {
                    base: *base,
                    body_block: *body_block,
                    exit_block: *exit_block,
                    var,
                    start: HilExpr::Symbol(start),
                    end: HilExpr::Symbol(end),
                    step: HilExpr::Symbol(step),
                }
            }
            RawBlockExit::FornLoop {
                base,
                body_block,
                exit_block,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                self.apply_exit_writes(block_id, exit_writes);
                BlockExit::FornLoop {
                    base: *base,
                    body_block: *body_block,
                    exit_block: *exit_block,
                }
            }
            RawBlockExit::ForgPrep {
                base,
                body_block,
                exit_block,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                let exprs = [
                    HilExpr::Symbol(self.ssa.read_reg(block_id, reg_add(*base, 0))),
                    HilExpr::Symbol(self.ssa.read_reg(block_id, reg_add(*base, 1))),
                    HilExpr::Symbol(self.ssa.read_reg(block_id, reg_add(*base, 2))),
                ];
                self.apply_exit_writes(block_id, exit_writes);
                BlockExit::ForgPrep {
                    base: *base,
                    body_block: *body_block,
                    exit_block: *exit_block,
                    exprs,
                }
            }
            RawBlockExit::ForgLoop {
                base,
                body_block,
                exit_block,
                result_count,
            } => {
                self.flush_pending_multiret(block_id, stmts, pending_multiret);
                self.apply_exit_writes(block_id, exit_writes);
                BlockExit::ForgLoop {
                    base: *base,
                    body_block: *body_block,
                    exit_block: *exit_block,
                    vars: (0..*result_count)
                        .map(|i| {
                            self.ssa
                                .read_reg(*body_block, reg_add(reg_add(*base, 3), i as u8))
                        })
                        .collect(),
                }
            }
            RawBlockExit::Return { base, count } => {
                assert!(
                    exit_writes.is_empty(),
                    "RETURN must not have synthetic exit writes: {exit_writes:?}"
                );

                match decoded_count(*count) {
                    Count::Variadic => {
                        assert!(
                            exit_writes.is_empty(),
                            "variadic return should not have synthetic exit writes"
                        );

                        let Some(multiret) = pending_multiret.take() else {
                            panic!("variadic return without pending multiret");
                        };

                        assert!(
                            multiret.base >= *base,
                            "pending multiret base {} is before variadic return base {}",
                            base,
                            multiret.base,
                        );

                        let mut rets = SmallVec::new();
                        for i in *base..multiret.base {
                            rets.push(HilExpr::Symbol(self.ssa.read_reg(block_id, i)));
                        }
                        rets.push(multiret.expr.node);

                        BlockExit::Return(rets)
                    }
                    Count::Number(n) => {
                        self.flush_pending_multiret(block_id, stmts, pending_multiret);

                        assert!(
                            exit_writes.is_empty(),
                            "fixed return should not have synthetic exit writes"
                        );

                        let rets = reg_range(*base, n)
                            .map(|i| HilExpr::Symbol(self.ssa.read_reg(block_id, i)))
                            .collect();

                        BlockExit::Return(rets)
                    }
                }
            }
        }
    }

    /// Converts a raw register/constant condition into a HIL expression.
    fn lower_cond(&mut self, block_id: usize, cond: &Cond) -> HilExpr {
        match cond {
            Cond::Unary(reg) => HilExpr::Symbol(self.ssa.read_reg(block_id, *reg)),
            Cond::Binary { lhs, op, rhs } => {
                let lhs = HilExpr::Symbol(self.ssa.read_reg(block_id, *lhs));
                let rhs = match rhs {
                    CondRhs::Reg(reg) => HilExpr::Symbol(self.ssa.read_reg(block_id, *reg)),
                    CondRhs::Const(idx) => const_expr(&self.proto.consts, *idx),
                    CondRhs::Nil => HilExpr::Nil,
                    CondRhs::Bool(value) => HilExpr::Bool(*value),
                };

                HilExpr::Binary {
                    lhs: Box::new(lhs),
                    op: *op,
                    rhs: Box::new(rhs),
                }
            }
        }
    }

    /// Materializes an unconsumed multiret before an exit reads registers.
    fn flush_pending_multiret(
        &mut self,
        block_id: usize,
        stmts: &mut Vec<Spanned<HilStmt>>,
        pending_multiret: &mut Option<MultiRet>,
    ) {
        let Some(multiret) = pending_multiret.take() else {
            return;
        };

        flush_multiret(multiret, block_id, &mut self.ssa, stmts);
    }

    /// Finds loop-carried register versions that should canonicalize together.
    fn collect_loop_carried_versions(&mut self) {
        let live_in_regs =
            compute_live_in_registers(&self.blocks, self.raw_blocks, self.successors, &self.ssa);

        for (src, targets) in self.successors.iter().enumerate() {
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
                    compute_loop_live_out_regs(&loop_body, self.successors, &live_in_regs);

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
                            self.loop_carried_versions.push((target_sym, source_sym));
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
                worklist.extend(&self.predecessors[b]);
            }
        }
        loop_body
    }

    /// Finds physical registers written anywhere in a loop body.
    fn collect_loop_written_regs(&self, loop_body: &HashSet<usize>) -> RegSet {
        let mut written_regs = RegSet::new();
        for &block_id in loop_body {
            for sd in &self.proto.instrs[self.raw_blocks[block_id].instr_range.clone()] {
                written_regs.extend(sd.node.written_registers());
            }
            written_regs.extend(self.raw_blocks[block_id].exit_writes.clone());
        }
        written_regs
    }

    /// Seals SSA, emits Phi nodes, and rewrites all symbols to canonical IDs.
    fn finalize(&mut self) {
        self.ssa.seal_blocks();
        self.ssa.finish(&mut self.blocks);

        let mut disjoint_set = UnionFind::new();
        for (target, source) in self.loop_carried_versions.drain(..) {
            disjoint_set.union(target, source);
        }

        self.union_phi_versions(&mut disjoint_set);
        self.union_storage_versions(&mut disjoint_set);
        resolve_ssa_symbols(&mut self.blocks, &self.ssa, &mut disjoint_set);

        for sym in &mut self.params {
            *sym = disjoint_set.find(self.ssa.resolve(*sym));
        }
        for sym in &mut self.upvalues {
            *sym = disjoint_set.find(self.ssa.resolve(*sym));
        }
    }

    /// Unions Phi targets with operands except for loop-preheader loop variables.
    fn union_phi_versions(&self, disjoint_set: &mut UnionFind<SymbolId>) {
        for (block_idx, block) in self.blocks.iter().enumerate() {
            for stmt in &block.stmts {
                if let HilStmt::Phi(phi) = &stmt.node {
                    for (pred_block, operand) in &phi.operands {
                        if is_loop_header_loop_var_operand(
                            &self.blocks,
                            block_idx,
                            *pred_block,
                            phi.target,
                        ) {
                            continue;
                        }
                        disjoint_set.union(phi.target, *operand);
                    }
                }
            }
        }
    }

    /// Unions storage versions that represent one logical upvalue or capture.
    fn union_storage_versions(&self, disjoint_set: &mut UnionFind<SymbolId>) {
        let mut upval_versions: HashMap<_, Vec<_>> = HashMap::new();
        let mut captured_versions: HashMap<_, Vec<_>> = HashMap::new();

        for (id, symbol) in self.ssa.arena().iter() {
            match symbol.kind {
                SymbolKind::Upvalue(idx) => {
                    upval_versions.entry(idx).or_default().push(id);
                }
                SymbolKind::CapturedRegister { reg, generation } => {
                    captured_versions
                        .entry((reg, generation))
                        .or_default()
                        .push(id);
                }
                SymbolKind::Register(_) | SymbolKind::Param(_) => {}
            }
        }

        union_version_groups(upval_versions.values().map(Vec::as_slice), disjoint_set);
        union_version_groups(captured_versions.values().map(Vec::as_slice), disjoint_set);
    }

    /// Applies exit writes to the SSA block, writing each register in `exit_writes` to a fresh symbol.
    fn apply_exit_writes(&mut self, block_id: usize, exit_writes: &[u8]) {
        for &reg in exit_writes {
            let sym = self.ssa.alloc_symbol(Symbol::reg(reg));
            self.ssa.write_reg(block_id, reg, sym);
        }
    }
}

/// Unions each symbol group into the first symbol in that group.
fn union_version_groups<'a, I>(groups: I, uf: &mut UnionFind<SymbolId>)
where
    I: IntoIterator<Item = &'a [SymbolId]>,
{
    for versions in groups {
        let Some((&first, rest)) = versions.split_first() else {
            continue;
        };

        for &version in rest {
            uf.union(first, version);
        }
    }
}

/// Rewrites all SSA temporary symbols in lifted blocks to their canonical IDs.
fn resolve_ssa_symbols(blocks: &mut [Block], ssa: &LifterSsa<'_>, djs: &mut UnionFind<SymbolId>) {
    let mut resolver = SymbolResolver { ssa, djs };
    for block in blocks {
        for stmt in &mut block.stmts {
            resolver.visit_stmt(&mut stmt.node);
        }
        visit_block_exit_symbols_mut(&mut block.exit, &mut resolver);
    }
}

/// Visitor that canonicalizes every symbol reference it sees.
struct SymbolResolver<'ssa, 'cfg, 'uf> {
    ssa: &'ssa LifterSsa<'cfg>,
    djs: &'uf mut UnionFind<SymbolId>,
}

impl VisitorMut for SymbolResolver<'_, '_, '_> {
    fn visit_symbol(&mut self, sym: &mut SymbolId) {
        let resolved = self.ssa.resolve(*sym);
        *sym = self.djs.find(resolved);
    }

    fn visit_capture(&mut self, _index: usize, sym: &mut SymbolId) {
        self.visit_symbol(sym);
    }

    /// Phi nodes are synthetic statements, so resolve both target and operands.
    fn visit_phi(&mut self, phi: &mut PhiNode) {
        self.visit_symbol(&mut phi.target);
        for (_, op) in &mut phi.operands {
            self.visit_symbol(op);
        }
    }
}

/// Visits symbols embedded in CFG exits, which are outside the generic HIL tree.
fn visit_block_exit_symbols_mut<V: VisitorMut + ?Sized>(exit: &mut BlockExit, visitor: &mut V) {
    match exit {
        BlockExit::CondJump { cond, .. } => {
            visitor.visit_expr(cond);
        }
        BlockExit::FornPrep {
            var,
            start,
            end,
            step,
            ..
        } => {
            visitor.visit_symbol(var);
            visitor.visit_expr(start);
            visitor.visit_expr(end);
            visitor.visit_expr(step);
        }
        BlockExit::ForgPrep { exprs, .. } => {
            for expr in exprs {
                visitor.visit_expr(expr);
            }
        }
        BlockExit::ForgLoop { vars, .. } => {
            for var in vars {
                visitor.visit_symbol(var);
            }
        }
        BlockExit::Return(values) => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
        BlockExit::Jump(_) | BlockExit::Fallthrough(_) | BlockExit::FornLoop { .. } => {}
    }
}

/// Builds a lookup from SSA symbols to their original physical register.
fn symbol_register_map(ssa: &LifterSsa<'_>) -> HashMap<SymbolId, u8> {
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
    fn visit_symbol(&mut self, sym: SymbolId) {
        if let Some(&reg) = self.reg_of.get(&sym)
            && !self.seen_defs.contains(reg)
        {
            self.uses.set(reg);
        }
    }

    fn visit_capture(&mut self, _index: usize, sym: SymbolId) {
        self.visit_symbol(sym);
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
    fn visit_lvalue_def(&mut self, lvalue: &HilExpr) {
        match lvalue {
            HilExpr::Symbol(sym) => self.note_def(*sym),
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
    fn visit_capture(&mut self, _index: usize, sym: SymbolId) {
        self.note_use(sym);
    }

    /// Applies statement-level use/def ordering before expression traversal.
    fn visit_stmt(&mut self, stmt: &HilStmt) {
        match stmt {
            HilStmt::Assign { left, value } => {
                self.visit_expr(value);
                self.visit_lvalue_def(left);
            }
            HilStmt::AssignMany { left, value } => {
                self.visit_expr(value);
                for lvalue in left {
                    self.visit_lvalue_def(lvalue);
                }
            }
            HilStmt::Call(expr) => self.visit_expr(expr),
            HilStmt::SetList { table, values, .. } => {
                self.note_use(*table);
                for value in values {
                    self.visit_expr(value);
                }
            }
            HilStmt::Phi(phi) => self.note_def(phi.target),
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
    match exit {
        BlockExit::CondJump { cond, .. } => {
            RegUseCollector {
                reg_of,
                uses,
                seen_defs,
            }
            .visit_expr(cond);
        }
        BlockExit::FornPrep {
            start, end, step, ..
        } => {
            let mut collector = RegUseCollector {
                reg_of,
                uses,
                seen_defs,
            };
            collector.visit_expr(start);
            collector.visit_expr(end);
            collector.visit_expr(step);
        }
        BlockExit::ForgPrep { exprs, .. } => {
            let mut collector = RegUseCollector {
                reg_of,
                uses,
                seen_defs,
            };
            for expr in exprs {
                collector.visit_expr(expr);
            }
        }
        BlockExit::Return(values) => {
            let mut collector = RegUseCollector {
                reg_of,
                uses,
                seen_defs,
            };
            for value in values {
                collector.visit_expr(value);
            }
        }
        BlockExit::Jump(_)
        | BlockExit::Fallthrough(_)
        | BlockExit::FornLoop { .. }
        | BlockExit::ForgLoop { .. } => {}
    }
}

/// Computes the registers each lifted block needs on entry.
fn compute_live_in_registers(
    blocks: &[Block],
    raw_blocks: &[RawBlock],
    successors: &[Vec<usize>],
    ssa: &LifterSsa<'_>,
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
            .visit_stmt(&stmt.node);
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
            for &succ in &successors[block_idx] {
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

fn compute_loop_live_out_regs(
    loop_body: &HashSet<usize>,
    successors: &[Vec<usize>],
    live_in_regs: &[RegSet],
) -> RegSet {
    let mut live_out = RegSet::new();

    for &block_id in loop_body {
        for &succ in &successors[block_id] {
            if !loop_body.contains(&succ) {
                live_out |= &live_in_regs[succ];
            }
        }
    }

    live_out
}

/// Returns true when a Phi operand is the pre-loop value for a loop variable.
fn is_loop_header_loop_var_operand(
    blocks: &[Block],
    block_idx: usize,
    pred_block: usize,
    target: SymbolId,
) -> bool {
    let Some(pred) = blocks.get(pred_block) else {
        return false;
    };

    match &pred.exit {
        BlockExit::FornPrep {
            body_block, var, ..
        } if *body_block == block_idx => *var == target,
        BlockExit::ForgPrep {
            body_block,
            exit_block,
            ..
        } if *body_block == block_idx => blocks.get(*exit_block).is_some_and(|block| {
            matches!(
                &block.exit,
                BlockExit::ForgLoop { vars, .. } if vars.contains(&target)
            )
        }),
        _ => false,
    }
}
