mod block_lifter;

use std::{
    collections::{BTreeSet, HashSet},
    ops::Range,
};

use smallvec::SmallVec;

use crate::{
    ast::BinOp,
    common::{Spanned, ToSpanned as _},
    disasm::Proto,
    hil::{
        cflow::graph::{AdjGraph, DominatorTree, GraphView, build_graph},
        ir::{HilExpr, HilStmt, PhiNode},
        lifter::ssa::SymbolId,
    },
    il::Instr,
};

/// Represents an unlifted block
#[derive(Debug)]
pub struct RawBlock {
    /// The range of instructions indices that belong to this block, excluding the potential exit instruction.
    instr_range: Range<usize>,
    /// Registers written by an unlifted terminator instruction.
    exit_writes: SmallVec<[u8; 4]>,
    exit: RawBlockExit,
}

/// Represents an unlifted terminating edge in the block.
#[derive(Debug, Clone)]
pub enum RawBlockExit {
    Jump(usize),
    Fallthrough(usize),
    CondJump {
        cond: Cond,
        then_block: usize,
        else_block: usize,
    },
    FornPrep {
        base: u8,
        body_block: usize,
        exit_block: usize,
    },
    FornLoop {
        base: u8,
        body_block: usize,
        exit_block: usize,
    },
    ForgPrep {
        base: u8,
        body_block: usize,
        exit_block: usize,
    },
    ForgLoop {
        base: u8,
        body_block: usize,
        exit_block: usize,
        result_count: usize,
    },
    Return {
        base: u8,
        count: u8,
    },
}

impl RawBlockExit {
    /// Returns successor targets encoded in one block exit.
    #[must_use]
    fn targets(&self) -> [Option<usize>; 2] {
        match self {
            RawBlockExit::Jump(target) | RawBlockExit::Fallthrough(target) => [Some(*target), None],
            RawBlockExit::CondJump {
                then_block,
                else_block,
                ..
            } => [Some(*then_block), Some(*else_block)],
            RawBlockExit::FornPrep {
                body_block,
                exit_block,
                ..
            } => [Some(*body_block), Some(*exit_block)],
            RawBlockExit::ForgPrep { body_block, .. } => [Some(*body_block), None],
            RawBlockExit::FornLoop {
                body_block,
                exit_block,
                ..
            }
            | RawBlockExit::ForgLoop {
                body_block,
                exit_block,
                ..
            } => [Some(*body_block), Some(*exit_block)],
            RawBlockExit::Return { .. } => [None, None],
        }
    }
}

/// Represents a lifted block
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Spanned<HilStmt>>,
    pub exit: BlockExit,
}

impl Block {
    /// Creates an empty block with a dummy exit.
    pub fn dummy() -> Self {
        Self {
            stmts: Vec::new(),
            exit: BlockExit::Return(SmallVec::new()),
        }
    }

    /// Returns the exit targets of this block.
    pub fn exit_targets(&self) -> [Option<usize>; 2] {
        self.exit.targets()
    }
}

/// Represents a lifted terminating edge in the block.
#[derive(Debug, Clone)]
pub enum BlockExit {
    Jump(usize),
    Fallthrough(usize),
    CondJump {
        cond: HilExpr,
        then_block: usize,
        else_block: usize,
    },
    FornPrep {
        base: u8,
        body_block: usize,
        exit_block: usize,
        var: SymbolId,
        start: HilExpr,
        end: HilExpr,
        step: HilExpr,
    },
    FornLoop {
        base: u8,
        body_block: usize,
        exit_block: usize,
    },
    ForgPrep {
        base: u8,
        body_block: usize,
        exit_block: usize,
        exprs: [HilExpr; 3],
    },
    ForgLoop {
        base: u8,
        body_block: usize,
        exit_block: usize,
        vars: SmallVec<[SymbolId; 3]>,
    },
    Return(SmallVec<[HilExpr; 3]>),
}

impl BlockExit {
    /// Returns successor targets encoded in one block exit.
    #[must_use]
    pub fn targets(&self) -> [Option<usize>; 2] {
        match self {
            BlockExit::Jump(target) | BlockExit::Fallthrough(target) => [Some(*target), None],
            BlockExit::CondJump {
                then_block,
                else_block,
                ..
            } => [Some(*then_block), Some(*else_block)],
            BlockExit::FornPrep {
                body_block,
                exit_block,
                ..
            } => [Some(*body_block), Some(*exit_block)],
            BlockExit::ForgPrep { body_block, .. } => [Some(*body_block), None],
            BlockExit::FornLoop {
                body_block,
                exit_block,
                ..
            }
            | BlockExit::ForgLoop {
                body_block,
                exit_block,
                ..
            } => [Some(*body_block), Some(*exit_block)],
            BlockExit::Return { .. } => [None, None],
        }
    }
}

#[derive(Debug, Clone)]
pub enum CondRhs {
    /// A physical register
    Reg(u8),
    /// An index into the proto's constants
    Const(usize),
    /// Nil value
    Nil,
    /// A boolean value
    Bool(bool),
}

#[derive(Debug, Clone)]
pub enum Cond {
    /// A binary condition, i.e. `lhs op rhs`
    Binary {
        /// The physical index of the register to compare.
        lhs: u8,
        /// The operator
        op: BinOp,
        /// The right side of the binary operation.
        rhs: CondRhs,
    },
    /// A unary condition, i.e. just `x`.
    Unary(u8),
}

#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    pub blocks: Vec<Block>,
    pub entry_block: usize,

    pub successors: Vec<Vec<usize>>,
    pub predecessors: Vec<Vec<usize>>,
    pub idoms: DominatorTree,

    pub params: Vec<SymbolId>,
    pub upvalues: Vec<SymbolId>,
}

impl ControlFlowGraph {
    pub fn from_proto(proto: &Proto, all_protos: &[Proto]) -> Self {
        let instrs = proto.instrs.as_slice();

        let entries = find_block_entries(instrs);
        let raw_blocks = build_raw_blocks(&entries, instrs);

        let (successors, predecessors) = build_graph(raw_blocks.iter().map(|b| b.exit.targets()));

        let block_lifter::BuildResult {
            mut blocks,
            params,
            upvalues,
        } = block_lifter::build_blocks(proto, all_protos, &raw_blocks, &successors, &predecessors);

        loop {
            let changed_cond = fold_truthy_cond_jumps(&mut blocks);
            let changed_jump = thread_jumps(&mut blocks);
            if !changed_cond && !changed_jump {
                break;
            }
        }

        let blocks = loop {
            let (_, predecessors) = build_graph(blocks.iter().map(|b| b.exit_targets()));
            let (changed_cond, new_blocks) = fold_condition_chains(blocks, &predecessors);

            if !changed_cond {
                break new_blocks;
            }
            blocks = new_blocks;
        };

        // Rebuild after folding
        let (successors, predecessors) = build_graph(blocks.iter().map(|b| b.exit_targets()));
        let idoms = AdjGraph::new(0, &successors, &predecessors).build_idoms();

        let mut graph = Self {
            blocks,
            entry_block: 0,
            successors,
            predecessors,
            idoms,
            params,
            upvalues,
        };
        for i in 0..graph.blocks.len() {
            graph.unfold_phis(i);
        }
        graph
    }

    /// Unfolds Phi Nodes into assign statements inserted at appropriate locations.
    ///
    /// This should be ran after the graph metadata has been computed.
    fn unfold_phis(&mut self, block_idx: usize) {
        let Some(idom) = self.idoms.idom(block_idx) else {
            // This block has no immediate dominator, we can't emit the phi node
            // target declaration anywhere.
            return;
        };

        let mut loop_header_targets = HashSet::new();
        for pred_idx in &self.predecessors[block_idx] {
            match &self.blocks[*pred_idx].exit {
                BlockExit::FornPrep {
                    body_block, var, ..
                } if *body_block == block_idx => {
                    loop_header_targets.insert(*var);
                }
                BlockExit::ForgLoop {
                    body_block, vars, ..
                } if *body_block == block_idx => {
                    loop_header_targets.extend(vars.iter().copied());
                }
                _ => {}
            }
        }

        let phis: Vec<_> = self.blocks[block_idx]
            .stmts
            .extract_if(.., |stmt| matches!(stmt.node, HilStmt::Phi { .. }))
            .map(|stmt| {
                let HilStmt::Phi(PhiNode { target, operands }) = stmt.node else {
                    unreachable!();
                };

                (target, operands)
            })
            .collect();

        for (target, operands) in phis {
            // Skip unfolding phi nodes of loop header targets, as the loop itself
            // initializes the variable.
            if loop_header_targets.contains(&target) {
                continue;
            }

            if operands.iter().all(|(_, version)| *version == target) {
                continue;
            }

            // Emit the target declaration in the idom block. The structurer
            // will determine whether to make it a declaration or not.
            self.blocks[idom].stmts.push(
                HilStmt::Assign {
                    left: HilExpr::Symbol(target),
                    value: HilExpr::Nil,
                }
                .to_spanned(0),
            );

            // In each operand block insert the `target = operand` statement.
            for (op_block_idx, version) in operands {
                if version == target {
                    continue;
                }
                self.blocks[op_block_idx].stmts.push(
                    HilStmt::Assign {
                        left: HilExpr::Symbol(target),
                        value: HilExpr::Symbol(version),
                    }
                    .to_spanned(0),
                );
            }
        }
    }
}

impl GraphView for ControlFlowGraph {
    fn entry(&self) -> usize {
        self.entry_block
    }

    fn successors(&self, node: usize) -> &[usize] {
        &self.successors[node]
    }

    fn predecessors(&self, node: usize) -> &[usize] {
        &self.predecessors[node]
    }

    fn contains_node(&self, node: usize) -> bool {
        node < self.blocks.len()
    }
}

/// Returns the list of instruction indices which are block entries.
#[must_use]
pub fn find_block_entries(instrs: &[Spanned<Instr>]) -> Vec<usize> {
    let mut entries = BTreeSet::new();
    entries.insert(0);

    for (idx, sd) in instrs.iter().enumerate() {
        match sd.node {
            Instr::Return { .. } if idx + 1 < instrs.len() => {
                entries.insert(idx + 1);
            }
            Instr::FornPrep { offset, .. }
            | Instr::ForgPrep { offset, .. }
            | Instr::ForgPrepInext { offset, .. }
            | Instr::ForgPrepNext { offset, .. } => {
                entries.insert(rel_target_from_instr(idx, offset.into(), instrs));
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::FornLoop { offset, .. } | Instr::ForgLoop { offset, .. } => {
                entries.insert(rel_target_from_instr(idx, offset.into(), instrs));
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::Jump { offset }
            | Instr::JumpBack { offset }
            | Instr::JumpIf { offset, .. }
            | Instr::JumpIfNot { offset, .. } => {
                entries.insert(rel_target_from_instr(idx, offset.into(), instrs));
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::JumpX { offset } => {
                entries.insert(rel_target_from_instr(idx, offset, instrs));
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::JumpIfEq { offset, .. }
            | Instr::JumpIfLe { offset, .. }
            | Instr::JumpIfLt { offset, .. }
            | Instr::JumpIfNotEq { offset, .. }
            | Instr::JumpIfNotLe { offset, .. }
            | Instr::JumpIfNotLt { offset, .. }
            | Instr::JumpXEqKNil { offset, .. }
            | Instr::JumpXEqKB { offset, .. }
            | Instr::JumpXEqKN { offset, .. }
            | Instr::JumpXEqKS { offset, .. } => {
                entries.insert(rel_target_from_instr(idx, offset.into(), instrs));
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::LoadB { jump, .. } if jump > 0 => {
                entries.insert(rel_target_from_instr(idx, jump.into(), instrs));
            }
            _ => {}
        }
    }

    entries.into_iter().collect()
}

/// Builds raw blocks from a list of entries and instructions.
fn build_raw_blocks(entries: &[usize], instrs: &[Spanned<Instr>]) -> Vec<RawBlock> {
    let mut raw_blocks = Vec::with_capacity(entries.len());

    for (block_idx, &start) in entries.iter().enumerate() {
        let end = entries.get(block_idx + 1).copied().unwrap_or(instrs.len());

        let Some(last_instr) = instrs
            .get(end.saturating_sub(1))
            .map(|spanned| spanned.node)
        else {
            continue;
        };

        let (body_end, exit_instr) = if last_instr.is_branch_exit() {
            (end - 1, Some(last_instr))
        } else if matches!(last_instr, Instr::LoadB { jump, .. } if jump > 0) {
            // LoadB still needs to be lifted to assign the boolean
            (end, Some(last_instr))
        } else {
            (end, None)
        };

        let exit_writes = if last_instr.is_branch_exit() {
            last_instr.written_registers()
        } else {
            SmallVec::new()
        };

        let exit_instr_idx = end.saturating_sub(1);
        let exit = match exit_instr {
            Some(Instr::Return { base, count }) => RawBlockExit::Return { base, count },
            Some(Instr::Jump { offset }) | Some(Instr::JumpBack { offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::Jump(pc_to_block_idx(entries, target))
            }
            Some(Instr::JumpX { offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset, instrs);
                RawBlockExit::Jump(pc_to_block_idx(entries, target))
            }
            Some(Instr::JumpIfNotLt { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Lt,
                        rhs: CondRhs::Reg(aux),
                    },
                    then_block: block_idx + 1,
                    else_block: pc_to_block_idx(entries, target),
                }
            }
            Some(Instr::JumpIf { reg, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::CondJump {
                    cond: Cond::Unary(reg),
                    then_block: pc_to_block_idx(entries, target),
                    else_block: block_idx + 1,
                }
            }
            Some(Instr::JumpIfNot { reg, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::CondJump {
                    cond: Cond::Unary(reg),
                    then_block: block_idx + 1,
                    else_block: pc_to_block_idx(entries, target),
                }
            }
            Some(Instr::JumpIfEq { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Eq,
                        rhs: CondRhs::Reg(aux),
                    },
                    then_block: pc_to_block_idx(entries, target),
                    else_block: block_idx + 1,
                }
            }
            Some(Instr::JumpIfNotEq { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Ne,
                        rhs: CondRhs::Reg(aux),
                    },
                    then_block: pc_to_block_idx(entries, target),
                    else_block: block_idx + 1,
                }
            }
            Some(Instr::JumpIfLe { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Lte,
                        rhs: CondRhs::Reg(aux),
                    },
                    then_block: pc_to_block_idx(entries, target),
                    else_block: block_idx + 1,
                }
            }
            Some(Instr::JumpIfNotLe { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Lte,
                        rhs: CondRhs::Reg(aux),
                    },
                    then_block: block_idx + 1,
                    else_block: pc_to_block_idx(entries, target),
                }
            }
            Some(Instr::JumpIfLt { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Lt,
                        rhs: CondRhs::Reg(aux),
                    },
                    then_block: pc_to_block_idx(entries, target),
                    else_block: block_idx + 1,
                }
            }
            Some(Instr::JumpXEqKNil {
                reg,
                invert,
                offset,
            }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                let (then_block, else_block) = if invert {
                    (block_idx + 1, pc_to_block_idx(entries, target))
                } else {
                    (pc_to_block_idx(entries, target), block_idx + 1)
                };
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Eq,
                        rhs: CondRhs::Nil,
                    },
                    then_block,
                    else_block,
                }
            }
            Some(Instr::JumpXEqKB {
                reg,
                k,
                invert,
                offset,
            }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                let (then_block, else_block) = if invert {
                    (block_idx + 1, pc_to_block_idx(entries, target))
                } else {
                    (pc_to_block_idx(entries, target), block_idx + 1)
                };
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Eq,
                        rhs: CondRhs::Bool(k),
                    },
                    then_block,
                    else_block,
                }
            }
            Some(Instr::JumpXEqKN {
                reg,
                k,
                invert,
                offset,
            })
            | Some(Instr::JumpXEqKS {
                reg,
                k,
                invert,
                offset,
            }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                let (then_block, else_block) = if invert {
                    (block_idx + 1, pc_to_block_idx(entries, target))
                } else {
                    (pc_to_block_idx(entries, target), block_idx + 1)
                };
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Eq,
                        rhs: CondRhs::Const(k as usize),
                    },
                    then_block,
                    else_block,
                }
            }
            Some(Instr::FornPrep { base, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::FornPrep {
                    base,
                    body_block: block_idx + 1,
                    exit_block: pc_to_block_idx(entries, target),
                }
            }
            Some(Instr::FornLoop { base, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::FornLoop {
                    base,
                    body_block: pc_to_block_idx(entries, target),
                    exit_block: block_idx + 1,
                }
            }
            Some(Instr::ForgPrep { base, offset })
            | Some(Instr::ForgPrepInext { base, offset })
            | Some(Instr::ForgPrepNext { base, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::ForgPrep {
                    base,
                    body_block: block_idx + 1,
                    exit_block: pc_to_block_idx(entries, target),
                }
            }
            Some(Instr::ForgLoop {
                base,
                offset,
                var_count,
                ..
            }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                RawBlockExit::ForgLoop {
                    base,
                    body_block: pc_to_block_idx(entries, target),
                    exit_block: block_idx + 1,
                    result_count: usize::from(var_count),
                }
            }
            Some(Instr::LoadB { jump, .. }) if jump > 0 => {
                let target = rel_target_from_instr(exit_instr_idx, jump.into(), instrs);
                RawBlockExit::Jump(pc_to_block_idx(entries, target))
            }
            _ => RawBlockExit::Fallthrough(block_idx + 1),
        };

        raw_blocks.push(RawBlock {
            instr_range: start..body_end,
            exit_writes,
            exit,
        });
    }

    raw_blocks
}

/// Resolves a relative branch target from an instruction index.
#[must_use]
fn rel_target_from_instr(instr_idx: usize, offset: i32, instrs: &[Spanned<Instr>]) -> usize {
    if instrs.is_empty() {
        return 0;
    }

    if instr_idx >= instrs.len() {
        let target = (instr_idx + 1).saturating_add_signed(offset as isize);
        return if target >= instrs.len() {
            instrs.len() - 1
        } else {
            target
        };
    }

    let target_word_pc = instrs[instr_idx]
        .pc
        .saturating_add(1)
        .saturating_add_signed(offset as isize);

    match instrs.binary_search_by(|spanned| spanned.pc.cmp(&target_word_pc)) {
        Ok(idx) => idx,
        Err(0) => 0,
        Err(pos) if pos >= instrs.len() => instrs.len() - 1,
        Err(pos) => pos - 1,
    }
}

/// Maps an instruction PC to its containing basic block index.
#[must_use]
fn pc_to_block_idx(entries: &[usize], pc: usize) -> usize {
    assert!(!entries.is_empty());
    assert!(entries[0] <= pc);
    entries.partition_point(|&e| e <= pc) - 1
}

/// Returns the truthiness of a symbol in a block, if it is assigned.
///
/// See [`HilExpr::truthiness`]
fn symbol_truthiness_in_block(block: &Block, symbol: SymbolId) -> Option<bool> {
    block.stmts.iter().find_map(|stmt| {
        let HilStmt::Assign {
            left: HilExpr::Symbol(target),
            value,
        } = &stmt.node
        else {
            return None;
        };

        (*target == symbol)
            .then_some(value)
            .and_then(|value| value.truthiness())
    })
}

/// Folds truthy condition jumps into the block exit, replacing them with a
/// direct jump to the target block.
fn fold_truthy_cond_jumps(blocks: &mut [Block]) -> bool {
    let mut was_changed = false;

    for block in blocks.iter_mut() {
        let Some(target) = (match &block.exit {
            BlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } => match cond {
                HilExpr::Symbol(symbol) => symbol_truthiness_in_block(block, *symbol)
                    .map(|truthy| if truthy { *then_block } else { *else_block }),
                _ => cond
                    .truthiness()
                    .map(|truthy| if truthy { *then_block } else { *else_block }),
            },
            _ => None,
        }) else {
            continue;
        };

        block.exit = BlockExit::Jump(target);
        was_changed = true;
    }

    was_changed
}

/// Folds condition chains into the block exit, replacing them with a direct
/// jump to the target block.
fn fold_condition_chains(
    mut blocks: Vec<Block>,
    predecessors: &[Vec<usize>],
) -> (bool, Vec<Block>) {
    let mut was_changed = false;

    for i in 0..blocks.len() {
        let (cond_a, then_a, else_a) = match &blocks[i].exit {
            BlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } => (cond.clone(), *then_block, *else_block),
            _ => continue,
        };

        if predecessors[then_a].len() == 1
            && blocks[then_a].stmts.is_empty()
            && let BlockExit::CondJump {
                cond: cond_b,
                then_block: then_b,
                else_block: else_b,
            } = blocks[then_a].exit.clone()
            && else_a == else_b
        {
            blocks[i].exit = BlockExit::CondJump {
                cond: HilExpr::Binary {
                    lhs: Box::new(cond_a),
                    op: BinOp::And,
                    rhs: Box::new(cond_b),
                },
                then_block: then_b,
                else_block: else_a,
            };
            was_changed = true;
            continue;
        }

        if predecessors[else_a].len() == 1
            && blocks[else_a].stmts.is_empty()
            && let BlockExit::CondJump {
                cond: cond_b,
                then_block: then_b,
                else_block: else_b,
            } = blocks[else_a].exit.clone()
            && then_a == then_b
        {
            blocks[i].exit = BlockExit::CondJump {
                cond: HilExpr::Binary {
                    lhs: Box::new(cond_a),
                    op: BinOp::Or,
                    rhs: Box::new(cond_b),
                },
                then_block: then_a,
                else_block: else_b,
            };
            was_changed = true;
        }
    }

    (was_changed, blocks)
}

/// Folds blocks with no statements and single jump exits.
///
/// # Returns
/// `true` if any blocks were folded, `false` otherwise.
fn thread_jumps(blocks: &mut [Block]) -> bool {
    let mut was_changed = false;
    for block_idx in 0..blocks.len() {
        if !matches!(
            &blocks[block_idx].exit,
            BlockExit::Jump(_) | BlockExit::Fallthrough(_) | BlockExit::CondJump { .. },
        ) {
            continue;
        }

        let folded = blocks[block_idx].exit_targets().map(|target| {
            let target_block = &blocks[target?];
            if target_block.stmts.is_empty() {
                match target_block.exit {
                    BlockExit::Jump(next) | BlockExit::Fallthrough(next) if next != target? => {
                        return Some(next);
                    }
                    _ => {}
                }
            }

            None
        });

        match &blocks[block_idx].exit {
            BlockExit::Jump(_) | BlockExit::Fallthrough(_) => {
                if let Some(folded_jump) = folded[0] {
                    blocks[block_idx].exit = BlockExit::Jump(folded_jump);
                    was_changed = true;
                }
            }
            BlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } => {
                let then_block = *then_block;
                let else_block = *else_block;

                let [folded_then, folded_else] = folded;
                if folded_then.is_some() || folded_else.is_some() {
                    blocks[block_idx].exit = BlockExit::CondJump {
                        cond: cond.clone(),
                        then_block: folded_then.unwrap_or(then_block),
                        else_block: folded_else.unwrap_or(else_block),
                    };
                    was_changed = true;
                }
            }
            _ => unreachable!(),
        }
    }
    was_changed
}
