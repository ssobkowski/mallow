use std::{
    borrow::Cow,
    collections::{BTreeSet, HashMap},
};

use bitvec::vec::BitVec;

use crate::ast::BinOp;
use crate::disasm::Proto;
use crate::hil::common::{const_expr, return_values};
use crate::hil::ir::{HilExpr, HilStmt, Spanned};
use crate::hil::lifter;
use crate::il::Instr;

/// One basic block in the per-proto control-flow graph.
#[derive(Debug, Clone)]
pub struct Block {
    pub id: usize,
    pub stmts: Vec<Spanned<HilStmt>>,
    pub exit: BlockExit,
    pub exit_word_pc: usize,
}

impl Block {
    /// Creates a new block with a synthetic exit PC.
    #[must_use]
    pub fn new(id: usize, stmts: Vec<Spanned<HilStmt>>, exit: BlockExit) -> Self {
        Self::with_exit_pc(id, stmts, exit, 0)
    }

    /// Creates a new block with an explicit exit PC.
    #[must_use]
    pub fn with_exit_pc(
        id: usize,
        stmts: Vec<Spanned<HilStmt>>,
        exit: BlockExit,
        exit_word_pc: usize,
    ) -> Self {
        Self {
            id,
            stmts,
            exit,
            exit_word_pc,
        }
    }
}

/// One terminating edge description for a block.
#[derive(Debug, Clone)]
pub enum BlockExit {
    Jump(usize),
    Fallthrough(usize),
    CondJump {
        cond: HilExpr,
        then_block: usize,
        else_block: usize,
    },
    ForNPrep {
        base: usize,
        loop_block: usize,
    },
    ForNLoop {
        base: usize,
        body_block: usize,
        exit_block: usize,
    },
    ForGPrep {
        base: usize,
        loop_block: usize,
    },
    ForGLoop {
        base: usize,
        body_block: usize,
        exit_block: usize,
        result_count: usize,
    },
    Return(Vec<HilExpr>),
}

/// Per-proto CFG plus dominance and loop-tail metadata.
#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    pub blocks: Vec<Block>,
    pub entry_block: usize,
    pub successors: Vec<Vec<usize>>,
    pub predecessors: Vec<Vec<usize>>,
    pub immediate_dominators: Vec<Option<usize>>,
    pub numeric_loops_by_base: HashMap<usize, Vec<usize>>,
    pub generic_loops_by_base: HashMap<usize, Vec<usize>>,
}

impl ControlFlowGraph {
    /// Builds a CFG from blocks and computes derived graph metadata.
    #[must_use]
    pub fn new(blocks: Vec<Block>, entry_block: usize) -> Self {
        let successors = build_successors(&blocks);
        let predecessors = build_predecessors(successors.len(), &successors);
        let immediate_dominators =
            build_dominator_metadata(entry_block, &successors, &predecessors);
        let (numeric_loops_by_base, generic_loops_by_base) = build_loop_indexes(&blocks);

        Self {
            blocks,
            entry_block,
            successors,
            predecessors,
            immediate_dominators,
            numeric_loops_by_base,
            generic_loops_by_base,
        }
    }

    /// Builds a CFG for one proto by splitting bytecode into basic blocks and decoding exits.
    #[must_use]
    pub fn from_proto(proto: &Proto, all_protos: &[Proto]) -> Self {
        if proto.instrs.is_empty() {
            const ENTRY: usize = 0;
            return Self::new(
                vec![Block::new(ENTRY, Vec::new(), BlockExit::Return(Vec::new()))],
                ENTRY,
            );
        }

        let instrs = proto.instrs.as_slice();
        let instr_word_pcs = normalized_instr_word_pcs(instrs, &proto.instr_word_pcs);
        let instr_word_pcs = instr_word_pcs.as_ref();

        let mut entries = BTreeSet::new();
        entries.insert(0usize);

        for (idx, instr) in instrs.iter().enumerate() {
            match instr {
                Instr::Return { .. } => {
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::FornPrep { offset, .. }
                | Instr::ForgPrep { offset, .. }
                | Instr::ForgPrepInext { offset, .. }
                | Instr::ForgPrepNext { offset, .. } => {
                    entries.insert(rel_target_plain_from_instr(
                        idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    ));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::FornLoop { offset, .. } | Instr::ForgLoop { offset, .. } => {
                    entries.insert(rel_target_plain_from_instr(
                        idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    ));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::Jump { offset }
                | Instr::JumpBack { offset }
                | Instr::JumpIf { offset, .. }
                | Instr::JumpIfNot { offset, .. } => {
                    entries.insert(rel_target_plain_from_instr(
                        idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    ));
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
                    entries.insert(rel_target_compare_from_instr(
                        idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    ));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::LoadB { jump, .. } if *jump > 0 => {
                    entries.insert(rel_target_plain_from_instr(
                        idx,
                        i16::from(*jump),
                        instrs,
                        instr_word_pcs,
                    ));
                }
                _ => {}
            }
        }

        let entries_vec: Vec<_> = entries.into_iter().collect();
        let mut blocks = Vec::with_capacity(entries_vec.len());

        for (block_idx, &start) in entries_vec.iter().enumerate() {
            let end = entries_vec
                .get(block_idx + 1)
                .copied()
                .unwrap_or(instrs.len());
            let block_instrs = &instrs[start..end];
            let Some(last_instr) = block_instrs.last() else {
                continue;
            };

            let (body_instrs, exit_instr) = if is_explicit_exit(last_instr) {
                let (block_instrs, exit_instr) = block_instrs.split_at(block_instrs.len() - 1);
                debug_assert!(!exit_instr.is_empty());

                (block_instrs, exit_instr.first())
            } else if matches!(last_instr, Instr::LoadB { jump, .. } if *jump > 0) {
                (block_instrs, Some(last_instr))
            } else {
                (block_instrs, None)
            };

            let exit_instr_idx = end.saturating_sub(1);

            let exit = match exit_instr {
                Some(Instr::Return { base, count }) => {
                    BlockExit::Return(return_values(*base, *count))
                }
                Some(Instr::Jump { offset }) | Some(Instr::JumpBack { offset }) => {
                    let target = rel_target_plain_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::Jump(pc_to_block_idx(&entries_vec, target))
                }
                Some(Instr::JumpIfNotLt { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op: BinOp::Lt,
                            rhs: Box::new(HilExpr::Local(*aux)),
                        },
                        then_block: block_idx + 1,
                        else_block: pc_to_block_idx(&entries_vec, target),
                    }
                }
                Some(Instr::JumpIf { reg, offset }) => {
                    let target = rel_target_plain_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::CondJump {
                        cond: HilExpr::Local(*reg),
                        then_block: pc_to_block_idx(&entries_vec, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfNot { reg, offset }) => {
                    let target = rel_target_plain_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::CondJump {
                        cond: HilExpr::Local(*reg),
                        then_block: block_idx + 1,
                        else_block: pc_to_block_idx(&entries_vec, target),
                    }
                }
                Some(Instr::JumpIfEq { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op: BinOp::Eq,
                            rhs: Box::new(HilExpr::Local(*aux)),
                        },
                        then_block: pc_to_block_idx(&entries_vec, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfLe { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op: BinOp::Lte,
                            rhs: Box::new(HilExpr::Local(*aux)),
                        },
                        then_block: pc_to_block_idx(&entries_vec, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfLt { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op: BinOp::Lt,
                            rhs: Box::new(HilExpr::Local(*aux)),
                        },
                        then_block: pc_to_block_idx(&entries_vec, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfNotEq { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op: BinOp::Eq,
                            rhs: Box::new(HilExpr::Local(*aux)),
                        },
                        then_block: block_idx + 1,
                        else_block: pc_to_block_idx(&entries_vec, target),
                    }
                }
                Some(Instr::JumpIfNotLe { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op: BinOp::Lte,
                            rhs: Box::new(HilExpr::Local(*aux)),
                        },
                        then_block: block_idx + 1,
                        else_block: pc_to_block_idx(&entries_vec, target),
                    }
                }
                Some(Instr::JumpXEqKNil {
                    reg,
                    invert,
                    offset,
                }) => {
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    let op = if *invert { BinOp::Ne } else { BinOp::Eq };
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op,
                            rhs: Box::new(HilExpr::Nil),
                        },
                        then_block: pc_to_block_idx(&entries_vec, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpXEqKB {
                    reg,
                    k,
                    invert,
                    offset,
                }) => {
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    let op = if *invert { BinOp::Ne } else { BinOp::Eq };
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op,
                            rhs: Box::new(HilExpr::Bool(*k)),
                        },
                        then_block: pc_to_block_idx(&entries_vec, target),
                        else_block: block_idx + 1,
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
                    let target = rel_target_compare_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    let op = if *invert { BinOp::Ne } else { BinOp::Eq };
                    BlockExit::CondJump {
                        cond: HilExpr::Binary {
                            lhs: Box::new(HilExpr::Local(*reg)),
                            op,
                            rhs: Box::new(const_expr(&proto.consts, *k as usize)),
                        },
                        then_block: pc_to_block_idx(&entries_vec, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::FornPrep { base, offset }) => {
                    let target = rel_target_plain_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::ForNPrep {
                        base: usize::from(*base),
                        loop_block: pc_to_block_idx(&entries_vec, target),
                    }
                }
                Some(Instr::FornLoop { base, offset }) => {
                    let target = rel_target_plain_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::ForNLoop {
                        base: usize::from(*base),
                        body_block: pc_to_block_idx(&entries_vec, target),
                        exit_block: block_idx + 1,
                    }
                }
                Some(Instr::ForgPrep { base, offset })
                | Some(Instr::ForgPrepInext { base, offset })
                | Some(Instr::ForgPrepNext { base, offset }) => {
                    let target = rel_target_plain_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::ForGPrep {
                        base: usize::from(*base),
                        loop_block: pc_to_block_idx(&entries_vec, target),
                    }
                }
                Some(Instr::ForgLoop {
                    base,
                    offset,
                    var_count,
                    ..
                }) => {
                    let target = rel_target_plain_from_instr(
                        exit_instr_idx,
                        *offset,
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::ForGLoop {
                        base: usize::from(*base),
                        body_block: pc_to_block_idx(&entries_vec, target),
                        exit_block: block_idx + 1,
                        result_count: usize::from(*var_count),
                    }
                }
                Some(Instr::LoadB { jump, .. }) if *jump > 0 => {
                    let target = rel_target_plain_from_instr(
                        exit_instr_idx,
                        i16::from(*jump),
                        instrs,
                        instr_word_pcs,
                    );
                    BlockExit::Jump(pc_to_block_idx(&entries_vec, target))
                }
                _ => BlockExit::Fallthrough(block_idx + 1),
            };

            let body_instr_word_pcs = &instr_word_pcs[start..start + body_instrs.len()];
            let lifted = lifter::lift(
                body_instrs,
                body_instr_word_pcs,
                &proto.consts,
                proto,
                all_protos,
            );
            let exit_word_pc = if end == 0 {
                0
            } else {
                instr_word_pcs[end.saturating_sub(1)]
            };

            blocks.push(Block::with_exit_pc(block_idx, lifted, exit, exit_word_pc));
        }

        Self::new(blocks, 0)
    }

    /// Returns all successor block ids for `block`.
    ///
    /// # Returns
    /// - `&[usize]`: outgoing targets, or an empty slice for out-of-range `block`.
    #[inline]
    #[must_use]
    pub fn successors(&self, block: usize) -> &[usize] {
        self.successors
            .get(block)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    /// Returns all predecessor block ids for `block`.
    ///
    /// # Returns
    /// - `&[usize]`: incoming sources, or an empty slice for out-of-range `block`.
    #[inline]
    #[must_use]
    pub fn predecessors(&self, block: usize) -> &[usize] {
        self.predecessors
            .get(block)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    /// Returns whether `dom` dominates `node`.
    ///
    /// This query exists because loop and merge recovery repeatedly ask dominance questions.
    ///
    /// # Returns
    /// - `true` when every path from entry to `node` passes through `dom`.
    /// - `false` otherwise.
    #[must_use]
    pub fn dominates(&self, dom: usize, node: usize) -> bool {
        if dom == node {
            return true;
        }
        let mut current = node;
        loop {
            match self.immediate_dominator(current) {
                Some(idom) if idom == dom => return true,
                Some(idom) => current = idom,
                None => return false,
            }
        }
    }

    /// Returns the immediate dominator of `block`.
    ///
    /// # Returns
    /// - `Some(idom)` for reachable non-entry blocks.
    /// - `None` for entry or unreachable blocks.
    #[inline]
    #[must_use]
    pub fn immediate_dominator(&self, block: usize) -> Option<usize> {
        self.immediate_dominators.get(block).copied().flatten()
    }
}

/// Returns successor targets encoded in one block exit.
///
/// # Returns
/// - `[Option<usize>; 2]`: one or two outgoing targets depending on exit shape.
#[must_use]
fn exit_targets(exit: &BlockExit) -> [Option<usize>; 2] {
    match *exit {
        BlockExit::Jump(target) | BlockExit::Fallthrough(target) => [Some(target), None],
        BlockExit::CondJump {
            then_block,
            else_block,
            ..
        } => [Some(then_block), Some(else_block)],
        BlockExit::ForNPrep { loop_block, .. } | BlockExit::ForGPrep { loop_block, .. } => {
            [Some(loop_block), None]
        }
        BlockExit::ForNLoop {
            body_block,
            exit_block,
            ..
        }
        | BlockExit::ForGLoop {
            body_block,
            exit_block,
            ..
        } => [Some(body_block), Some(exit_block)],
        BlockExit::Return(_) => [None, None],
    }
}

/// Returns whether one instruction must terminate its basic block.
#[must_use]
fn is_explicit_exit(instr: &Instr) -> bool {
    matches!(
        instr,
        Instr::Return { .. }
            | Instr::Jump { .. }
            | Instr::JumpBack { .. }
            | Instr::JumpIf { .. }
            | Instr::JumpIfNot { .. }
            | Instr::JumpIfEq { .. }
            | Instr::JumpIfLe { .. }
            | Instr::JumpIfLt { .. }
            | Instr::JumpIfNotEq { .. }
            | Instr::JumpIfNotLe { .. }
            | Instr::JumpIfNotLt { .. }
            | Instr::JumpXEqKNil { .. }
            | Instr::JumpXEqKB { .. }
            | Instr::JumpXEqKN { .. }
            | Instr::JumpXEqKS { .. }
            | Instr::FornPrep { .. }
            | Instr::FornLoop { .. }
            | Instr::ForgPrep { .. }
            | Instr::ForgPrepInext { .. }
            | Instr::ForgPrepNext { .. }
            | Instr::ForgLoop { .. }
    )
}

/// Resolves a relative branch target from the next instruction index.
///
/// Some Luau compare-family jumps encode "no jump" as offset `1` instead of `0`;
/// `bias` normalizes those opcodes back to a plain PC-relative target.
fn rel_target_with_bias(next_pc: usize, offset: i16, bias: i16, instr_len: usize) -> usize {
    if instr_len == 0 {
        return 0;
    }

    let target = next_pc.saturating_add_signed((offset - bias) as isize);
    if target >= instr_len {
        instr_len - 1
    } else {
        target
    }
}

fn normalized_instr_word_pcs<'a>(
    instrs: &[Instr],
    instr_word_pcs: &'a [usize],
) -> Cow<'a, [usize]> {
    if instr_word_pcs.len() == instrs.len() && !instr_word_pcs.is_empty() {
        return Cow::Borrowed(instr_word_pcs);
    }

    let mut word_pcs = Vec::with_capacity(instrs.len());
    let mut word_pc = 0usize;
    for instr in instrs {
        word_pcs.push(word_pc);
        word_pc = word_pc.saturating_add(instr.word_len());
    }
    Cow::Owned(word_pcs)
}

/// Resolves a relative branch target from an instruction index.
///
/// # Returns
/// - the instruction index targeted by the relative branch.
#[must_use]
fn rel_target_from_instr(
    instr_idx: usize,
    offset: i16,
    bias: i16,
    instrs: &[Instr],
    instr_word_pcs: &[usize],
) -> usize {
    if instrs.is_empty() {
        return 0;
    }

    if instr_idx >= instrs.len() || instr_word_pcs.len() != instrs.len() {
        return rel_target_with_bias(instr_idx + 1, offset, bias, instrs.len());
    }

    let next_word_pc = instr_word_pcs[instr_idx].saturating_add(instrs[instr_idx].word_len());
    let raw = next_word_pc as isize + offset as isize - bias as isize;
    let target_word_pc = if raw < 0 { 0usize } else { raw as usize };

    match instr_word_pcs.binary_search(&target_word_pc) {
        Ok(idx) => idx,
        Err(0) => 0,
        Err(pos) if pos >= instrs.len() => instrs.len() - 1,
        Err(pos) => pos - 1,
    }
}

/// Resolves the target of a jump opcode whose offset uses `0 == next instruction`.
#[must_use]
fn rel_target_plain_from_instr(
    instr_idx: usize,
    offset: i16,
    instrs: &[Instr],
    instr_word_pcs: &[usize],
) -> usize {
    rel_target_from_instr(instr_idx, offset, 0, instrs, instr_word_pcs)
}

/// Resolves the target of a compare-family jump whose offset uses `1 == next instruction`.
#[must_use]
fn rel_target_compare_from_instr(
    instr_idx: usize,
    offset: i16,
    instrs: &[Instr],
    instr_word_pcs: &[usize],
) -> usize {
    rel_target_from_instr(instr_idx, offset, 1, instrs, instr_word_pcs)
}

/// Maps an instruction PC to its containing basic block index.
fn pc_to_block_idx(entries: &[usize], pc: usize) -> usize {
    assert!(!entries.is_empty());
    assert!(entries[0] <= pc);
    entries.partition_point(|&e| e <= pc) - 1
}

/// Builds forward adjacency lists from block exits.
///
/// # Returns
/// - `Vec<Vec<usize>>`: `successors[src]` for each block id.
#[must_use]
fn build_successors(blocks: &[Block]) -> Vec<Vec<usize>> {
    let len = blocks.len();
    let mut successors = vec![Vec::new(); len];

    for (src, block) in blocks.iter().enumerate() {
        for target in exit_targets(&block.exit).into_iter().flatten() {
            if target < len {
                successors[src].push(target);
            }
        }
    }

    successors
}

/// Builds reverse adjacency lists from forward adjacency.
///
/// # Returns
/// - `Vec<Vec<usize>>`: `predecessors[target]` for each block id.
#[must_use]
fn build_predecessors(len: usize, successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut predecessors = vec![Vec::new(); len];

    for (src, targets) in successors.iter().enumerate() {
        for &target in targets {
            predecessors[target].push(src);
        }
    }

    predecessors
}

/// Marks blocks reachable from entry.
///
/// # Returns
/// - `Vec<bool>`: reachability bitset by block id.
#[must_use]
fn reachable_blocks(entry_block: usize, successors: &[Vec<usize>]) -> Vec<bool> {
    let mut reachable = vec![false; successors.len()];
    let mut stack = Vec::new();

    if entry_block < successors.len() {
        stack.push(entry_block);
    }

    while let Some(block) = stack.pop() {
        if reachable[block] {
            continue;
        }
        reachable[block] = true;

        for &next in &successors[block] {
            if !reachable[next] {
                stack.push(next);
            }
        }
    }

    reachable
}

/// Computes immediate dominators for all reachable blocks.
///
/// # Returns
/// - `Vec<Option<usize>>`: idom by block id; `None` for entry and unreachable blocks.
#[must_use]
fn build_dominator_metadata(
    entry_block: usize,
    successors: &[Vec<usize>],
    predecessors: &[Vec<usize>],
) -> Vec<Option<usize>> {
    let len = successors.len();
    let reachable = reachable_blocks(entry_block, successors);

    let mut dom: Vec<_> = (0..len)
        .map(|block| {
            if !reachable[block] {
                return BitVec::repeat(false, len);
            }
            if block == entry_block {
                let mut bits = BitVec::repeat(false, len);
                bits.set(entry_block, true);
                return bits;
            }
            let mut bits = BitVec::repeat(false, len);
            for (i, is_reachable) in reachable.iter().enumerate().take(len) {
                if *is_reachable {
                    bits.set(i, true);
                }
            }
            bits
        })
        .collect();

    let mut changed = true;
    while changed {
        changed = false;
        for block in 0..len {
            if !reachable[block] || block == entry_block {
                continue;
            }

            let mut next = {
                let mut acc: Option<BitVec> = None;
                for &pred in &predecessors[block] {
                    if !reachable[pred] {
                        continue;
                    }
                    acc = Some(match acc {
                        None => dom[pred].clone(),
                        Some(mut bits) => {
                            bits &= &dom[pred];
                            bits
                        }
                    });
                }
                acc.unwrap_or_else(|| BitVec::repeat(false, len))
            };
            next.set(block, true);

            if next != dom[block] {
                dom[block] = next;
                changed = true;
            }
        }
    }

    let mut immediate_dominators = vec![None; len];
    for block in 0..len {
        if !reachable[block] || block == entry_block {
            continue;
        }

        immediate_dominators[block] = (0..len)
            .filter(|&candidate| candidate != block && dom[block][candidate])
            .find(|&candidate| {
                (0..len)
                    .filter(|&other| other != candidate && other != block && dom[block][other])
                    .all(|other| !dom[other][candidate])
            });
    }

    immediate_dominators
}

/// Indexes loop-tail blocks by Luau loop base register.
///
/// # Returns
/// - numeric and generic loop-tail maps keyed by base register.
#[must_use]
fn build_loop_indexes(
    blocks: &[Block],
) -> (HashMap<usize, Vec<usize>>, HashMap<usize, Vec<usize>>) {
    let mut numeric_loops_by_base: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut generic_loops_by_base: HashMap<usize, Vec<usize>> = HashMap::new();

    for (idx, block) in blocks.iter().enumerate() {
        match block.exit {
            BlockExit::ForNLoop { base, .. } => {
                numeric_loops_by_base.entry(base).or_default().push(idx)
            }
            BlockExit::ForGLoop { base, .. } => {
                generic_loops_by_base.entry(base).or_default().push(idx)
            }
            _ => {}
        }
    }

    (numeric_loops_by_base, generic_loops_by_base)
}

#[cfg(test)]
mod tests {
    use crate::disasm::Proto;
    use crate::il::Instr;

    use super::ControlFlowGraph;

    #[test]
    fn from_proto_builds_conditional_edges() {
        let proto = Proto {
            instrs: vec![
                Instr::LoadB {
                    reg: 0,
                    value: true,
                    jump: 0,
                },
                Instr::JumpIfNot { reg: 0, offset: 1 },
                Instr::LoadN { reg: 1, value: 1 },
                Instr::Return { base: 1, count: 2 },
                Instr::Return { base: 0, count: 1 },
            ],
            ..Proto::default()
        };
        let all_protos = vec![proto];

        let cfg = ControlFlowGraph::from_proto(&all_protos[0], &all_protos);
        assert_eq!(cfg.blocks.len(), 4);
        assert!(matches!(
            cfg.blocks[0].exit,
            super::BlockExit::CondJump {
                then_block: 1,
                else_block: 2,
                ..
            }
        ));
    }

    #[test]
    fn from_proto_builds_numeric_for_edges() {
        let proto = Proto {
            instrs: vec![
                Instr::FornPrep { base: 0, offset: 2 },
                Instr::LoadN { reg: 1, value: 1 },
                Instr::FornLoop {
                    base: 0,
                    offset: -2,
                },
                Instr::Return { base: 0, count: 1 },
            ],
            ..Proto::default()
        };
        let all_protos = vec![proto];

        let cfg = ControlFlowGraph::from_proto(&all_protos[0], &all_protos);
        assert_eq!(cfg.blocks.len(), 3);
        assert!(matches!(
            cfg.blocks[0].exit,
            super::BlockExit::ForNPrep {
                base: 0,
                loop_block: 2
            }
        ));
        assert!(matches!(
            cfg.blocks[1].exit,
            super::BlockExit::ForNLoop {
                base: 0,
                body_block: 1,
                exit_block: 2
            }
        ));
    }

    #[test]
    fn from_proto_uses_block_local_word_pcs_for_lifted_statements() {
        let proto = Proto {
            instrs: vec![
                Instr::LoadN { reg: 0, value: 1 },
                Instr::Return { base: 0, count: 1 },
                Instr::LoadN { reg: 1, value: 2 },
                Instr::Return { base: 1, count: 2 },
            ],
            instr_word_pcs: vec![0, 1, 2, 3],
            ..Proto::default()
        };
        let all_protos = vec![proto];

        let cfg = ControlFlowGraph::from_proto(&all_protos[0], &all_protos);
        assert_eq!(cfg.blocks.len(), 2);
        assert_eq!(cfg.blocks[0].stmts[0].pc, 0);
        assert_eq!(cfg.blocks[1].stmts[0].pc, 2);
    }

    #[test]
    fn from_proto_synthesizes_word_pcs_from_instruction_lengths() {
        let proto = Proto {
            instrs: vec![
                Instr::GetImport {
                    dest: 0,
                    index: 0,
                    path: 1,
                },
                Instr::LoadN { reg: 1, value: 2 },
                Instr::Return { base: 0, count: 1 },
            ],
            ..Proto::default()
        };
        let all_protos = vec![proto];

        let cfg = ControlFlowGraph::from_proto(&all_protos[0], &all_protos);
        assert_eq!(cfg.blocks.len(), 1);
        assert_eq!(cfg.blocks[0].stmts.len(), 2);
        assert_eq!(cfg.blocks[0].stmts[0].pc, 0);
        assert_eq!(cfg.blocks[0].stmts[1].pc, 2);
    }
}
