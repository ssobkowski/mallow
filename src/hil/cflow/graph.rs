use std::{
    collections::{BTreeSet, HashMap},
    ops::Range,
};

use id_arena::Arena;

use crate::{
    ast::BinOp,
    disasm::Proto,
    hil::{
        common::{const_expr, decoded_count},
        ir::{HilExpr, HilStmt, Spanned, ToSpanned as _},
        lifter::{
            LiftContext, Lifter, lift,
            symbol::{Symbol, SymbolId},
        },
    },
    il::{Constant, Count, Instr},
};

/// Represents an unlifted block
#[derive(Debug)]
pub struct RawBlock {
    /// The range of instructions indices that belong to this block, excluding the potential exit instruction.
    instr_range: Range<usize>,
    /// The full range of instruction indices that belong to this block, including the potential exit instruction.
    full_instr_range: Range<usize>,
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
        base: usize,
        body_block: usize,
        exit_block: usize,
    },
    FornLoop {
        base: usize,
        body_block: usize,
        exit_block: usize,
    },
    ForgPrep {
        base: usize,
        body_block: usize,
        exit_block: usize,
    },
    ForgLoop {
        base: usize,
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
    fn exit_targets(&self) -> [Option<usize>; 2] {
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
        base: usize,
        body_block: usize,
        exit_block: usize,
    },
    FornLoop {
        base: usize,
        body_block: usize,
        exit_block: usize,
    },
    ForgPrep {
        base: usize,
        body_block: usize,
        exit_block: usize,
    },
    ForgLoop {
        base: usize,
        body_block: usize,
        exit_block: usize,
        result_count: usize,
    },
    Return(Vec<HilExpr>),
}

impl BlockExit {
    /// Returns successor targets encoded in one block exit.
    #[must_use]
    fn exit_targets(&self) -> [Option<usize>; 2] {
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

#[derive(Debug)]
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
    pub fn from_proto(proto: &Proto, all_protos: &[Proto]) -> Self {
        let instrs = proto.instrs.as_slice();

        // First, we build a "raw" cfg - plain blocks that only hold the range
        // of instructions they contain.

        let mut entries = BTreeSet::new();
        entries.insert(0usize);

        for (idx, (instr, _)) in instrs.iter().enumerate() {
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
                    entries.insert(rel_target_plain_from_instr(idx, *offset, instrs));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::FornLoop { offset, .. } | Instr::ForgLoop { offset, .. } => {
                    entries.insert(rel_target_plain_from_instr(idx, *offset, instrs));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::Jump { offset }
                | Instr::JumpBack { offset }
                | Instr::JumpIf { offset, .. }
                | Instr::JumpIfNot { offset, .. } => {
                    entries.insert(rel_target_plain_from_instr(idx, *offset, instrs));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::JumpX { offset } => {
                    entries.insert(rel_target_plain_from_instr_wide(idx, *offset, instrs));
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
                    entries.insert(rel_target_compare_from_instr(idx, *offset, instrs));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::LoadB { jump, .. } if *jump > 0 => {
                    entries.insert(rel_target_plain_from_instr(idx, i16::from(*jump), instrs));
                }
                _ => {}
            }
        }

        let entries: Vec<_> = entries.into_iter().collect();
        let mut raw_blocks = Vec::with_capacity(entries.len());

        for (block_idx, &start) in entries.iter().enumerate() {
            let end = entries.get(block_idx + 1).copied().unwrap_or(instrs.len());

            let block_instrs: Vec<_> = instrs[start..end].iter().map(|i| i.0).collect();
            let Some(last_instr) = block_instrs.last() else {
                continue;
            };

            let is_branch_or_return =
                is_branch_exit(last_instr) || matches!(last_instr, Instr::Return { .. });

            let (body_end, exit_instr) = if is_branch_or_return {
                (end - 1, Some(last_instr))
            } else if matches!(last_instr, Instr::LoadB { jump, .. } if *jump > 0) {
                // LoadB still needs to be lifted to assign the boolean
                (end, Some(last_instr))
            } else {
                (end, None)
            };

            let exit_instr_idx = end.saturating_sub(1);
            let exit = match exit_instr.copied() {
                Some(Instr::Return { base, count }) => RawBlockExit::Return { base, count },
                Some(Instr::Jump { offset }) | Some(Instr::JumpBack { offset }) => {
                    let target = rel_target_plain_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::Jump(pc_to_block_idx(&entries, target))
                }
                Some(Instr::JumpX { offset }) => {
                    let target = rel_target_plain_from_instr_wide(exit_instr_idx, offset, instrs);
                    RawBlockExit::Jump(pc_to_block_idx(&entries, target))
                }
                Some(Instr::JumpIfNotLt { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Binary {
                            lhs: reg,
                            op: BinOp::Lt,
                            rhs: CondRhs::Reg(aux),
                        },
                        then_block: block_idx + 1,
                        else_block: pc_to_block_idx(&entries, target),
                    }
                }
                Some(Instr::JumpIf { reg, offset }) => {
                    let target = rel_target_plain_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Unary(reg),
                        then_block: pc_to_block_idx(&entries, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfNot { reg, offset }) => {
                    let target = rel_target_plain_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Unary(reg),
                        then_block: block_idx + 1,
                        else_block: pc_to_block_idx(&entries, target),
                    }
                }
                Some(Instr::JumpIfEq { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Binary {
                            lhs: reg,
                            op: BinOp::Eq,
                            rhs: CondRhs::Reg(aux),
                        },
                        then_block: pc_to_block_idx(&entries, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfNotEq { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Binary {
                            lhs: reg,
                            op: BinOp::Ne,
                            rhs: CondRhs::Reg(aux),
                        },
                        then_block: pc_to_block_idx(&entries, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfLe { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Binary {
                            lhs: reg,
                            op: BinOp::Lte,
                            rhs: CondRhs::Reg(aux),
                        },
                        then_block: pc_to_block_idx(&entries, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfNotLe { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Binary {
                            lhs: reg,
                            op: BinOp::Gt,
                            rhs: CondRhs::Reg(aux),
                        },
                        then_block: block_idx + 1,
                        else_block: pc_to_block_idx(&entries, target),
                    }
                }
                Some(Instr::JumpIfLt { reg, aux, offset }) => {
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Binary {
                            lhs: reg,
                            op: BinOp::Lt,
                            rhs: CondRhs::Reg(aux),
                        },
                        then_block: pc_to_block_idx(&entries, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpXEqKNil {
                    reg,
                    invert,
                    offset,
                }) => {
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    let (then_block, else_block) = if invert {
                        (block_idx + 1, pc_to_block_idx(&entries, target))
                    } else {
                        (pc_to_block_idx(&entries, target), block_idx + 1)
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
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    let (then_block, else_block) = if invert {
                        (block_idx + 1, pc_to_block_idx(&entries, target))
                    } else {
                        (pc_to_block_idx(&entries, target), block_idx + 1)
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
                    let target = rel_target_compare_from_instr(exit_instr_idx, offset, instrs);
                    let (then_block, else_block) = if invert {
                        (block_idx + 1, pc_to_block_idx(&entries, target))
                    } else {
                        (pc_to_block_idx(&entries, target), block_idx + 1)
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
                    let target = rel_target_plain_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::FornPrep {
                        base: usize::from(base),
                        body_block: block_idx + 1,
                        exit_block: pc_to_block_idx(&entries, target),
                    }
                }
                Some(Instr::FornLoop { base, offset }) => {
                    let target = rel_target_plain_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::FornLoop {
                        base: usize::from(base),
                        body_block: pc_to_block_idx(&entries, target),
                        exit_block: block_idx + 1,
                    }
                }
                Some(Instr::ForgPrep { base, offset })
                | Some(Instr::ForgPrepInext { base, offset })
                | Some(Instr::ForgPrepNext { base, offset }) => {
                    let target = rel_target_plain_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::ForgPrep {
                        base: usize::from(base),
                        body_block: block_idx + 1,
                        exit_block: pc_to_block_idx(&entries, target),
                    }
                }
                Some(Instr::ForgLoop {
                    base,
                    offset,
                    var_count,
                    ..
                }) => {
                    let target = rel_target_plain_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::ForgLoop {
                        base: usize::from(base),
                        body_block: pc_to_block_idx(&entries, target),
                        exit_block: block_idx + 1,
                        result_count: usize::from(var_count),
                    }
                }
                Some(Instr::LoadB { jump, .. }) if jump > 0 => {
                    let target =
                        rel_target_plain_from_instr(exit_instr_idx, i16::from(jump), instrs);
                    RawBlockExit::Jump(pc_to_block_idx(&entries, target))
                }
                _ => RawBlockExit::Fallthrough(block_idx + 1),
            };

            raw_blocks.push(RawBlock {
                instr_range: start..body_end,
                full_instr_range: start..end,
                exit,
            });
        }

        let successors = build_successors(raw_blocks.iter().map(|b| b.exit.exit_targets()));
        let predecessors = build_predecessors(&successors);
        let idoms = build_immediate_dominators(0, &successors, &predecessors);

        // Having a raw cfg, we can now compute the phi nodes for each block.
        let defs: Vec<BTreeSet<_>> = raw_blocks
            .iter()
            .map(|b| {
                let block_instrs = &instrs[b.full_instr_range.clone()];
                block_instrs
                    .iter()
                    .flat_map(|(i, _)| i.written_registers())
                    .collect()
            })
            .collect();

        // TODO: This whole section is stupid as fuck. It currently uses every register
        //       ever written for Phi Node insertion, which is redundant and retarded.
        //       Implement Braun et al.'s.
        let all_written_regs: BTreeSet<_> = defs
            .iter()
            .flat_map(|block_defs| block_defs.iter().copied())
            .collect();

        let mut phi_sites: Vec<Vec<u8>> = vec![Vec::new(); raw_blocks.len()];
        for (block_id, preds) in predecessors.iter().enumerate() {
            if preds.len() >= 2 {
                // This is a join point, it needs phis
                phi_sites[block_id].extend(all_written_regs.iter().cloned());
            }
        }

        // Iteration order of the blocks matters here as we want every dominator
        // to come before the blocks it dominates.
        type BlockState = [Option<SymbolId>; 256];

        let mut exit_states: Vec<Option<BlockState>> = vec![None; raw_blocks.len()];
        let mut arena = Arena::new();
        let mut blocks: Vec<Option<Block>> = vec![None; raw_blocks.len()];

        eprintln!(
            "Proto {} RPO: {:?}",
            proto.index,
            compute_rpo(0, &successors)
        );
        for (i, succs) in successors.iter().enumerate() {
            eprintln!("  block {i} successors: {succs:?}");
        }
        for (i, b) in raw_blocks.iter().enumerate() {
            eprintln!("  raw block {i}: {:?}", b.exit);
            for (instr, _) in &proto.instrs[b.full_instr_range.clone()] {
                println!(
                    "    Instr {:?} written regs {:?}",
                    instr,
                    instr.written_registers()
                );
            }
        }

        for block_id in compute_rpo(0, &successors) {
            let mut symbols = if block_id == 0 {
                let mut symbols = [None; 256] as BlockState;

                for i in 0..proto.num_params {
                    symbols[i as usize] = Some(arena.alloc(Symbol::new(i, 0)));
                }

                symbols
            } else {
                exit_states[idoms[block_id].unwrap()].unwrap()
            };

            let mut stmts = emit_phis(
                &phi_sites[block_id],
                &predecessors[block_id],
                &exit_states,
                &mut symbols,
                &mut arena,
            );
            stmts.extend(lift(LiftContext {
                instrs: &instrs[raw_blocks[block_id].instr_range.clone()],
                consts: &proto.consts,
                parent_proto: proto,
                protos: all_protos,
                arena: &mut arena,
                state: &mut symbols,
            }));

            let exit = translate_exit(&raw_blocks[block_id].exit, &symbols, &proto.consts);
            blocks[block_id] = Some(Block { stmts, exit });
            exit_states[block_id] = Some(symbols);

            for &succ in &successors[block_id] {
                let Some(succ_block) = blocks[succ].as_mut() else {
                    continue;
                };
                for stmt in &mut succ_block.stmts {
                    let HilStmt::Phi { target, operands } = &mut stmt.inner else {
                        continue;
                    };

                    // Skip if this predecessor already filled its operand (forward edge, done in emit_phis)
                    if operands.iter().any(|(p, _)| *p == block_id) {
                        continue;
                    }

                    let reg = arena[*target].reg;
                    if let Some(sym) = exit_states[block_id].unwrap()[reg as usize] {
                        operands.push((block_id, sym));
                    }
                }
            }
        }

        let mut blocks: Vec<_> = blocks
            .into_iter()
            .map(|b| {
                b.unwrap_or_else(|| {
                    // Luau compiler might leave some "dead" blocks (for instance leftovers of jump threading optimization)
                    // we don't panic here as it's probably fine (if rpo couldn't reach it), just emit a dummy
                    Block {
                        stmts: Vec::new(),
                        exit: BlockExit::Return(Vec::new()),
                    }
                })
            })
            .collect();

        let blocks = loop {
            let (changed, new_blocks) = fold_short_circuits(blocks);
            if !changed {
                break new_blocks;
            }
            blocks = new_blocks;
        };
        let (numeric_loops_by_base, generic_loops_by_base) = build_loop_indexes(&blocks);

        // Rebuild after folding
        let successors = build_successors(blocks.iter().map(|b| b.exit.exit_targets()));
        let predecessors = build_predecessors(&successors);
        let immediate_dominators = build_immediate_dominators(0, &successors, &predecessors);

        Self {
            blocks,
            entry_block: 0,
            successors,
            predecessors,
            immediate_dominators,
            numeric_loops_by_base,
            generic_loops_by_base,
        }
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

/// Builds forward adjacency lists from block exits.
#[must_use]
fn build_successors<I>(targets_iter: I) -> Vec<Vec<usize>>
where
    I: IntoIterator<Item = [Option<usize>; 2]>,
    I::IntoIter: ExactSizeIterator,
{
    let iter = targets_iter.into_iter();
    let len = iter.len();

    iter.map(|targets| targets.into_iter().flatten().filter(|&t| t < len).collect())
        .collect()
}

/// Builds reverse adjacency lists from forward adjacency.
#[must_use]
fn build_predecessors(successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut predecessors = vec![Vec::new(); successors.len()];

    for (src, targets) in successors.iter().enumerate() {
        for &target in targets {
            predecessors[target].push(src);
        }
    }

    predecessors
}

fn compute_rpo(entry_block: usize, successors: &[Vec<usize>]) -> Vec<usize> {
    let len = successors.len();
    let mut visited = vec![false; len];
    let mut post_order = Vec::with_capacity(len);

    // TODO: Use iterated stack here? This might overflow, though I have not hit that yet.
    fn dfs(
        block: usize,
        successors: &[Vec<usize>],
        visited: &mut [bool],
        post_order: &mut Vec<usize>,
    ) {
        visited[block] = true;
        for &succ in &successors[block] {
            if !visited[succ] {
                dfs(succ, successors, visited, post_order);
            }
        }
        post_order.push(block);
    }

    dfs(entry_block, successors, &mut visited, &mut post_order);

    post_order.reverse();
    post_order
}

/// Computes immediate dominators for all reachable blocks using the
/// Cooper-Harvey-Kennedy algorithm.
pub fn build_immediate_dominators(
    entry_block: usize,
    successors: &[Vec<usize>],
    predecessors: &[Vec<usize>],
) -> Vec<Option<usize>> {
    let rpo_nodes = compute_rpo(entry_block, successors);

    let len = successors.len();
    let mut doms = vec![None; len];
    doms[entry_block] = Some(entry_block);

    let mut rpo_number = vec![usize::MAX; len];
    for (index, &block) in rpo_nodes.iter().enumerate() {
        rpo_number[block] = index;
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &block in &rpo_nodes {
            if block == entry_block {
                continue;
            }

            let Some(mut new_idom) = predecessors[block]
                .iter()
                .copied()
                .find(|&p| doms[p].is_some())
            else {
                continue;
            };

            for &p in &predecessors[block] {
                if p != new_idom && doms[p].is_some() {
                    new_idom = intersect(p, new_idom, &doms, &rpo_number);
                }
            }

            if doms[block] != Some(new_idom) {
                doms[block] = Some(new_idom);
                changed = true;
            }
        }
    }
    doms[entry_block] = None;

    doms
}

fn intersect(mut b1: usize, mut b2: usize, doms: &[Option<usize>], rpo_number: &[usize]) -> usize {
    while b1 != b2 {
        while rpo_number[b1] > rpo_number[b2] {
            b1 = doms[b1].unwrap();
        }
        while rpo_number[b2] > rpo_number[b1] {
            b2 = doms[b2].unwrap();
        }
    }
    b1
}

/// Resolves a relative branch target from the next instruction index.
///
/// Some Luau compare-family jumps encode "no jump" as offset `1` instead of `0`;
/// `bias` normalizes those opcodes back to a plain PC-relative target.
const fn rel_target_with_bias(next_pc: usize, offset: i32, bias: i32, instr_len: usize) -> usize {
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

/// Resolves a relative branch target from an instruction index.
#[must_use]
fn rel_target_from_instr(instr_idx: usize, offset: i32, instrs: &[(Instr, usize)]) -> usize {
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

    let (_, pc) = instrs[instr_idx];
    let target_word_pc = pc.saturating_add(1).saturating_add_signed(offset as isize);

    match instrs.binary_search_by(|(_, pc)| pc.cmp(&target_word_pc)) {
        Ok(idx) => idx,
        Err(0) => 0,
        Err(pos) if pos >= instrs.len() => instrs.len() - 1,
        Err(pos) => pos - 1,
    }
}

/// Resolves the target of a jump opcode whose offset uses `0 == next instruction`.
#[must_use]
fn rel_target_plain_from_instr(instr_idx: usize, offset: i16, instrs: &[(Instr, usize)]) -> usize {
    rel_target_from_instr(instr_idx, offset as i32, instrs)
}

/// Resolves the target of a wide jump opcode whose offset uses `0 == next instruction`.
#[must_use]
fn rel_target_plain_from_instr_wide(
    instr_idx: usize,
    offset: i32,
    instrs: &[(Instr, usize)],
) -> usize {
    rel_target_from_instr(instr_idx, offset, instrs)
}

/// Resolves the target of a compare-family jump whose offset uses `1 == next instruction`.
#[must_use]
fn rel_target_compare_from_instr(
    instr_idx: usize,
    offset: i16,
    instrs: &[(Instr, usize)],
) -> usize {
    rel_target_from_instr(instr_idx, offset as i32, instrs)
}

/// Returns whether one instruction must terminate its basic block.
#[must_use]
const fn is_branch_exit(instr: &Instr) -> bool {
    matches!(
        instr,
        Instr::Jump { .. }
            | Instr::JumpX { .. }
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

/// Maps an instruction PC to its containing basic block index.
fn pc_to_block_idx(entries: &[usize], pc: usize) -> usize {
    assert!(!entries.is_empty());
    assert!(entries[0] <= pc);
    entries.partition_point(|&e| e <= pc) - 1
}

fn emit_phis(
    phi_regs: &[u8],
    predecessors: &[usize],
    exit_states: &[Option<[Option<SymbolId>; 256]>],
    current_symbols: &mut [Option<SymbolId>; 256],
    arena: &mut Arena<Symbol>,
) -> Vec<Spanned<HilStmt>> {
    let mut stmts = Vec::new();

    for &reg in phi_regs {
        // TODO: flat_map first + zip with predecessors (?)
        let operands: Vec<_> = predecessors
            .iter()
            .map(|&p| (p, exit_states[p].as_ref().and_then(|s| s[reg as usize])))
            .collect();

        // Check if we are waiting on a back-edge that hasn't been visited yet
        let has_unknown_preds = operands.iter().any(|(_, s)| s.is_none());

        // If we have no unknown predecessors, and every predecessor that
        // has been processed agrees on the same symbol, and no predecessor
        // has a different one, no phi is needed.
        let known: Vec<_> = operands.iter().filter_map(|(_, s)| *s).collect();
        if !has_unknown_preds && !known.is_empty() && known.windows(2).all(|w| w[0] == w[1]) {
            current_symbols[reg as usize] = Some(known[0]);
            continue;
        }

        // TODO: Does pc matter here? If yes, what pc should be used?
        let target = arena.alloc(Symbol::new(reg, 0));
        current_symbols[reg as usize] = Some(target);

        stmts.push(
            HilStmt::Phi {
                target,
                operands: operands
                    .into_iter()
                    .filter_map(|(pred, sym)| sym.map(|s| (pred, s)))
                    .collect(),
            }
            .to_spanned(0),
        );
    }

    stmts
}

// TODO: Make RawBlockExit Copy as the constant dereferencing here is retarded,
//       and it's a one time 40 bytes copy anyways.
fn translate_exit(
    exit: &RawBlockExit,
    state: &[Option<SymbolId>; 256],
    consts: &[Constant],
) -> BlockExit {
    match exit {
        RawBlockExit::Jump(t) => BlockExit::Jump(*t),
        RawBlockExit::Fallthrough(t) => BlockExit::Fallthrough(*t),
        RawBlockExit::CondJump {
            cond,
            then_block,
            else_block,
        } => {
            let hil_cond = match cond {
                Cond::Unary(reg) => HilExpr::Symbol(
                    state[*reg as usize].unwrap_or_else(|| panic!("unbound register: {}", reg)),
                ),
                Cond::Binary { lhs, op, rhs } => {
                    let lhs_expr = HilExpr::Symbol(
                        state[*lhs as usize].unwrap_or_else(|| panic!("unbound register: {}", lhs)),
                    );
                    let rhs_expr = match rhs {
                        CondRhs::Reg(r) => HilExpr::Symbol(
                            state[*r as usize].unwrap_or_else(|| panic!("unbound register: {}", r)),
                        ),
                        CondRhs::Const(idx) => const_expr(consts, *idx),
                        CondRhs::Nil => HilExpr::Nil,
                        CondRhs::Bool(b) => HilExpr::Bool(*b),
                    };

                    HilExpr::Binary {
                        lhs: Box::new(lhs_expr),
                        op: *op,
                        rhs: Box::new(rhs_expr),
                    }
                }
            };

            BlockExit::CondJump {
                cond: hil_cond,
                then_block: *then_block,
                else_block: *else_block,
            }
        }
        RawBlockExit::FornPrep {
            base,
            body_block,
            exit_block,
        } => BlockExit::FornPrep {
            base: *base,
            body_block: *body_block,
            exit_block: *exit_block,
        },
        RawBlockExit::FornLoop {
            base,
            body_block,
            exit_block,
        } => BlockExit::FornLoop {
            base: *base,
            body_block: *body_block,
            exit_block: *exit_block,
        },
        RawBlockExit::ForgPrep {
            base,
            body_block,
            exit_block,
        } => BlockExit::ForgPrep {
            base: *base,
            body_block: *body_block,
            exit_block: *exit_block,
        },
        RawBlockExit::ForgLoop {
            base,
            body_block,
            exit_block,
            result_count,
        } => BlockExit::ForgLoop {
            base: *base,
            body_block: *body_block,
            exit_block: *exit_block,
            result_count: *result_count,
        },
        RawBlockExit::Return { base, count } => match decoded_count(*count) {
            Count::Variadic => todo!(),
            Count::Number(n) => {
                let rets = (*base..*base + n)
                    .map(|i| {
                        let symbol = state[i as usize].unwrap_or_else(|| {
                            panic!("unbound register: {} while translating raw block exit", i)
                        });
                        HilExpr::Symbol(symbol)
                    })
                    .collect();
                BlockExit::Return(rets)
            }
        },
    }
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
            BlockExit::FornLoop { base, .. } => {
                numeric_loops_by_base.entry(base).or_default().push(idx)
            }
            BlockExit::ForgLoop { base, .. } => {
                generic_loops_by_base.entry(base).or_default().push(idx)
            }
            _ => {}
        }
    }

    (numeric_loops_by_base, generic_loops_by_base)
}

/// Folds Lua's `and/or` ternary pattern into a cohesive if-else control flow.
///
/// # Returns
///
/// A tuple of `(changed, blocks)` where `changed` is `true` if any short-circuit
/// folding was performed, and `blocks` is the modified block list.
fn fold_short_circuits(mut blocks: Vec<Block>) -> (bool, Vec<Block>) {
    // Lua itself lacks a native ternary operator, so `cond and x or y` compiles into
    // a diamond-shaped CFG: the condition is checked first, and if truthy, the result
    // register is checked again to guard against falsy `x` values.
    //
    //     A: if cond → B, C
    //     B: if x    → D, C   (x = MOVE of cond result; the "truthy guard")
    //     C: <fallback>
    //     D: <continuation>
    //
    // When we detect this shape (A and B share the same else-block C), we can
    // collapse it: emit `result = cond and x` into A, then re-target A's exit
    // to jump directly to D or C - eliminating the redundant block B in the process.

    let mut was_changed = false;
    for i in 0..blocks.len() {
        let (then_b, else_b, cond) = match &blocks[i].exit {
            BlockExit::CondJump {
                then_block,
                else_block,
                cond,
            } => (*then_block, *else_block, cond.clone()),
            _ => continue,
        };

        let (then_d, else_e) = match blocks.get(then_b).map(|b| &b.exit) {
            Some(BlockExit::CondJump {
                then_block,
                else_block,
                ..
            }) => (*then_block, *else_block),
            _ => continue,
        };

        if else_b != else_e {
            continue;
        }

        // This will match only if the then block has a single assignment
        // of a register to a register, which is the "truthy check" (Luau
        // needs to MOVE this register before the jump)
        if let [
            Spanned {
                inner:
                    HilStmt::Assign {
                        left: HilExpr::Symbol(result_reg),
                        value: HilExpr::Symbol(cond_expr),
                    },
                ..
            },
        ] = &blocks[then_b].stmts[..]
        {
            // copy out before the borrow dies
            let result_reg = *result_reg;
            let cond_expr = *cond_expr;
            // immutable borrow of self.blocks[then_b] ends here

            blocks[i].stmts.push(
                HilStmt::Assign {
                    left: HilExpr::Symbol(result_reg),
                    value: HilExpr::Binary {
                        lhs: Box::new(cond),
                        op: BinOp::And,
                        rhs: Box::new(HilExpr::Symbol(cond_expr)),
                    },
                }
                .to_spanned(0),
            );

            blocks[i].exit = BlockExit::CondJump {
                cond: HilExpr::Symbol(result_reg),
                then_block: then_d,
                else_block: else_b,
            };

            was_changed = true;
        }
    }

    (was_changed, blocks)
}
