use std::collections::BTreeSet;
use std::ops::Range;

use anyhow::{Result, anyhow, ensure};
use smallvec::SmallVec;

use crate::il::{DecodedInstr, Instr, Proto, reg_add, reg_range};
use crate::operator::BinOp;

/// Returns the list of instruction indices which are block entries.
fn find_block_entries(instrs: &[DecodedInstr]) -> Result<Vec<usize>> {
    let mut entries = BTreeSet::new();
    entries.insert(0);

    for (idx, decoded) in instrs.iter().enumerate() {
        match decoded.instr {
            Instr::Return { .. } if idx + 1 < instrs.len() => {
                entries.insert(idx + 1);
            }
            Instr::FornPrep { offset, .. }
            | Instr::ForgPrep { offset, .. }
            | Instr::ForgPrepInext { offset, .. }
            | Instr::ForgPrepNext { offset, .. } => {
                entries.insert(rel_target_from_instr(idx, offset.into(), instrs)?);
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::FornLoop { offset, .. } | Instr::ForgLoop { offset, .. } => {
                entries.insert(rel_target_from_instr(idx, offset.into(), instrs)?);
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::Jump { offset }
            | Instr::JumpBack { offset }
            | Instr::JumpIf { offset, .. }
            | Instr::JumpIfNot { offset, .. } => {
                entries.insert(rel_target_from_instr(idx, offset.into(), instrs)?);
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::JumpX { offset } => {
                entries.insert(rel_target_from_instr(idx, offset, instrs)?);
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
                entries.insert(rel_target_from_instr(idx, offset.into(), instrs)?);
                if idx + 1 < instrs.len() {
                    entries.insert(idx + 1);
                }
            }
            Instr::LoadB { jump, .. } if jump > 0 => {
                entries.insert(rel_target_from_instr(idx, jump.into(), instrs)?);
            }
            _ => {}
        }
    }

    Ok(entries.into_iter().collect())
}

/// Represents an unlifted block
#[derive(Debug)]
pub struct RawBlock {
    pub(crate) instr_range: Range<usize>,
    pub(crate) exit_writes: SmallVec<[u8; 4]>,
    pub(crate) exit: RawBlockExit,
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
    pub(crate) fn targets(&self) -> impl Iterator<Item = usize> {
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
        .into_iter()
        .flatten()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum CondRhs {
    /// A physical register
    Reg(u8),
    /// An index into the proto's constants
    Const(u32),
    /// Nil value
    Nil,
    /// A boolean value
    Bool(bool),
}

#[derive(Debug, Clone, Copy)]
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

/// Builds the bytecode-level blocks shared by flat and structured lifting.
pub fn build_raw_from_proto(proto: &Proto) -> Result<Vec<RawBlock>> {
    let entries = find_block_entries(&proto.instrs)?;
    let mut raw_blocks = Vec::with_capacity(entries.len());

    for (block_idx, &start) in entries.iter().enumerate() {
        let end = entries
            .get(block_idx + 1)
            .copied()
            .unwrap_or(proto.instrs.len());

        let Some(last_instr) = proto
            .instrs
            .get(end.saturating_sub(1))
            .map(|decoded| decoded.instr)
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

        let mut exit_writes = if last_instr.is_branch_exit() {
            last_instr.written_registers()
        } else {
            SmallVec::new()
        };

        let exit_instr_idx = end.saturating_sub(1);
        let exit = match exit_instr {
            Some(Instr::Return { base, count }) => RawBlockExit::Return { base, count },
            Some(Instr::Jump { offset }) | Some(Instr::JumpBack { offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                RawBlockExit::Jump(pc_to_block_idx(&entries, target))
            }
            Some(Instr::JumpX { offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset, &proto.instrs)?;
                RawBlockExit::Jump(pc_to_block_idx(&entries, target))
            }
            Some(Instr::JumpIfNotLt { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
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
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                RawBlockExit::CondJump {
                    cond: Cond::Unary(reg),
                    then_block: pc_to_block_idx(&entries, target),
                    else_block: block_idx + 1,
                }
            }
            Some(Instr::JumpIfNot { reg, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                RawBlockExit::CondJump {
                    cond: Cond::Unary(reg),
                    then_block: block_idx + 1,
                    else_block: pc_to_block_idx(&entries, target),
                }
            }
            Some(Instr::JumpIfEq { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
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
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
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
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
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
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Lte,
                        rhs: CondRhs::Reg(aux),
                    },
                    then_block: block_idx + 1,
                    else_block: pc_to_block_idx(&entries, target),
                }
            }
            Some(Instr::JumpIfLt { reg, aux, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
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
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
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
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
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
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                let (then_block, else_block) = if invert {
                    (block_idx + 1, pc_to_block_idx(&entries, target))
                } else {
                    (pc_to_block_idx(&entries, target), block_idx + 1)
                };
                RawBlockExit::CondJump {
                    cond: Cond::Binary {
                        lhs: reg,
                        op: BinOp::Eq,
                        rhs: CondRhs::Const(k),
                    },
                    then_block,
                    else_block,
                }
            }
            Some(Instr::FornPrep { base, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                RawBlockExit::FornPrep {
                    base,
                    body_block: block_idx + 1,
                    exit_block: pc_to_block_idx(&entries, target),
                }
            }
            Some(Instr::FornLoop { offset, .. }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                RawBlockExit::FornLoop {
                    body_block: pc_to_block_idx(&entries, target),
                    exit_block: block_idx + 1,
                }
            }
            Some(Instr::ForgPrep { base, offset })
            | Some(Instr::ForgPrepInext { base, offset })
            | Some(Instr::ForgPrepNext { base, offset }) => {
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                let exit_block = pc_to_block_idx(&entries, target);

                let end = entries
                    .get(exit_block + 1)
                    .copied()
                    .unwrap_or(proto.instrs.len());
                let result_count = match proto
                    .instrs
                    .get(end.saturating_sub(1))
                    .map(|decoded| decoded.instr)
                {
                    Some(Instr::ForgLoop { var_count, .. }) => Ok(var_count),
                    other => Err(anyhow!(
                        "FORGPREP target block must end in FORGLOOP, got {other:?}"
                    )),
                }?;

                exit_writes = reg_range(reg_add(base, 3), result_count).collect();

                RawBlockExit::ForgPrep {
                    base,
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
                let target = rel_target_from_instr(exit_instr_idx, offset.into(), &proto.instrs)?;
                RawBlockExit::ForgLoop {
                    base,
                    body_block: pc_to_block_idx(&entries, target),
                    exit_block: block_idx + 1,
                    result_count: usize::from(var_count),
                }
            }
            Some(Instr::LoadB { jump, .. }) if jump > 0 => {
                let target = rel_target_from_instr(exit_instr_idx, jump.into(), &proto.instrs)?;
                RawBlockExit::Jump(pc_to_block_idx(&entries, target))
            }
            _ => RawBlockExit::Fallthrough(block_idx + 1),
        };

        raw_blocks.push(RawBlock {
            instr_range: start..body_end,
            exit_writes,
            exit,
        });
    }

    Ok(raw_blocks)
}

/// Resolves a relative branch target from an instruction index.
fn rel_target_from_instr(instr_idx: usize, offset: i32, instrs: &[DecodedInstr]) -> Result<usize> {
    ensure!(!instrs.is_empty(), "instrs must not be empty");

    if instr_idx >= instrs.len() {
        let target = (instr_idx + 1).saturating_add_signed(offset as isize);
        ensure!(
            target < instrs.len(),
            "target instr {target} was out of range (max: {})",
            instrs.len() - 1
        );
        return Ok(target);
    }

    let target_word_pc = instrs[instr_idx]
        .word_pc
        .saturating_add(1)
        .saturating_add_signed(offset);

    instrs
        .binary_search_by(|decoded| decoded.word_pc.cmp(&target_word_pc))
        .map_err(|_| anyhow!("branch target {target_word_pc} does not point at an instruction"))
}

/// Maps an instruction PC to its containing basic block index.
#[inline]
#[must_use]
fn pc_to_block_idx(entries: &[usize], pc: usize) -> usize {
    assert!(!entries.is_empty());
    assert!(entries[0] <= pc);
    entries.partition_point(|&e| e <= pc) - 1
}
