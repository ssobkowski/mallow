use std::borrow::Cow;
use std::collections::BTreeSet;

use anyhow::{Result, anyhow};
use smallvec::{SmallVec, smallvec};

use crate::il::{DecodedInstr, Instr, Proto, reg_add, reg_range};
use crate::operator::BinOp;

/// Returns the list of instruction indices which are block entries.
fn find_block_entries(instrs: &[DecodedInstr]) -> Result<Vec<usize>> {
    let mut entries = BTreeSet::new();
    entries.insert(0);

    for (idx, decoded) in instrs.iter().enumerate() {
        if decoded.instr.branch_offset().is_some() {
            entries.insert(branch_target_idx(instrs, idx)?);
        }
        // LoadB jumps without ending its block, since it still assigns a register.
        if decoded.instr.is_branch_exit() && idx + 1 < instrs.len() {
            entries.insert(idx + 1);
        }
    }

    Ok(entries.into_iter().collect())
}

/// Represents an unlifted block
#[derive(Debug)]
pub struct RawBlock<'p> {
    pub(crate) instrs: Cow<'p, [DecodedInstr]>,
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
    #[inline]
    pub(crate) fn targets(&self) -> SmallVec<[usize; 2]> {
        match self {
            RawBlockExit::Jump(target) | RawBlockExit::Fallthrough(target) => smallvec![*target],
            RawBlockExit::CondJump {
                then_block,
                else_block,
                ..
            } => smallvec![*then_block, *else_block],
            RawBlockExit::FornPrep {
                body_block,
                exit_block,
                ..
            } => smallvec![*body_block, *exit_block],
            RawBlockExit::ForgPrep { body_block, .. } => smallvec![*body_block],
            RawBlockExit::FornLoop {
                body_block,
                exit_block,
                ..
            }
            | RawBlockExit::ForgLoop {
                body_block,
                exit_block,
                ..
            } => smallvec![*body_block, *exit_block],
            RawBlockExit::Return { .. } => SmallVec::new(),
        }
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
pub fn build_raw_from_proto<'p>(proto: &'p Proto) -> Result<Vec<RawBlock<'p>>> {
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
            Some(Instr::Jump { .. }) | Some(Instr::JumpBack { .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
                RawBlockExit::Jump(pc_to_block_idx(&entries, target))
            }
            Some(Instr::JumpX { .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
                RawBlockExit::Jump(pc_to_block_idx(&entries, target))
            }
            Some(Instr::JumpIfNotLt { reg, aux, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::JumpIf { reg, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
                RawBlockExit::CondJump {
                    cond: Cond::Unary(reg),
                    then_block: pc_to_block_idx(&entries, target),
                    else_block: block_idx + 1,
                }
            }
            Some(Instr::JumpIfNot { reg, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
                RawBlockExit::CondJump {
                    cond: Cond::Unary(reg),
                    then_block: block_idx + 1,
                    else_block: pc_to_block_idx(&entries, target),
                }
            }
            Some(Instr::JumpIfEq { reg, aux, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::JumpIfNotEq { reg, aux, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::JumpIfLe { reg, aux, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::JumpIfNotLe { reg, aux, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::JumpIfLt { reg, aux, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::JumpXEqKNil { reg, invert, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::JumpXEqKB { reg, k, invert, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::JumpXEqKN { reg, k, invert, .. })
            | Some(Instr::JumpXEqKS { reg, k, invert, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
            Some(Instr::FornPrep { base, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
                RawBlockExit::FornPrep {
                    base,
                    body_block: block_idx + 1,
                    exit_block: pc_to_block_idx(&entries, target),
                }
            }
            Some(Instr::FornLoop { .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
                RawBlockExit::FornLoop {
                    body_block: pc_to_block_idx(&entries, target),
                    exit_block: block_idx + 1,
                }
            }
            Some(Instr::ForgPrep { base, .. })
            | Some(Instr::ForgPrepInext { base, .. })
            | Some(Instr::ForgPrepNext { base, .. }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
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
                base, var_count, ..
            }) => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
                RawBlockExit::ForgLoop {
                    base,
                    body_block: pc_to_block_idx(&entries, target),
                    exit_block: block_idx + 1,
                    result_count: usize::from(var_count),
                }
            }
            Some(Instr::LoadB { jump, .. }) if jump > 0 => {
                let target = branch_target_idx(&proto.instrs, exit_instr_idx)?;
                RawBlockExit::Jump(pc_to_block_idx(&entries, target))
            }
            _ => RawBlockExit::Fallthrough(block_idx + 1),
        };

        raw_blocks.push(RawBlock {
            instrs: Cow::Borrowed(&proto.instrs[start..body_end]),
            exit_writes,
            exit,
        });
    }

    Ok(raw_blocks)
}

/// Resolves the instruction index the branch at `instr_idx` targets.
fn branch_target_idx(instrs: &[DecodedInstr], instr_idx: usize) -> Result<usize> {
    let decoded = instrs
        .get(instr_idx)
        .ok_or_else(|| anyhow!("instr {instr_idx} was out of range"))?;
    let target_word_pc = decoded
        .branch_target()
        .ok_or_else(|| anyhow!("instr {instr_idx} ({}) does not branch", decoded.instr))?;

    instrs
        .binary_search_by(|decoded| decoded.word_pc.cmp(&target_word_pc))
        .map_err(|_| anyhow!("branch target {target_word_pc} does not point at an instruction"))
}

/// Maps an instruction PC to its containing basic block index.
#[inline]
fn pc_to_block_idx(entries: &[usize], pc: usize) -> usize {
    assert!(!entries.is_empty());
    assert!(entries[0] <= pc);
    entries.partition_point(|&e| e <= pc) - 1
}
