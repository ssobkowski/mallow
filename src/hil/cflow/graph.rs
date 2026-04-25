use std::{
    collections::{BTreeSet, HashMap, HashSet},
    ops::Range,
};

use id_arena::Arena;
use smallvec::SmallVec;

use crate::{
    ast::BinOp,
    disasm::Proto,
    hil::{
        cflow::union_find::UnionFind,
        common::{const_expr, decoded_count},
        ir::{HilExpr, HilStmt, HilTableItem, PhiNode, Spanned, ToSpanned as _},
        lifter::{
            LiftContext, lift,
            ssa::{Ssa, Symbol, SymbolId, SymbolKind},
        },
    },
    il::{Count, Instr},
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
    pub immediate_dominators: Vec<Option<usize>>,

    pub params: Vec<SymbolId>,
    pub upvalues: Vec<SymbolId>,
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
                    entries.insert(rel_target_from_instr(idx, (*offset).into(), instrs));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::FornLoop { offset, .. } | Instr::ForgLoop { offset, .. } => {
                    entries.insert(rel_target_from_instr(idx, (*offset).into(), instrs));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::Jump { offset }
                | Instr::JumpBack { offset }
                | Instr::JumpIf { offset, .. }
                | Instr::JumpIfNot { offset, .. } => {
                    entries.insert(rel_target_from_instr(idx, (*offset).into(), instrs));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::JumpX { offset } => {
                    entries.insert(rel_target_from_instr(idx, *offset, instrs));
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
                    entries.insert(rel_target_from_instr(idx, (*offset).into(), instrs));
                    if idx + 1 < instrs.len() {
                        entries.insert(idx + 1);
                    }
                }
                Instr::LoadB { jump, .. } if *jump > 0 => {
                    entries.insert(rel_target_from_instr(idx, (*jump).into(), instrs));
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
            let exit_writes = if is_branch_or_return {
                last_instr.written_registers()
            } else {
                SmallVec::new()
            };

            let exit_instr_idx = end.saturating_sub(1);
            let exit = match exit_instr.copied() {
                Some(Instr::Return { base, count }) => RawBlockExit::Return { base, count },
                Some(Instr::Jump { offset }) | Some(Instr::JumpBack { offset }) => {
                    let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                    RawBlockExit::Jump(pc_to_block_idx(&entries, target))
                }
                Some(Instr::JumpX { offset }) => {
                    let target = rel_target_from_instr(exit_instr_idx, offset, instrs);
                    RawBlockExit::Jump(pc_to_block_idx(&entries, target))
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
                        else_block: pc_to_block_idx(&entries, target),
                    }
                }
                Some(Instr::JumpIf { reg, offset }) => {
                    let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Unary(reg),
                        then_block: pc_to_block_idx(&entries, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfNot { reg, offset }) => {
                    let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Unary(reg),
                        then_block: block_idx + 1,
                        else_block: pc_to_block_idx(&entries, target),
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
                        then_block: pc_to_block_idx(&entries, target),
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
                        then_block: pc_to_block_idx(&entries, target),
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
                        then_block: pc_to_block_idx(&entries, target),
                        else_block: block_idx + 1,
                    }
                }
                Some(Instr::JumpIfNotLe { reg, aux, offset }) => {
                    let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                    RawBlockExit::CondJump {
                        cond: Cond::Binary {
                            lhs: reg,
                            op: BinOp::Gt,
                            rhs: CondRhs::Reg(aux),
                        },
                        then_block: pc_to_block_idx(&entries, target),
                        else_block: block_idx + 1,
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
                        then_block: pc_to_block_idx(&entries, target),
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
                    let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
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
                    let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
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
                    let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                    RawBlockExit::FornPrep {
                        base,
                        body_block: block_idx + 1,
                        exit_block: pc_to_block_idx(&entries, target),
                    }
                }
                Some(Instr::FornLoop { base, offset }) => {
                    let target = rel_target_from_instr(exit_instr_idx, offset.into(), instrs);
                    RawBlockExit::FornLoop {
                        base,
                        body_block: pc_to_block_idx(&entries, target),
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
                        exit_block: pc_to_block_idx(&entries, target),
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
                        body_block: pc_to_block_idx(&entries, target),
                        exit_block: block_idx + 1,
                        result_count: usize::from(var_count),
                    }
                }
                Some(Instr::LoadB { jump, .. }) if jump > 0 => {
                    let target = rel_target_from_instr(exit_instr_idx, jump.into(), instrs);
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

        let successors = build_successors(raw_blocks.iter().map(|b| b.exit.targets()));
        let predecessors = build_predecessors(&successors);

        let mut arena = Arena::new();
        let mut blocks: Vec<Block> = vec![Block::dummy(); raw_blocks.len()];
        let mut ssa = Ssa::new(&predecessors, &mut arena);

        let mut params = Vec::with_capacity(proto.num_params as usize);
        for i in 0..proto.num_params {
            let sym = ssa.alloc_symbol(Symbol::param(i));
            ssa.write_reg(0, i, sym);
            params.push(sym);
        }

        for i in 0..proto.num_upvals {
            let sym = ssa.alloc_symbol(Symbol::upval(i));
            ssa.write_upval(0, i, sym);
        }

        for block_id in compute_rpo(0, &successors) {
            let (mut stmts, mut pending_multiret) = lift(LiftContext {
                instrs: &instrs[raw_blocks[block_id].instr_range.clone()],
                consts: &proto.consts,
                parent_proto: proto,
                protos: all_protos,
                ssa: &mut ssa,
                block_idx: block_id,
            });

            // Some terminators, such as FORGLOOP, write registers even though they
            // are modeled as block exits and never pass through the lifter.
            for &reg in &raw_blocks[block_id].exit_writes {
                let sym = ssa.alloc_symbol(Symbol::reg(reg));
                ssa.write_reg(block_id, reg, sym);
            }

            let exit = match &raw_blocks[block_id].exit {
                RawBlockExit::Jump(t) => BlockExit::Jump(*t),
                RawBlockExit::Fallthrough(t) => BlockExit::Fallthrough(*t),
                RawBlockExit::CondJump {
                    cond,
                    then_block,
                    else_block,
                } => {
                    let hil_cond = match cond {
                        Cond::Unary(reg) => HilExpr::Symbol(ssa.read_reg(block_id, *reg)),
                        Cond::Binary { lhs, op, rhs } => {
                            let lhs_expr = HilExpr::Symbol(ssa.read_reg(block_id, *lhs));
                            let rhs_expr = match rhs {
                                CondRhs::Reg(r) => HilExpr::Symbol(ssa.read_reg(block_id, *r)),
                                CondRhs::Const(idx) => const_expr(&proto.consts, *idx),
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
                } => {
                    let var = ssa.read_reg(*body_block, *base + 2);
                    let start = ssa.read_reg(block_id, *base + 2);
                    let end = ssa.read_reg(block_id, *base);
                    let step = ssa.read_reg(block_id, *base + 1);
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
                } => BlockExit::FornLoop {
                    base: *base,
                    body_block: *body_block,
                    exit_block: *exit_block,
                },
                RawBlockExit::ForgPrep {
                    base,
                    body_block,
                    exit_block,
                } => {
                    let exprs = [
                        HilExpr::Symbol(ssa.read_reg(block_id, *base)),
                        HilExpr::Symbol(ssa.read_reg(block_id, *base + 1)),
                        HilExpr::Symbol(ssa.read_reg(block_id, *base + 2)),
                    ];
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
                } => BlockExit::ForgLoop {
                    base: *base,
                    body_block: *body_block,
                    exit_block: *exit_block,
                    vars: (0..*result_count)
                        .map(|i| ssa.read_reg(*body_block, *base + 3 + i as u8))
                        .collect(),
                },
                RawBlockExit::Return { base, count } => match decoded_count(*count) {
                    Count::Variadic => {
                        let mut rets = SmallVec::new();
                        if let Some(multiret) = pending_multiret.take() {
                            if multiret.base >= *base {
                                for i in *base..multiret.base {
                                    rets.push(HilExpr::Symbol(ssa.read_reg(block_id, i)));
                                }
                            }
                            rets.push(multiret.expr.inner);
                        } else {
                            // No multiret, just return the base register
                            rets.push(HilExpr::Symbol(ssa.read_reg(block_id, *base)));
                        }
                        BlockExit::Return(rets)
                    }
                    Count::Number(n) => {
                        let rets = (*base..*base + n)
                            .map(|i| {
                                let sym = ssa.read_reg(block_id, i);
                                HilExpr::Symbol(sym)
                            })
                            .collect();
                        BlockExit::Return(rets)
                    }
                },
            };

            if let Some(multiret) = pending_multiret {
                match multiret.expr.inner {
                    HilExpr::Call { .. } | HilExpr::MethodCall { .. } => {
                        stmts.push(HilStmt::Call(multiret.expr.inner).to_spanned(multiret.expr.pc));
                    }
                    HilExpr::VarArgs => {
                        let sym = ssa.alloc_symbol(Symbol::reg(multiret.base));
                        ssa.write_reg(block_id, multiret.base, sym);

                        stmts.push(
                            HilStmt::Assign {
                                left: HilExpr::Symbol(sym),
                                value: HilExpr::VarArgs,
                            }
                            .to_spanned(multiret.expr.pc),
                        );
                    }
                    _ => unreachable!("unexpected deferred variadic source"),
                }
            }

            blocks[block_id] = Block { stmts, exit };
            ssa.mark_filled(block_id);
        }

        let live_in_regs = compute_live_in_registers(&blocks, &raw_blocks, &successors, &ssa);

        for (src, targets) in successors.iter().enumerate() {
            for &target in targets {
                if target <= src {
                    if matches!(
                        &raw_blocks[src].exit,
                        RawBlockExit::FornLoop { .. } | RawBlockExit::ForgLoop { .. }
                    ) {
                        continue;
                    }

                    let mut loop_body = HashSet::new();
                    loop_body.insert(target);
                    let mut worklist = vec![src];
                    while let Some(b) = worklist.pop() {
                        if loop_body.insert(b) {
                            worklist.extend(&predecessors[b]);
                        }
                    }

                    let mut written_regs = HashSet::new();
                    for &block_id in &loop_body {
                        for (instr, _) in &instrs[raw_blocks[block_id].instr_range.clone()] {
                            written_regs.extend(instr.written_registers());
                        }
                        written_regs.extend(raw_blocks[block_id].exit_writes.clone());
                    }

                    let loop_live_out =
                        compute_loop_live_out_regs(&loop_body, &successors, &live_in_regs);

                    for u in 0..proto.num_upvals {
                        ssa.read_upval(target, u);
                    }

                    for reg in written_regs {
                        if live_in_regs[target].contains(&reg) || loop_live_out.contains(&reg) {
                            ssa.read_reg(target, reg);
                        }
                    }
                }
            }
        }

        ssa.seal_blocks();
        ssa.finish(&mut blocks);

        let mut disjoint_set = UnionFind::new();
        for (block_idx, block) in blocks.iter().enumerate() {
            for stmt in &block.stmts {
                if let HilStmt::Phi(phi) = &stmt.inner {
                    for (pred_block, operand) in &phi.operands {
                        if is_loop_header_loop_var_operand(
                            &blocks,
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

        // Unify all versions of the same upvalue.
        let mut upval_versions: HashMap<_, Vec<_>> = HashMap::new();
        for (id, symbol) in ssa.arena_iter() {
            if let SymbolKind::Upvalue(idx) = symbol.kind {
                upval_versions.entry(idx).or_default().push(id);
            }
        }

        for versions in upval_versions.values() {
            for i in 1..versions.len() {
                disjoint_set.union(versions[0], versions[i]);
            }
        }

        // Unify captured-by-reference register versions by their lifetime
        // generation. The lifter tags these as `CapturedRegister`; a
        // `CLOSEUPVALS` starts a new generation and register reuse after that
        // must remain distinct.
        let mut captured_versions: HashMap<_, Vec<_>> = HashMap::new();
        for (id, symbol) in ssa.arena_iter() {
            if let SymbolKind::CapturedRegister { reg, generation } = symbol.kind {
                captured_versions
                    .entry((reg, generation))
                    .or_default()
                    .push(id);
            }
        }

        for versions in captured_versions.values() {
            for i in 1..versions.len() {
                disjoint_set.union(versions[0], versions[i]);
            }
        }

        resolve_ssa_symbols(&mut blocks, &ssa, &mut disjoint_set);

        for sym in &mut params {
            *sym = disjoint_set.find(ssa.resolve(*sym));
        }

        let mut upvalues = Vec::with_capacity(proto.num_upvals as usize);
        for i in 0..proto.num_upvals {
            // Find any symbol for upvalue i and resolve its canonical id
            let id = ssa
                .arena_iter()
                .find_map(|(id, sym)| {
                    if let SymbolKind::Upvalue(idx) = sym.kind
                        && idx == i
                    {
                        return Some(id);
                    }
                    None
                })
                .unwrap();
            upvalues.push(disjoint_set.find(id));
        }

        loop {
            let changed_cond = fold_constant_cond_jumps(&mut blocks);
            let changed_jump = thread_jumps(&mut blocks);
            if !changed_cond && !changed_jump {
                break;
            }
        }

        let blocks = loop {
            let successors = build_successors(blocks.iter().map(|b| b.exit_targets()));
            let predecessors = build_predecessors(&successors);
            let (changed_cond, new_blocks) = fold_condition_chains(blocks, &predecessors);

            let successors = build_successors(new_blocks.iter().map(|b| b.exit_targets()));
            let predecessors = build_predecessors(&successors);
            let (changed_dup, new_blocks) =
                duplicate_shared_falsy_fallbacks(new_blocks, &predecessors);

            if !changed_cond && !changed_dup {
                break new_blocks;
            }
            blocks = new_blocks;
        };

        // Rebuild after folding
        let successors = build_successors(blocks.iter().map(|b| b.exit_targets()));
        let predecessors = build_predecessors(&successors);
        let immediate_dominators = build_immediate_dominators(0, &successors, &predecessors);

        let mut graph = Self {
            blocks,
            entry_block: 0,
            successors,
            predecessors,
            immediate_dominators,
            params,
            upvalues,
        };
        for i in 0..graph.blocks.len() {
            graph.unfold_phis(i);
        }
        graph
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
    #[cfg(feature = "visualize")]
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

    /// Unfolds Phi Nodes into assign statements inserted at appropriate locations.
    ///
    /// This should be ran after the graph metadata has been computed.
    fn unfold_phis(&mut self, block_idx: usize) {
        let Some(idom) = self.immediate_dominator(block_idx) else {
            // This block has no immediate dominator, we can't emit the phi node
            // target declaration anywhere.
            return;
        };

        let mut loop_header_targets = HashSet::new();
        for pred_idx in self.predecessors(block_idx) {
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
            .extract_if(.., |stmt| matches!(stmt.inner, HilStmt::Phi { .. }))
            .map(|stmt| {
                let HilStmt::Phi(PhiNode { target, operands }) = stmt.inner else {
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

/// Determines whether a given Phi node operand comes from a loop preheader
/// and targets the loop's internal iteration variables.
///
/// During SSA construction, Phi nodes are inserted at loop headers to merge
/// values from the preheader (before the loop) and the latch (end of the loop).
/// However, for Luau `for` loops, the iteration variables are initialized *by* the
/// loop setup opcodes (`FornPrep` / `ForgPrep`), effectively shadowing whatever
/// data was in those physical registers previously.
///
/// If the union-find algorithm links the loop variable's Phi target
/// with the preheader's operand, the loop variable will incorrectly fuse with
/// completely unrelated variables that just happened to share the same physical
/// register earlier in the function (causing scope bleeding and duplicate variable
/// declarations). This function identifies those specific operands so the
/// SSA resolver can ignore them.
#[must_use]
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

fn symbol_truthiness_in_block(block: &Block, symbol: SymbolId) -> Option<bool> {
    block.stmts.iter().find_map(|stmt| {
        let HilStmt::Assign {
            left: HilExpr::Symbol(target),
            value,
        } = &stmt.inner
        else {
            return None;
        };

        (*target == symbol)
            .then_some(value)
            .and_then(|value| value.truthiness())
    })
}

fn fold_constant_cond_jumps(blocks: &mut [Block]) -> bool {
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

/// Duplicates simple fallback blocks shared by multiple falsy short-circuit edges.
///
/// The bytecode for nested `and/or` expressions often has several failed truthiness
/// checks converge on the same fallback assignment block. That block is semantically
/// just "run this fallback for this failed edge", but the shared predecessor set is
/// not a single-entry region and prevents structured `if not value then ... end`
/// output. Tail-duplicating the fallback preserves the CFG semantics while making
/// each falsy edge own a normal branch body.
fn duplicate_shared_falsy_fallbacks(
    mut blocks: Vec<Block>,
    predecessors: &[Vec<usize>],
) -> (bool, Vec<Block>) {
    let successors = build_successors(blocks.iter().map(|block| block.exit_targets()));
    let mut rewrites = Vec::new();

    for (target, preds) in predecessors.iter().enumerate() {
        if preds.len() <= 1 || !is_duplicateable_fallback(&blocks[target]) {
            continue;
        }

        if preds
            .iter()
            .any(|&pred| is_reachable(&successors, target, pred))
        {
            continue;
        }

        if !preds.iter().all(|&pred| {
            matches!(
                blocks[pred].exit,
                BlockExit::CondJump {
                    then_block,
                    else_block,
                    ..
                } if then_block == target || else_block == target
            )
        }) {
            continue;
        }

        rewrites.extend(preds.iter().skip(1).map(|&pred| (pred, target)));
    }

    if rewrites.is_empty() {
        return (false, blocks);
    }

    for (pred, target) in rewrites {
        let clone_target = blocks.len();
        blocks.push(blocks[target].clone());
        replace_exit_target(&mut blocks[pred].exit, target, clone_target);
    }

    (true, blocks)
}

fn is_reachable(successors: &[Vec<usize>], start: usize, target: usize) -> bool {
    let mut stack = vec![start];
    let mut seen = vec![false; successors.len()];

    while let Some(node) = stack.pop() {
        if node == target {
            return true;
        }

        if std::mem::replace(&mut seen[node], true) {
            continue;
        }

        stack.extend(successors[node].iter().copied());
    }

    false
}

fn is_duplicateable_fallback(block: &Block) -> bool {
    if block.stmts.is_empty() {
        return matches!(block.exit, BlockExit::CondJump { .. });
    }

    if !block
        .stmts
        .iter()
        .all(|stmt| matches!(stmt.inner, HilStmt::Assign { .. }))
    {
        return false;
    }

    match block.exit {
        BlockExit::Jump(_) | BlockExit::Fallthrough(_) => true,
        BlockExit::CondJump {
            cond: HilExpr::Symbol(cond),
            ..
        } => block.stmts.iter().any(|stmt| {
            matches!(
                stmt.inner,
                HilStmt::Assign {
                    left: HilExpr::Symbol(symbol),
                    ..
                } if symbol == cond
            )
        }),
        _ => false,
    }
}

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
            && is_safe_to_hoist_across_condition(&blocks[then_a], &cond_a)
            && let BlockExit::CondJump {
                cond: cond_b,
                then_block: then_b,
                else_block: else_b,
            } = blocks[then_a].exit.clone()
            && !block_assigns_condition_symbol(&blocks[then_a], &cond_b)
            && else_a == else_b
        {
            let mut stmts = std::mem::take(&mut blocks[then_a].stmts);
            blocks[i].stmts.append(&mut stmts);

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
            && is_safe_to_hoist_across_condition(&blocks[else_a], &cond_a)
            && let BlockExit::CondJump {
                cond: cond_b,
                then_block: then_b,
                else_block: else_b,
            } = blocks[else_a].exit.clone()
            && !block_assigns_condition_symbol(&blocks[else_a], &cond_b)
            && then_a == then_b
        {
            let mut stmts = std::mem::take(&mut blocks[else_a].stmts);
            blocks[i].stmts.append(&mut stmts);

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

fn block_assigns_condition_symbol(block: &Block, condition: &HilExpr) -> bool {
    let HilExpr::Symbol(cond_symbol) = condition else {
        return false;
    };

    block.stmts.iter().any(|stmt| {
        matches!(
            stmt.inner,
            HilStmt::Assign {
                left: HilExpr::Symbol(symbol),
                ..
            } if symbol == *cond_symbol
        )
    })
}

fn replace_exit_target(exit: &mut BlockExit, old_target: usize, new_target: usize) {
    match exit {
        BlockExit::Jump(target)
        | BlockExit::Fallthrough(target)
        | BlockExit::FornLoop {
            body_block: target, ..
        }
        | BlockExit::ForgLoop {
            body_block: target, ..
        } if *target == old_target => {
            *target = new_target;
        }
        BlockExit::CondJump {
            then_block,
            else_block,
            ..
        } => {
            if *then_block == old_target {
                *then_block = new_target;
            }
            if *else_block == old_target {
                *else_block = new_target;
            }
        }
        BlockExit::FornPrep {
            body_block,
            exit_block,
            ..
        }
        | BlockExit::ForgPrep {
            body_block,
            exit_block,
            ..
        } => {
            if *body_block == old_target {
                *body_block = new_target;
            }
            if *exit_block == old_target {
                *exit_block = new_target;
            }
        }
        BlockExit::FornLoop { exit_block, .. } | BlockExit::ForgLoop { exit_block, .. } => {
            if *exit_block == old_target {
                *exit_block = new_target;
            }
        }
        BlockExit::Return(_) | BlockExit::Jump(_) | BlockExit::Fallthrough(_) => {}
    }
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
                    BlockExit::Jump(next) | BlockExit::Fallthrough(next) => {
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

fn resolve_ssa_symbols(blocks: &mut [Block], ssa: &Ssa, djs: &mut UnionFind<SymbolId>) {
    fn resolve(sym: &mut SymbolId, ssa: &Ssa, djs: &mut UnionFind<SymbolId>) {
        let resolved = ssa.resolve(*sym);
        *sym = djs.find(resolved);
    }

    fn walk_stmt(stmt: &mut HilStmt, ssa: &Ssa, djs: &mut UnionFind<SymbolId>) {
        match stmt {
            HilStmt::Assign { left, value } => {
                walk_expr(left, ssa, djs);
                walk_expr(value, ssa, djs);
            }
            HilStmt::AssignMany { left, value } => {
                for lvalue in left {
                    walk_expr(lvalue, ssa, djs);
                }
                walk_expr(value, ssa, djs);
            }
            HilStmt::Call(expr) => walk_expr(expr, ssa, djs),
            HilStmt::SetList { table, values, .. } => {
                resolve(table, ssa, djs);
                for v in values {
                    walk_expr(v, ssa, djs);
                }
            }
            HilStmt::Phi(phi) => {
                resolve(&mut phi.target, ssa, djs);
                for (_, op) in &mut phi.operands {
                    resolve(op, ssa, djs);
                }
            }
        }
    }

    fn walk_expr(expr: &mut HilExpr, ssa: &Ssa, djs: &mut UnionFind<SymbolId>) {
        match expr {
            HilExpr::Symbol(sym) => {
                resolve(sym, ssa, djs);
            }
            HilExpr::Closure { captures, .. } => {
                for capture in captures {
                    resolve(capture, ssa, djs);
                }
            }
            HilExpr::GetField { obj, .. } => {
                walk_expr(obj, ssa, djs);
            }
            HilExpr::GetIndex { obj, index } => {
                walk_expr(obj, ssa, djs);
                walk_expr(index, ssa, djs);
            }
            HilExpr::Call { fun, args } => {
                walk_expr(fun, ssa, djs);
                for arg in args {
                    walk_expr(arg, ssa, djs);
                }
            }
            HilExpr::MethodCall { object, args, .. } => {
                walk_expr(object, ssa, djs);
                for arg in args {
                    walk_expr(arg, ssa, djs);
                }
            }
            HilExpr::Binary { lhs, rhs, .. } => {
                walk_expr(lhs, ssa, djs);
                walk_expr(rhs, ssa, djs);
            }
            HilExpr::Unary { expr, .. } => {
                walk_expr(expr, ssa, djs);
            }
            HilExpr::Table { items } => {
                for item in items {
                    match item {
                        HilTableItem::List(expr) => walk_expr(expr, ssa, djs),
                        HilTableItem::Index(k, v) => {
                            walk_expr(k, ssa, djs);
                            walk_expr(v, ssa, djs);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn walk_exit(exit: &mut BlockExit, ssa: &Ssa, djs: &mut UnionFind<SymbolId>) {
        match exit {
            BlockExit::CondJump { cond, .. } => {
                walk_expr(cond, ssa, djs);
            }
            BlockExit::FornPrep {
                var,
                start,
                end,
                step,
                ..
            } => {
                resolve(var, ssa, djs);
                walk_expr(start, ssa, djs);
                walk_expr(end, ssa, djs);
                walk_expr(step, ssa, djs);
            }
            BlockExit::ForgPrep { exprs, .. } => {
                for e in exprs {
                    walk_expr(e, ssa, djs);
                }
            }
            BlockExit::ForgLoop { vars, .. } => {
                for v in vars {
                    resolve(v, ssa, djs);
                }
            }
            BlockExit::Return(values) => {
                for v in values {
                    walk_expr(v, ssa, djs);
                }
            }
            _ => {}
        }
    }

    for block in blocks {
        for stmt in &mut block.stmts {
            walk_stmt(&mut stmt.inner, ssa, djs);
        }
        walk_exit(&mut block.exit, ssa, djs);
    }
}

fn is_safe_to_hoist_across_condition(block: &Block, condition: &HilExpr) -> bool {
    if !block.stmts.is_empty()
        && block.stmts.iter().all(|stmt| {
            matches!(
                &stmt.inner,
                HilStmt::Assign { value, .. } if is_condition_prelude_value(value)
            )
        })
    {
        return false;
    }

    block.stmts.iter().all(|stmt| {
        let HilStmt::Assign { left, value } = &stmt.inner else {
            return false;
        };

        value.is_pure()
            && !matches!(
                (left, condition),
                (HilExpr::Symbol(assigned), HilExpr::Symbol(cond)) if assigned == cond
            )
    })
}

fn is_condition_prelude_value(expr: &HilExpr) -> bool {
    matches!(
        expr,
        HilExpr::Nil
            | HilExpr::Number(_)
            | HilExpr::String(_)
            | HilExpr::Bool(_)
            | HilExpr::Symbol(_)
            | HilExpr::Import(_)
            | HilExpr::Global(_)
    )
}

fn symbol_register_map(ssa: &Ssa) -> HashMap<SymbolId, u8> {
    ssa.arena_iter()
        .filter_map(|(id, sym)| match sym.kind {
            SymbolKind::Register(reg) | SymbolKind::CapturedRegister { reg, .. } => Some((id, reg)),
            _ => None,
        })
        .collect()
}

fn note_reg_use(
    sym: SymbolId,
    reg_of: &HashMap<SymbolId, u8>,
    uses: &mut HashSet<u8>,
    seen_defs: &HashSet<u8>,
) {
    if let Some(&reg) = reg_of.get(&sym)
        && !seen_defs.contains(&reg)
    {
        uses.insert(reg);
    }
}

fn collect_expr_reg_uses(
    expr: &HilExpr,
    reg_of: &HashMap<SymbolId, u8>,
    uses: &mut HashSet<u8>,
    seen_defs: &HashSet<u8>,
) {
    match expr {
        HilExpr::Symbol(sym) => note_reg_use(*sym, reg_of, uses, seen_defs),
        HilExpr::Closure { captures, .. } => {
            for capture in captures {
                note_reg_use(*capture, reg_of, uses, seen_defs);
            }
        }
        HilExpr::GetField { obj, .. } => {
            collect_expr_reg_uses(obj, reg_of, uses, seen_defs);
        }
        HilExpr::GetIndex { obj, index } => {
            collect_expr_reg_uses(obj, reg_of, uses, seen_defs);
            collect_expr_reg_uses(index, reg_of, uses, seen_defs);
        }
        HilExpr::Call { fun, args } => {
            collect_expr_reg_uses(fun, reg_of, uses, seen_defs);
            for arg in args {
                collect_expr_reg_uses(arg, reg_of, uses, seen_defs);
            }
        }
        HilExpr::MethodCall { object, args, .. } => {
            collect_expr_reg_uses(object, reg_of, uses, seen_defs);
            for arg in args {
                collect_expr_reg_uses(arg, reg_of, uses, seen_defs);
            }
        }
        HilExpr::Binary { lhs, rhs, .. } => {
            collect_expr_reg_uses(lhs, reg_of, uses, seen_defs);
            collect_expr_reg_uses(rhs, reg_of, uses, seen_defs);
        }
        HilExpr::Unary { expr, .. } => {
            collect_expr_reg_uses(expr, reg_of, uses, seen_defs);
        }
        HilExpr::Table { items } => {
            for item in items {
                match item {
                    HilTableItem::List(expr) => {
                        collect_expr_reg_uses(expr, reg_of, uses, seen_defs);
                    }
                    HilTableItem::Index(k, v) => {
                        collect_expr_reg_uses(k, reg_of, uses, seen_defs);
                        collect_expr_reg_uses(v, reg_of, uses, seen_defs);
                    }
                }
            }
        }
        _ => {}
    }
}

fn collect_lvalue_reg_use_def(
    lvalue: &HilExpr,
    reg_of: &HashMap<SymbolId, u8>,
    uses: &mut HashSet<u8>,
    defs: &mut HashSet<u8>,
    seen_defs: &mut HashSet<u8>,
) {
    match lvalue {
        HilExpr::Symbol(sym) => {
            if let Some(&reg) = reg_of.get(sym) {
                defs.insert(reg);
                seen_defs.insert(reg);
            }
        }
        _ => {
            collect_expr_reg_uses(lvalue, reg_of, uses, seen_defs);
        }
    }
}

fn collect_stmt_reg_use_def(
    stmt: &HilStmt,
    reg_of: &HashMap<SymbolId, u8>,
    uses: &mut HashSet<u8>,
    defs: &mut HashSet<u8>,
    seen_defs: &mut HashSet<u8>,
) {
    match stmt {
        HilStmt::Assign { left, value } => {
            collect_expr_reg_uses(value, reg_of, uses, seen_defs);
            collect_lvalue_reg_use_def(left, reg_of, uses, defs, seen_defs);
        }
        HilStmt::AssignMany { left, value } => {
            collect_expr_reg_uses(value, reg_of, uses, seen_defs);
            for lvalue in left {
                match lvalue {
                    HilExpr::Symbol(sym) => {
                        if let Some(&reg) = reg_of.get(sym) {
                            defs.insert(reg);
                            seen_defs.insert(reg);
                        }
                    }
                    _ => {
                        collect_lvalue_reg_use_def(lvalue, reg_of, uses, defs, seen_defs);
                    }
                }
            }
        }
        HilStmt::Call(expr) => {
            collect_expr_reg_uses(expr, reg_of, uses, seen_defs);
        }
        HilStmt::SetList { table, values, .. } => {
            note_reg_use(*table, reg_of, uses, seen_defs);
            for value in values {
                collect_expr_reg_uses(value, reg_of, uses, seen_defs);
            }
        }
        HilStmt::Phi(phi) => {
            if let Some(&reg) = reg_of.get(&phi.target) {
                defs.insert(reg);
                seen_defs.insert(reg);
            }
        }
    }
}

fn collect_exit_reg_uses(
    exit: &BlockExit,
    reg_of: &HashMap<SymbolId, u8>,
    uses: &mut HashSet<u8>,
    seen_defs: &HashSet<u8>,
) {
    match exit {
        BlockExit::CondJump { cond, .. } => {
            collect_expr_reg_uses(cond, reg_of, uses, seen_defs);
        }
        BlockExit::FornPrep {
            start, end, step, ..
        } => {
            collect_expr_reg_uses(start, reg_of, uses, seen_defs);
            collect_expr_reg_uses(end, reg_of, uses, seen_defs);
            collect_expr_reg_uses(step, reg_of, uses, seen_defs);
        }
        BlockExit::ForgPrep { exprs, .. } => {
            for expr in exprs {
                collect_expr_reg_uses(expr, reg_of, uses, seen_defs);
            }
        }
        BlockExit::Return(values) => {
            for value in values {
                collect_expr_reg_uses(value, reg_of, uses, seen_defs);
            }
        }
        _ => {}
    }
}

fn compute_live_in_registers(
    blocks: &[Block],
    raw_blocks: &[RawBlock],
    successors: &[Vec<usize>],
    ssa: &Ssa,
) -> Vec<HashSet<u8>> {
    let reg_of = symbol_register_map(ssa);

    let mut block_uses = vec![HashSet::new(); blocks.len()];
    let mut block_defs = vec![HashSet::new(); blocks.len()];

    for (block_idx, block) in blocks.iter().enumerate() {
        let mut seen_defs = HashSet::new();

        for stmt in &block.stmts {
            collect_stmt_reg_use_def(
                &stmt.inner,
                &reg_of,
                &mut block_uses[block_idx],
                &mut block_defs[block_idx],
                &mut seen_defs,
            );
        }

        collect_exit_reg_uses(&block.exit, &reg_of, &mut block_uses[block_idx], &seen_defs);

        block_defs[block_idx].extend(raw_blocks[block_idx].exit_writes.iter().copied());
    }

    let mut live_in = vec![HashSet::new(); blocks.len()];
    let mut live_out = vec![HashSet::new(); blocks.len()];

    let mut changed = true;
    while changed {
        changed = false;

        for block_idx in (0..blocks.len()).rev() {
            let mut new_out = HashSet::new();
            for &succ in &successors[block_idx] {
                new_out.extend(live_in[succ].iter().copied());
            }

            let mut new_in = block_uses[block_idx].clone();
            new_in.extend(
                new_out
                    .iter()
                    .copied()
                    .filter(|reg| !block_defs[block_idx].contains(reg)),
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
    live_in_regs: &[HashSet<u8>],
) -> HashSet<u8> {
    let mut live_out = HashSet::new();

    for &block_id in loop_body {
        for &succ in &successors[block_id] {
            if !loop_body.contains(&succ) {
                live_out.extend(live_in_regs[succ].iter().copied());
            }
        }
    }

    live_out
}
