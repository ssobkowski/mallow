pub mod common;
pub mod ssa;

use std::collections::HashMap;

use anyhow::{Context, Result, bail, ensure};
use smol_str::ToSmolStr;
use ssa::Ssa;

use crate::common::ByteString;
use crate::disasm::Chunk;
use crate::hil::cflow::graph::GraphView;
use crate::hil::ir::{Capture, CellId, Expr, Number, Stmt, ValuePack};
use crate::hil::lifter::common::{CAPTURE_REF, CAPTURE_UPVAL, CAPTURE_VAL};
use crate::hil::lifter::ssa::{Symbol, SymbolId};
use crate::hil::ty::bytecode::ProtoTypeContext;
use crate::il::{
    ChildProtoId, ConstId, Constant, Count, DecodedInstr, ImportPath, Instr, Proto, ProtoId,
    reg_add, reg_range,
};
use crate::operator::{BinOp, UnOp};

/// A deferred variadic source that has not yet been consumed.
///
/// Either a multiret call result (`Expr::Call` / `Expr::MethodCall`) or a full
/// vararg splice (`Expr::VarArgs`). The `base` register is the first slot of
/// the variadic sequence; consumers pull as many values as they need starting
/// there.
#[derive(Debug)]
pub struct MultiRet {
    /// First result register of the variadic sequence.
    pub base: u8,
    /// The expression that produced the sequence.
    pub expr: Expr,
    /// Debug-local index used if a deferred vararg must be materialized.
    pub local_index: Option<usize>,
}

/// Returns true when an instruction can appear between a pending multiret and
/// its consumer without invalidating the deferred sequence.
///
/// Luau can insert bookkeeping opcodes (e.g. `CLOSEUPVALS`) between a variadic
/// call and the eventual `RETURN`, so we must not flush the pending source there.
const fn instr_preserves_multiret(instr: Instr, pending_src_reg: u8) -> bool {
    match instr {
        Instr::FastCall1 { .. }
        | Instr::FastCall2 { .. }
        | Instr::FastCall2K { .. }
        | Instr::FastCall3 { .. }
        | Instr::FastCall { .. }
        | Instr::CloseUpvals { .. } => true,
        Instr::GetImport { dest, .. }
        | Instr::GetGlobal { dest, .. }
        | Instr::GetUpval { dest, .. }
        | Instr::Move { dest, .. } => dest < pending_src_reg,
        _ => false,
    }
}

fn binop_for_instr(instr: &Instr) -> BinOp {
    match instr {
        Instr::Add { .. } | Instr::AddK { .. } => BinOp::Add,
        Instr::Sub { .. } | Instr::SubK { .. } | Instr::SubRK { .. } => BinOp::Sub,
        Instr::Mul { .. } | Instr::MulK { .. } => BinOp::Mul,
        Instr::Div { .. } | Instr::DivK { .. } | Instr::DivRK { .. } => BinOp::Div,
        Instr::IDiv { .. } | Instr::IDivK { .. } => BinOp::IDiv,
        Instr::Mod { .. } | Instr::ModK { .. } => BinOp::Mod,
        Instr::Pow { .. } | Instr::PowK { .. } => BinOp::Pow,
        Instr::And { .. } | Instr::AndK { .. } => BinOp::And,
        Instr::Or { .. } | Instr::OrK { .. } => BinOp::Or,
        _ => unreachable!("not a binary operator instruction: {:?}", instr),
    }
}

fn unop_for_instr(instr: &Instr) -> UnOp {
    match instr {
        Instr::Minus { .. } => UnOp::Minus,
        Instr::Length { .. } => UnOp::Length,
        Instr::Not { .. } => UnOp::Not,
        _ => unreachable!("not a unary operator instruction: {:?}", instr),
    }
}

/// Builds a field access without losing a non-UTF-8 key.
fn string_key_access(object: Expr, key: ByteString) -> Expr {
    if let Some(field) = key.as_utf8() {
        Expr::GetField {
            obj: Box::new(object),
            field: field.into(),
        }
    } else {
        Expr::GetIndex {
            obj: Box::new(object),
            index: Box::new(Expr::String(key)),
        }
    }
}

/// Tracks which register slots currently hold open captured storage.
#[derive(Debug, Clone, Copy)]
pub struct CaptureState {
    /// Storage generation for each register slot.
    reg_generations: [u16; 256],
    /// Open captured generation for each register slot.
    open_refs: [Option<u16>; 256],
}

impl Default for CaptureState {
    fn default() -> Self {
        Self {
            reg_generations: [0; 256],
            open_refs: [None; 256],
        }
    }
}

impl CaptureState {
    /// Applies capture bookkeeping for one instruction.
    pub fn note_instruction(&mut self, instr: Instr) {
        match instr {
            Instr::Capture {
                capture_type: CAPTURE_REF,
                reg,
            } => self.open_ref(reg),
            Instr::CloseUpvals { reg } => self.close_refs(reg),
            _ => {}
        }
    }

    /// Returns the open storage generation for one register slot.
    pub(crate) fn open_generation(&self, reg: u8) -> Option<u16> {
        self.open_refs[reg as usize]
    }

    /// Returns the current storage generation for one register slot.
    pub(crate) fn generation(&self, reg: u8) -> u16 {
        self.reg_generations[reg as usize]
    }

    /// Opens captured storage for one register slot.
    fn open_ref(&mut self, reg: u8) {
        self.open_refs[reg as usize] = Some(self.reg_generations[reg as usize]);
    }

    /// Closes captured storage from one register slot through the stack top.
    fn close_refs(&mut self, from_reg: u8) {
        for generation in &mut self.reg_generations[from_reg as usize..] {
            *generation = generation
                .checked_add(1)
                .expect("capture generation overflow");
        }

        for captured in &mut self.open_refs[from_reg as usize..] {
            *captured = None;
        }
    }
}

pub struct LiftContext<'a, 'cfg, G: GraphView> {
    pub instrs: &'a [DecodedInstr],
    pub chunk: &'a Chunk,
    pub proto: &'a Proto,
    pub type_context: &'a ProtoTypeContext,
    pub ssa: &'a mut Ssa<'cfg, G>,
    pub block_idx: usize,
    pub capture_state: CaptureState,
    /// Cells for captured register generations in this function.
    pub captured_cells: &'a HashMap<(u8, u16), CellId>,
    /// Cells for declared upvalue slots in this function.
    pub upvalue_cells: &'a [CellId],
}

pub struct Lifter<'a, 'cfg, G: GraphView> {
    ip: usize,

    instrs: &'a [DecodedInstr],
    chunk: &'a Chunk,
    proto: &'a Proto,
    type_context: &'a ProtoTypeContext,

    ssa: &'a mut Ssa<'cfg, G>,
    block_idx: usize,

    stmts: Vec<Stmt>,
    pending_multiret: Option<MultiRet>,

    capture_state: CaptureState,
    captured_cells: &'a HashMap<(u8, u16), CellId>,
    upvalue_cells: &'a [CellId],
}

impl<'a, 'cfg, G: GraphView> Lifter<'a, 'cfg, G> {
    pub fn new(ctx: LiftContext<'a, 'cfg, G>) -> Self {
        Self {
            ip: 0,
            instrs: ctx.instrs,
            chunk: ctx.chunk,
            proto: ctx.proto,
            type_context: ctx.type_context,
            ssa: ctx.ssa,
            block_idx: ctx.block_idx,
            stmts: Vec::new(),
            pending_multiret: None,
            capture_state: ctx.capture_state,
            captured_cells: ctx.captured_cells,
            upvalue_cells: ctx.upvalue_cells,
        }
    }

    fn current_pc(&self) -> u32 {
        let ip = self.ip.saturating_sub(1);
        debug_assert!(
            ip < self.instrs.len(),
            "ip out of bounds: {ip} (instrs len: {})",
            self.instrs.len()
        );

        self.instrs[ip].word_pc
    }

    fn next(&mut self) -> Option<Instr> {
        let instr = self.instrs.get(self.ip).copied();
        if instr.is_some() {
            self.ip += 1;
        }
        instr.map(|decoded| decoded.instr)
    }

    /// Pushes one statement into the lifted block body.
    fn push(&mut self, stmt: Stmt) {
        self.stmts.push(stmt);
    }

    /// Reads the values of the given register range.
    fn read_regs(&mut self, start: u8, count: u8) -> Vec<Expr> {
        reg_range(start, count)
            .map(|reg| self.read_reg(reg))
            .collect()
    }

    /// Allocates assignment targets for a range of registers.
    fn alloc_regs(&mut self, start: u8, count: u8) -> Vec<Expr> {
        reg_range(start, count)
            .map(|reg| {
                assert!(
                    self.open_cell(reg).is_none(),
                    "multi-value writes to captured registers need explicit stores"
                );
                Expr::Symbol(self.alloc_reg_symbol(reg))
            })
            .collect()
    }

    /// Returns a chained concatenated expression of the values of the given register range.
    fn concat_expr_range(&mut self, start: u8, end: u8) -> Expr {
        assert!(
            start <= end,
            "invalid CONCAT register range: {start}..{end}"
        );

        let mut expr = self.read_reg(end);
        for reg in (start..end).rev() {
            expr = Expr::Binary {
                lhs: Box::new(self.read_reg(reg)),
                op: BinOp::Concat,
                rhs: Box::new(expr),
            };
        }
        expr
    }

    /// Emits a plain assignment statement.
    fn assign(&mut self, left: Expr, value: Expr) {
        self.push(Stmt::Assign { left, value });
    }

    /// Emits a register write.
    fn assign_reg(&mut self, reg: u8, value: Expr) {
        if let Some(cell) = self.open_cell(reg) {
            self.push(Stmt::StoreCell { cell, value });
        } else {
            let sym = self.alloc_reg_symbol(reg);
            self.push(Stmt::Assign {
                left: Expr::Symbol(sym),
                value,
            });
        }
    }

    /// Reads one register, loading mutable captured storage when needed.
    fn read_reg(&mut self, reg: u8) -> Expr {
        let Some(cell) = self.open_cell(reg) else {
            return Expr::Symbol(self.ssa.read_reg(self.block_idx, reg));
        };

        let target = self.alloc_value_symbol(reg);
        self.push(Stmt::LoadCell { target, cell });
        Expr::Symbol(target)
    }

    /// Returns the open cell for one register.
    fn open_cell(&self, reg: u8) -> Option<CellId> {
        let generation = self.capture_state.open_generation(reg)?;
        Some(
            *self
                .captured_cells
                .get(&(reg, generation))
                .expect("open captured register must have an allocated cell"),
        )
    }

    /// Allocates a symbol for one register value without changing register SSA state.
    fn alloc_value_symbol(&mut self, reg: u8) -> SymbolId {
        let pc = self.current_pc();
        self.ssa.alloc_symbol(
            Symbol::reg(reg)
                .with_type(self.type_context.local_at(reg, pc))
                .with_local_index(self.proto.local_index_after(reg, pc)),
        )
    }

    fn alloc_reg_symbol(&mut self, reg: u8) -> SymbolId {
        let sym = self.alloc_value_symbol(reg);
        self.ssa.write_reg(self.block_idx, reg, sym);
        sym
    }

    /// Allocates one source value before storing it into an open cell.
    fn store_reg_from_value(&mut self, reg: u8, value: Expr) {
        let cell = self
            .open_cell(reg)
            .expect("captured register store needs an open cell");
        let target = self.alloc_value_symbol(reg);
        self.push(Stmt::Assign {
            left: Expr::Symbol(target),
            value,
        });
        self.push(Stmt::StoreCell {
            cell,
            value: Expr::Symbol(target),
        });
    }

    fn note_close_upvals(&mut self, from_reg: u8) {
        self.capture_state.close_refs(from_reg);
    }

    /// Opens one captured register cell and records its initial value.
    fn open_capture_cell(&mut self, reg: u8) -> CellId {
        if let Some(cell) = self.open_cell(reg) {
            return cell;
        }

        let generation = self.capture_state.generation(reg);
        let cell = *self
            .captured_cells
            .get(&(reg, generation))
            .expect("reference capture must have an allocated cell");
        let symbol = self.ssa.read_reg(self.block_idx, reg);
        let value = Expr::Symbol(symbol);
        self.capture_state.open_ref(reg);
        self.ssa.write_reg(self.block_idx, reg, symbol);
        self.push(Stmt::OpenCell { cell, value });
        cell
    }

    fn instr_consumes_pending_multiret(&self, instr: Instr) -> bool {
        let Some(pending) = &self.pending_multiret else {
            return false;
        };

        match instr {
            Instr::Call {
                func, arg_count, ..
            } if Count::from(arg_count) == Count::Variadic => {
                pending.base >= func.saturating_add(1)
            }

            Instr::SetList { base, count, .. } if Count::from(count) == Count::Variadic => {
                pending.base >= base
            }

            // NAMECALL can consume through the following CALL, so this one needs
            // special handling / lookahead.
            Instr::NameCall { .. } | Instr::NameCallUData { .. } => true,

            _ => false,
        }
    }

    fn flush_pending_before(&mut self, instr: Instr) {
        let Some(pending) = &self.pending_multiret else {
            return;
        };

        if self.instr_consumes_pending_multiret(instr) {
            return;
        }

        if instr_preserves_multiret(instr, pending.base) {
            return;
        }

        self.flush_multiret();
    }

    /// Lifts all instructions into HIL statements in bytecode order.
    pub fn run(mut self) -> Result<(Vec<Stmt>, Option<MultiRet>, CaptureState)> {
        while let Some(instr) = self.next() {
            self.flush_pending_before(instr);

            match &instr {
                Instr::Nop => {}
                Instr::LoadNil { reg } => self.assign_reg(*reg, Expr::Nil),
                Instr::LoadB { reg, value, .. } => self.assign_reg(*reg, Expr::Bool(*value)),
                Instr::LoadN { reg, value } => {
                    self.assign_reg(*reg, Expr::Number(Number::Float(*value as f64)))
                }
                Instr::LoadK { reg, index } => {
                    let value = self.const_expr(ConstId(*index as u32))?;
                    self.assign_reg(*reg, value);
                }
                Instr::LoadKX { reg, index } => {
                    let value = self.const_expr(ConstId(*index))?;
                    self.assign_reg(*reg, value);
                }
                Instr::Move { dest, src } => {
                    let value = self.read_reg(*src);
                    self.assign_reg(*dest, value)
                }
                Instr::GetGlobal { dest, key, .. } => {
                    self.assign_reg(
                        *dest,
                        Expr::Global(
                            self.const_name(ConstId(*key))
                                .with_context(|| format!("invalid string constant {key}"))?,
                        ),
                    );
                }
                Instr::SetGlobal { src, key, .. } => {
                    let value = self.read_reg(*src);
                    self.assign(
                        Expr::Global(
                            self.const_name(ConstId(*key))
                                .with_context(|| format!("invalid string constant {key}"))?,
                        ),
                        value,
                    );
                }
                Instr::GetUpval { dest, upval } => {
                    let cell = self.upvalue_cells[*upval as usize];
                    let target = self.alloc_value_symbol(*dest);
                    self.push(Stmt::LoadCell { target, cell });
                    self.assign_reg(*dest, Expr::Symbol(target));
                }
                Instr::SetUpval { src, upval } => {
                    let cell = self.upvalue_cells[*upval as usize];
                    let value = self.read_reg(*src);
                    self.push(Stmt::StoreCell { cell, value });
                }
                Instr::GetImport { dest, path, .. } => {
                    self.assign_reg(
                        *dest,
                        Expr::import(ImportPath(*path), self.chunk, self.proto)?,
                    );
                }

                Instr::NameCall {
                    dest,
                    object,
                    method,
                    ..
                } => self.lift_namecall(*dest, *object, *method)?,
                Instr::NameCallUData {
                    dest,
                    object,
                    method,
                    ..
                } => self.lift_namecall(*dest, *object, u32::from(*method))?,
                Instr::Call {
                    func,
                    arg_count,
                    ret_count,
                } => self.lift_call(*func, *arg_count, *ret_count),
                Instr::Return { .. } => {
                    unreachable!("RETURN should have been handled by the CFG generator")
                }

                Instr::GetTableKS {
                    dest, table, key, ..
                } => {
                    let table = self.read_reg(*table);
                    let key = self.const_string(ConstId(*key))?;
                    self.assign_reg(*dest, string_key_access(table, key));
                }
                Instr::GetUDataKS {
                    dest,
                    userdata,
                    key,
                    ..
                } => {
                    let userdata = self.read_reg(*userdata);
                    let key = self.const_string(ConstId(u32::from(*key)))?;
                    self.assign_reg(*dest, string_key_access(userdata, key));
                }
                Instr::GetTable { dest, table, key } => {
                    let table = self.read_reg(*table);
                    let key = self.read_reg(*key);
                    self.assign_reg(
                        *dest,
                        Expr::GetIndex {
                            obj: Box::new(table),
                            index: Box::new(key),
                        },
                    );
                }
                Instr::GetTableN { dest, table, index } => {
                    let table = self.read_reg(*table);
                    self.assign_reg(
                        *dest,
                        Expr::GetIndex {
                            obj: Box::new(table),
                            index: Box::new(Expr::Number(Number::Float(*index as f64))),
                        },
                    );
                }
                Instr::SetTableKS {
                    src, table, key, ..
                } => {
                    let table = self.read_reg(*table);
                    let value = self.read_reg(*src);
                    let key = self.const_string(ConstId(*key))?;
                    self.assign(string_key_access(table, key), value);
                }
                Instr::SetUDataKS {
                    src, userdata, key, ..
                } => {
                    let userdata = self.read_reg(*userdata);
                    let value = self.read_reg(*src);
                    let key = self.const_string(ConstId(u32::from(*key)))?;
                    self.assign(string_key_access(userdata, key), value);
                }
                Instr::SetTableN { src, table, index } => {
                    let table = self.read_reg(*table);
                    let value = self.read_reg(*src);
                    self.assign(
                        Expr::GetIndex {
                            obj: Box::new(table),
                            index: Box::new(Expr::Number(Number::Float(*index as f64))),
                        },
                        value,
                    );
                }
                Instr::SetTable { src, table, key } => {
                    let table = self.read_reg(*table);
                    let key = self.read_reg(*key);
                    let value = self.read_reg(*src);
                    self.assign(
                        Expr::GetIndex {
                            obj: Box::new(table),
                            index: Box::new(key),
                        },
                        value,
                    );
                }

                // reg op reg — covers all arithmetic and logical RR forms.
                Instr::Add { dest, a, b }
                | Instr::Sub { dest, a, b }
                | Instr::Mul { dest, a, b }
                | Instr::Div { dest, a, b }
                | Instr::IDiv { dest, a, b }
                | Instr::Mod { dest, a, b }
                | Instr::Pow { dest, a, b }
                | Instr::And { dest, a, b }
                | Instr::Or { dest, a, b } => {
                    let lhs = self.read_reg(*a);
                    let rhs = self.read_reg(*b);
                    self.assign_reg(
                        *dest,
                        Expr::Binary {
                            lhs: Box::new(lhs),
                            op: binop_for_instr(&instr),
                            rhs: Box::new(rhs),
                        },
                    );
                }

                // reg op const(number) — the RHS is always a numeric constant.
                Instr::AddK { dest, reg, k }
                | Instr::SubK { dest, reg, k }
                | Instr::MulK { dest, reg, k }
                | Instr::DivK { dest, reg, k }
                | Instr::IDivK { dest, reg, k }
                | Instr::ModK { dest, reg, k }
                | Instr::PowK { dest, reg, k } => {
                    let num = match self.proto.get_constant(ConstId(*k as u32)) {
                        Some(Constant::Number(x)) => *x,
                        other => bail!(
                            "*K arithmetic instructions can only reference number constants, got {other:?} instead",
                        ),
                    };
                    let lhs = self.read_reg(*reg);
                    self.assign_reg(
                        *dest,
                        Expr::Binary {
                            lhs: Box::new(lhs),
                            op: binop_for_instr(&instr),
                            rhs: Box::new(Expr::Number(Number::Float(num))),
                        },
                    );
                }

                // const(number) op reg — operands are flipped; only Sub and Div have this form.
                Instr::SubRK { dest, k, reg } | Instr::DivRK { dest, k, reg } => {
                    let num = match self.proto.get_constant(ConstId(*k as u32)) {
                        Some(Constant::Number(x)) => *x,
                        other => bail!(
                            "*RK arithmetic instructions can only reference number constants, got {other:?} instead",
                        ),
                    };
                    let rhs = self.read_reg(*reg);
                    self.assign_reg(
                        *dest,
                        Expr::Binary {
                            lhs: Box::new(Expr::Number(Number::Float(num))),
                            op: binop_for_instr(&instr),
                            rhs: Box::new(rhs),
                        },
                    );
                }

                // reg op const(any) — And/Or can short-circuit against any constant type.
                Instr::AndK { dest, reg, k } | Instr::OrK { dest, reg, k } => {
                    let lhs = self.read_reg(*reg);
                    self.assign_reg(
                        *dest,
                        Expr::Binary {
                            lhs: Box::new(lhs),
                            op: binop_for_instr(&instr),
                            rhs: Box::new(self.const_expr(ConstId(*k as u32))?),
                        },
                    );
                }

                Instr::Concat { dest, a, b } => {
                    let expr = self.concat_expr_range(*a, *b);
                    self.assign_reg(*dest, expr);
                }

                Instr::Not { dest, reg }
                | Instr::Minus { dest, reg }
                | Instr::Length { dest, reg } => {
                    let value = self.read_reg(*reg);
                    self.assign_reg(
                        *dest,
                        Expr::Unary {
                            op: unop_for_instr(&instr),
                            expr: Box::new(value),
                        },
                    )
                }

                Instr::NewTable { dest, .. } => {
                    self.assign_reg(*dest, Expr::Table { items: Vec::new() });
                }
                Instr::DupTable { dest, k } => {
                    let value = self.const_expr(ConstId(*k as u32))?;
                    self.assign_reg(*dest, value);
                }

                Instr::SetList {
                    table,
                    base,
                    count,
                    index,
                } => self.lift_setlist(*table, *base, *count, *index),

                Instr::NewClosure { dest, proto: index } => {
                    let Some(proto_id) = self.proto.get_child_proto(ChildProtoId(*index)) else {
                        bail!(
                            "did not find child proto for index {} in proto {:?}",
                            *index,
                            self.proto.id,
                        );
                    };
                    self.lift_closure(*dest, proto_id)?;
                }
                Instr::DupClosure { dest, k } => {
                    let Some(Constant::Closure(proto_id)) =
                        self.proto.get_constant(ConstId(*k as u32))
                    else {
                        bail!(
                            "constant {} of proto {:?} is missing or not a closure",
                            *k,
                            self.proto.id
                        );
                    };
                    self.lift_closure(*dest, *proto_id)?;
                }

                Instr::CloseUpvals { reg } => self.note_close_upvals(*reg),

                // Bookkeeping-only opcodes that the decompiler does not need to model.
                Instr::FastCall1 { .. }
                | Instr::FastCall2 { .. }
                | Instr::FastCall2K { .. }
                | Instr::FastCall3 { .. }
                | Instr::FastCall { .. }
                | Instr::PrepVarArgs { .. } => {}

                Instr::Capture { .. } => unreachable!(
                    "CAPTURE instructions should have been consumed by NEWCLOSURE/DUPCLOSURE handling"
                ),

                Instr::GetVarArgs { dest, count } => match Count::from(*count) {
                    Count::Variadic => {
                        debug_assert!(self.pending_multiret.is_none());
                        self.pending_multiret = Some(MultiRet {
                            base: *dest,
                            expr: Expr::VarArgs,
                            local_index: self.proto.local_index_after(*dest, self.current_pc()),
                        });
                    }
                    Count::Number(n) => {
                        let left = self.alloc_regs(*dest, n);
                        self.push(Stmt::AssignMany {
                            left,
                            values: ValuePack::Open {
                                head: Vec::new(),
                                tail: Box::new(Expr::VarArgs),
                            },
                        });
                    }
                },

                // Lifter does not need to handle these instructions
                Instr::Break
                | Instr::Jump { .. }
                | Instr::JumpBack { .. }
                | Instr::JumpIf { .. }
                | Instr::JumpIfNot { .. }
                | Instr::JumpX { .. }
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
                | Instr::ForgPrep { .. }
                | Instr::ForgPrepInext { .. }
                | Instr::ForgPrepNext { .. }
                | Instr::FornLoop { .. }
                | Instr::ForgLoop { .. }
                | Instr::Coverage
                | Instr::NativeCall => {}
            }
        }

        Ok((self.stmts, self.pending_multiret, self.capture_state))
    }

    fn lift_call(&mut self, func: u8, arg_count: u8, ret_count: u8) {
        let first_arg = reg_add(func, 1);
        let args = match Count::from(arg_count) {
            Count::Number(argc) => ValuePack::Fixed(self.read_regs(first_arg, argc)),
            Count::Variadic => self.take_variadic_from(first_arg).unwrap_or_else(|| {
                debug_assert!(false, "variadic CALL without pending multiret");
                ValuePack::empty()
            }),
        };
        let fun = self.read_reg(func);
        let call = Expr::Call {
            fun: Box::new(fun),
            args,
        };
        self.emit_call_result(func, ret_count, call);
    }

    fn lift_namecall(&mut self, dest: u8, object: u8, method: u32) -> Result<()> {
        let namecall_pc = self.current_pc();
        let (func, arg_count, ret_count) = match self.next() {
            Some(Instr::Call {
                func,
                arg_count,
                ret_count,
            }) => (func, arg_count, ret_count),
            Some(other) => {
                bail!(
                    "malformed bytecode: NAMECALL at {namecall_pc} not followed by CALL (got {other:?})"
                )
            }
            None => {
                bail!(
                    "malformed bytecode: NAMECALL at the end of the stream with no following CALL"
                )
            }
        };

        ensure!(
            func == dest,
            "malformed bytecode: CALL func reg {func} does not match NAMECALL dest reg {dest}"
        );

        let method = self.const_name(ConstId(method))?;

        let first_arg = reg_add(func, 2); // receiver is at func+1, user args start at func+2
        let variadic_args = match Count::from(arg_count) {
            Count::Variadic => self.take_variadic_from(first_arg),
            Count::Number(_) => None,
        };

        if variadic_args.is_none() {
            let should_flush = self.pending_multiret.as_ref().is_some_and(|m| {
                !instr_preserves_multiret(
                    Instr::Call {
                        func,
                        arg_count,
                        ret_count,
                    },
                    m.base,
                )
            });
            if should_flush {
                self.flush_multiret();
            }
        }

        let args = match Count::from(arg_count) {
            Count::Number(argc) if argc > 1 => {
                ValuePack::Fixed(self.read_regs(first_arg, argc - 1))
            }
            Count::Variadic => variadic_args.unwrap_or_else(ValuePack::empty),
            _ => ValuePack::empty(),
        };

        let object = self.read_reg(object);
        let method_call = Expr::MethodCall {
            object: Box::new(object),
            method,
            args,
        };
        self.emit_call_result(func, ret_count, method_call);
        Ok(())
    }

    fn lift_setlist(&mut self, table: u8, base: u8, count: u8, index: u32) {
        let values = match Count::from(count) {
            Count::Number(n) => ValuePack::Fixed(self.read_regs(base, n)),
            Count::Variadic => self.take_variadic_from(base).unwrap_or_else(|| {
                debug_assert!(false, "variadic call without pending multiret");
                ValuePack::empty()
            }),
        };

        let table = self.read_reg(table);
        let Expr::Symbol(table) = table else {
            unreachable!("SETLIST table loads must produce a symbol")
        };
        self.push(Stmt::SetList {
            table,
            index,
            values,
        });
    }

    /// Emit the result of a CALL or NAMECALL depending on the return count.
    fn emit_call_result(&mut self, dest: u8, ret_count: u8, expr: Expr) {
        assert!(
            matches!(expr, Expr::Call { .. } | Expr::MethodCall { .. }),
            "expected a call expression"
        );
        match Count::from(ret_count) {
            Count::Number(0) => self.push(Stmt::Call(expr)),
            Count::Number(1) if self.open_cell(dest).is_some() => {
                self.store_reg_from_value(dest, expr)
            }
            Count::Number(1) => self.assign_reg(dest, expr),
            Count::Number(n) => {
                assert!(
                    reg_range(dest, n).all(|reg| self.open_cell(reg).is_none()),
                    "multi-return writes to captured registers are unsupported"
                );
                let left = self.alloc_regs(dest, n);
                self.push(Stmt::AssignMany {
                    left,
                    values: ValuePack::Open {
                        head: Vec::new(),
                        tail: Box::new(expr),
                    },
                });
            }
            Count::Variadic => {
                debug_assert!(self.pending_multiret.is_none());
                self.pending_multiret = Some(MultiRet {
                    base: dest,
                    expr,
                    local_index: None,
                });
            }
        }
    }

    fn lift_closure(&mut self, dest: u8, proto_id: ProtoId) -> Result<()> {
        let proto = self
            .chunk
            .get_proto(proto_id)
            .with_context(|| format!("did not find proto {proto_id:?}"))?;

        let (captures, recursive_cell) = self.consume_captures(proto.num_upvals, dest)?;
        let value = Expr::Closure {
            proto: proto.id,
            captures,
        };
        if let Some(cell) = recursive_cell {
            self.push(Stmt::OpenCell { cell, value });
        } else {
            self.assign_reg(dest, value);

            if self.open_cell(dest).is_none() {
                let sym = self.ssa.read_reg(self.block_idx, dest);
                let local_index = self.proto.local_index_after(dest, self.current_pc());
                self.ssa.set_local_index(sym, local_index);
            }
        }

        Ok(())
    }

    /// Builds an open value pack from the pending multiret starting no later than `first`.
    fn take_variadic_from(&mut self, first: u8) -> Option<ValuePack> {
        if self
            .pending_multiret
            .as_ref()
            .is_none_or(|m| m.base < first)
        {
            return None;
        }
        let MultiRet { base, expr, .. } = self.pending_multiret.take().unwrap();
        Some(ValuePack::Open {
            head: self.read_regs(first, base - first),
            tail: Box::new(expr),
        })
    }

    /// Consume `count` CAPTURE instructions immediately following the current
    /// cursor position.
    fn consume_captures(
        &mut self,
        count: u8,
        closure_dest: u8,
    ) -> Result<(Vec<Capture>, Option<CellId>)> {
        if count == 0 {
            return Ok((Vec::new(), None));
        }

        let mut captures = Vec::with_capacity(count as usize);
        let mut recursive_cell = None;
        for i in 0..count {
            match self.next() {
                Some(Instr::Capture { capture_type, reg }) => {
                    let capture = match capture_type {
                        CAPTURE_VAL => {
                            let value = self.read_reg(reg);
                            let Expr::Symbol(value) = value else {
                                unreachable!("register reads must produce symbols")
                            };
                            Capture::Copy(value)
                        }
                        CAPTURE_REF if reg == closure_dest && self.open_cell(reg).is_none() => {
                            let generation = self.capture_state.generation(reg);
                            let cell = self.captured_cells[&(reg, generation)];
                            self.capture_state.open_ref(reg);
                            recursive_cell = Some(cell);
                            Capture::Share(cell)
                        }
                        CAPTURE_REF => Capture::Share(self.open_capture_cell(reg)),
                        CAPTURE_UPVAL => Capture::Share(self.upvalue_cells[reg as usize]),
                        _ => unreachable!("unknown capture type: {capture_type}"),
                    };
                    captures.push(capture);
                }
                Some(other) => {
                    bail!(
                        "malformed bytecode: expected CAPTURE #{i} after closure got instr: {other:?}"
                    );
                }
                None => {
                    bail!(
                        "malformed bytecode: unexpected end of instructions while consuming CAPTURE #{i}"
                    );
                }
            }
        }
        Ok((captures, recursive_cell))
    }

    /// Flush the pending multiret to `self.stmts` as a standalone call-stmt or
    /// a plain `local = ...` assignment.
    fn flush_multiret(&mut self) {
        let Some(multiret) = self.pending_multiret.take() else {
            return;
        };

        flush_multiret(multiret, self.block_idx, self.ssa, &mut self.stmts);
    }

    /// A helper for resolving string constants from the chunk.
    #[inline]
    fn const_string(&self, id: ConstId) -> Result<ByteString> {
        let ct = self
            .proto
            .get_constant(id)
            .with_context(|| format!("missing constant at {id:?}"))?;
        let Constant::String(sid) = ct else {
            bail!("expected string constant at {id:?}, got {ct:?}");
        };
        self.chunk
            .get_string(*sid)
            .with_context(|| format!("invalid string id {:?}", sid))
    }

    /// Resolves one string constant that must be valid UTF-8 source text.
    fn const_name(&self, id: ConstId) -> Result<smol_str::SmolStr> {
        let value = self.const_string(id)?;
        let value = value
            .as_utf8()
            .with_context(|| format!("string constant {id:?} is not valid UTF-8"))?;
        Ok(value.to_smolstr())
    }

    /// A helper for resolving expression constants from the proto.
    #[inline]
    fn const_expr(&self, id: ConstId) -> Result<Expr> {
        let ct = self
            .proto
            .get_constant(id)
            .with_context(|| format!("missing constant at {id:?}"))?;
        Expr::from_constant(ct, self.chunk, self.proto)
    }
}

/// Flushes a deferred variadic source into the given statement stream.
///
/// A pending call-like multiret becomes a standalone call statement. A pending
/// vararg splice must materialize into its base register because later code can
/// reference that register by symbol.
pub fn flush_multiret<G: GraphView>(
    multiret: MultiRet,
    block_idx: usize,
    ssa: &mut Ssa<'_, G>,
    stmts: &mut Vec<Stmt>,
) {
    let MultiRet {
        base,
        expr,
        local_index,
    } = multiret;

    match expr {
        call @ (Expr::Call { .. } | Expr::MethodCall { .. }) => {
            stmts.push(Stmt::Call(call));
        }
        Expr::VarArgs => {
            let sym = ssa.alloc_symbol(Symbol::reg(base).with_local_index(local_index));
            ssa.write_reg(block_idx, base, sym);

            stmts.push(Stmt::Assign {
                left: Expr::Symbol(sym),
                value: Expr::VarArgs,
            });
        }
        _ => unreachable!("unexpected deferred variadic source"),
    }
}

/// Lifts one instruction slice into raw HIL statements.
pub fn lift<'a, 'cfg, G: GraphView>(
    ctx: LiftContext<'a, 'cfg, G>,
) -> Result<(Vec<Stmt>, Option<MultiRet>, CaptureState)> {
    let lifter = Lifter::new(ctx);
    lifter.run()
}

#[cfg(test)]
mod tests {
    use super::string_key_access;
    use crate::common::ByteString;
    use crate::hil::ir::Expr;

    /// Invalid UTF-8 field keys remain byte-exact index expressions.
    #[test]
    fn string_key_access_preserves_invalid_utf8() {
        let key = ByteString::from(vec![0x80, 0xFF]);
        let access = string_key_access(Expr::Global("object".into()), key.clone());

        assert!(matches!(
            access,
            Expr::GetIndex { index, .. } if *index == Expr::String(key)
        ));
    }
}
