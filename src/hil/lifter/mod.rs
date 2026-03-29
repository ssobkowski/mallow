// mod passes;
pub mod ssa;

use ssa::Ssa;

use crate::{
    ast::{BinOp, UnOp},
    common::{escape_string, is_lua_ident},
    disasm::Proto,
    hil::{
        common::{const_expr, decoded_count},
        ir::{HilExpr, HilStmt, Spanned, ToSpanned},
        lifter::ssa::{Symbol, SymbolId},
    },
    il::{Constant, Count, Instr},
};

/// A deferred variadic source that has not yet been consumed.
///
/// Either a multiret call result (`HilExpr::Call` / `HilExpr::MethodCall`) or a full
/// vararg splice (`HilExpr::VarArgs`). The `base` register is the first slot of
/// the variadic sequence; consumers pull as many values as they need starting
/// there.
#[derive(Debug)]
pub struct MultiRet {
    /// First result register of the variadic sequence.
    base: u8,
    /// The expression that produced the sequence.
    expr: Spanned<HilExpr>,
}

/// Returns true when an instruction can appear between a pending multiret and
/// its consumer without invalidating the deferred sequence.
///
/// Luau can insert bookkeeping opcodes (e.g. `CLOSEUPVALS`) between a variadic
/// call and the eventual `RETURN`, so we must not flush the pending source there.
fn instr_preserves_multiret(instr: &Instr, pending_src_reg: u8) -> bool {
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
        | Instr::Move { dest, .. } => *dest < pending_src_reg,
        _ => false,
    }
}

fn binop_for_instr(instr: &Instr) -> BinOp {
    match instr {
        Instr::Add { .. } | Instr::AddK { .. } => BinOp::Add,
        Instr::Sub { .. } | Instr::SubK { .. } | Instr::SubRK { .. } => BinOp::Sub,
        Instr::Mul { .. } | Instr::MulK { .. } => BinOp::Mul,
        Instr::Div { .. } | Instr::DivK { .. } | Instr::DivRK { .. } => BinOp::Div,
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

pub struct LiftContext<'a, 'cfg> {
    pub instrs: &'a [(Instr, usize)],
    pub consts: &'a [Constant],
    pub parent_proto: &'a Proto,
    pub protos: &'a [Proto],
    pub ssa: &'a mut Ssa<'cfg>,
    pub block_idx: usize,
}

pub struct Lifter<'a, 'cfg> {
    ip: usize,

    instrs: &'a [(Instr, usize)],
    consts: &'a [Constant],
    parent_proto: &'a Proto,
    protos: &'a [Proto],

    ssa: &'a mut Ssa<'cfg>,
    block_idx: usize,

    upvalues: Vec<SymbolId>,

    stmts: Vec<Spanned<HilStmt>>,
    pending_multiret: Option<MultiRet>,
}

impl<'a, 'cfg> Lifter<'a, 'cfg> {
    pub fn new(ctx: LiftContext<'a, 'cfg>) -> Self {
        Self {
            ip: 0,
            instrs: ctx.instrs,
            consts: ctx.consts,
            parent_proto: ctx.parent_proto,
            protos: ctx.protos,
            ssa: ctx.ssa,
            block_idx: ctx.block_idx,
            upvalues: Vec::new(),
            stmts: Vec::new(),
            pending_multiret: None,
        }
    }

    fn current_pc(&self) -> usize {
        let ip = self.ip.saturating_sub(1);
        debug_assert!(
            ip < self.instrs.len(),
            "ip out of bounds: {ip} (instrs len: ${})",
            self.instrs.len()
        );

        self.instrs[ip].1
    }

    fn next(&mut self) -> Option<Instr> {
        let instr = self.instrs.get(self.ip).copied();
        if instr.is_some() {
            self.ip += 1;
        }
        instr.map(|i| i.0)
    }

    /// Pushes one statement tagged with the current instruction PC.
    fn push(&mut self, stmt: HilStmt) {
        self.stmts.push(Spanned::new(stmt, self.current_pc()));
    }

    fn read_regs(&mut self, start: u8, count: u8) -> Vec<HilExpr> {
        (0..count)
            .map(|i| HilExpr::Symbol(self.get_reg_symbol(start + i)))
            .collect()
    }

    fn alloc_regs(&mut self, start: u8, count: u8) -> Vec<SymbolId> {
        (0..count)
            .map(|i| {
                let reg = start + i;
                let sym = self.ssa.alloc_symbol(Symbol::new(reg));
                self.ssa.write_reg(self.block_idx, reg, sym);
                sym
            })
            .collect()
    }

    fn concat_expr_range(&mut self, start: u8, end: u8) -> HilExpr {
        debug_assert!(
            start <= end,
            "invalid CONCAT register range: {start}..{end}"
        );

        let mut expr = HilExpr::Symbol(self.get_reg_symbol(end));
        for reg in (start..end).rev() {
            expr = HilExpr::Binary {
                lhs: Box::new(HilExpr::Symbol(self.get_reg_symbol(reg))),
                op: BinOp::Concat,
                rhs: Box::new(expr),
            };
        }
        expr
    }

    /// Emits a plain assignment statement at the current PC span.
    fn assign(&mut self, left: HilExpr, value: HilExpr) {
        let ip = self.ip.saturating_sub(1);
        debug_assert!(ip < self.instrs.len());
        let pc = self.instrs[ip].1;

        self.stmts
            .push(HilStmt::Assign { left, value }.to_spanned(pc));
    }

    /// Emits a plain assignment statement at the current PC span, and allocates
    /// a new register symbol in the arena.
    fn assign_reg(&mut self, reg: u8, value: HilExpr) {
        let ip = self.ip.saturating_sub(1);
        debug_assert!(ip < self.instrs.len());
        let pc = self.instrs[ip].1;

        let sym = self.ssa.alloc_symbol(Symbol::new(reg));
        self.ssa.write_reg(self.block_idx, reg, sym);

        self.stmts.push(
            HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                value,
            }
            .to_spanned(pc),
        );
    }

    fn get_reg_symbol(&mut self, reg: u8) -> SymbolId {
        self.ssa.read_reg(self.block_idx, reg)
    }

    /// Lifts all instructions into pc-spanned HIL statements in bytecode order.
    pub fn run(mut self) -> Vec<Spanned<HilStmt>> {
        while let Some(instr) = self.next() {
            match &instr {
                Instr::Nop => {}
                Instr::LoadNil { reg } => self.assign_reg(*reg, HilExpr::Nil),
                Instr::LoadB { reg, value, .. } => self.assign_reg(*reg, HilExpr::Bool(*value)),
                Instr::LoadN { reg, value } => {
                    self.assign_reg(*reg, HilExpr::Number(*value as f64))
                }
                Instr::LoadK { reg, index } => {
                    self.assign_reg(*reg, self.const_expr(*index as usize));
                }
                Instr::Move { dest, src } => {
                    let sym = self.get_reg_symbol(*src);
                    self.assign_reg(*dest, HilExpr::Symbol(sym))
                }
                Instr::GetGlobal { dest, key, .. } => {
                    self.assign_reg(
                        *dest,
                        HilExpr::Global(self.const_string(*key as usize).into()),
                    );
                }
                Instr::SetGlobal { src, key, .. } => {
                    let sym = self.get_reg_symbol(*src);
                    self.assign(
                        HilExpr::Global(self.const_string(*key as usize).into()),
                        HilExpr::Symbol(sym),
                    );
                }
                Instr::GetUpval { dest, upval } => {
                    let upval_sym = self.upvalues[*upval as usize];
                    self.assign_reg(*dest, HilExpr::Symbol(upval_sym));
                }
                Instr::SetUpval { src, upval } => {
                    let upval_sym = self.upvalues[*upval as usize];
                    let src_sym = self.get_reg_symbol(*src);

                    // TODO
                    // self.arena[upval_sym].mutability = Mutability::Mutable;

                    self.assign(HilExpr::Symbol(upval_sym), HilExpr::Symbol(src_sym))
                }
                Instr::GetImport { dest, index, path } => {
                    let name = self
                        .decode_import_path(*path)
                        .unwrap_or_else(|| format!("import_k{}", index));
                    self.assign_reg(*dest, HilExpr::Import(name.into()));
                }

                Instr::NameCall {
                    dest,
                    object,
                    method,
                    ..
                } => self.lift_namecall(*dest, *object, *method),
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
                    let key_str = self.const_string(*key as usize);
                    let sym = self.get_reg_symbol(*table);
                    self.assign_reg(
                        *dest,
                        HilExpr::GetField {
                            obj: Box::new(HilExpr::Symbol(sym)),
                            field: key_str.into(),
                        },
                    );
                }
                Instr::GetTable { dest, table, key } => {
                    let table_sym = self.get_reg_symbol(*table);
                    let key_sym = self.get_reg_symbol(*key);
                    self.assign_reg(
                        *dest,
                        HilExpr::GetIndex {
                            obj: Box::new(HilExpr::Symbol(table_sym)),
                            index: Box::new(HilExpr::Symbol(key_sym)),
                        },
                    );
                }
                Instr::GetTableN { dest, table, index } => {
                    let sym = self.get_reg_symbol(*table);
                    self.assign_reg(
                        *dest,
                        HilExpr::GetIndex {
                            obj: Box::new(HilExpr::Symbol(sym)),
                            index: Box::new(HilExpr::Number(*index as f64)),
                        },
                    );
                }
                Instr::SetTableKS {
                    src, table, key, ..
                } => {
                    let table_sym = self.get_reg_symbol(*table);
                    let value_sym = self.get_reg_symbol(*src);
                    self.push(HilStmt::SetField {
                        table: table_sym,
                        key: self.const_string(*key as usize).into(),
                        value: HilExpr::Symbol(value_sym),
                    });
                }
                Instr::SetTableN { src, table, index } => {
                    let table_sym = self.get_reg_symbol(*table);
                    let value_sym = self.get_reg_symbol(*src);
                    self.assign(
                        HilExpr::GetIndex {
                            obj: Box::new(HilExpr::Symbol(table_sym)),
                            index: Box::new(HilExpr::Number(*index as f64)),
                        },
                        HilExpr::Symbol(value_sym),
                    );
                }
                Instr::SetTable { src, table, key } => {
                    let table_sym = self.get_reg_symbol(*table);
                    let key_sym = self.get_reg_symbol(*key);
                    let value_sym = self.get_reg_symbol(*src);
                    self.assign(
                        HilExpr::GetIndex {
                            obj: Box::new(HilExpr::Symbol(table_sym)),
                            index: Box::new(HilExpr::Symbol(key_sym)),
                        },
                        HilExpr::Symbol(value_sym),
                    );
                }

                // reg op reg — covers all arithmetic and logical RR forms.
                Instr::Add { dest, a, b }
                | Instr::Sub { dest, a, b }
                | Instr::Mul { dest, a, b }
                | Instr::Div { dest, a, b }
                | Instr::Mod { dest, a, b }
                | Instr::Pow { dest, a, b }
                | Instr::And { dest, a, b }
                | Instr::Or { dest, a, b } => {
                    let lhs_sym = self.get_reg_symbol(*a);
                    let rhs_sym = self.get_reg_symbol(*b);
                    self.assign_reg(
                        *dest,
                        HilExpr::Binary {
                            lhs: Box::new(HilExpr::Symbol(lhs_sym)),
                            op: binop_for_instr(&instr),
                            rhs: Box::new(HilExpr::Symbol(rhs_sym)),
                        },
                    );
                }

                // reg op const(number) — the RHS is always a numeric constant.
                Instr::AddK { dest, reg, k }
                | Instr::SubK { dest, reg, k }
                | Instr::MulK { dest, reg, k }
                | Instr::DivK { dest, reg, k }
                | Instr::ModK { dest, reg, k }
                | Instr::PowK { dest, reg, k } => {
                    let num = match self.consts[*k as usize] {
                        Constant::Number(x) => x,
                        _ => unreachable!(
                            "*K arithmetic instructions can only reference number constants"
                        ),
                    };
                    let lhs_sym = self.get_reg_symbol(*reg);
                    self.assign_reg(
                        *dest,
                        HilExpr::Binary {
                            lhs: Box::new(HilExpr::Symbol(lhs_sym)),
                            op: binop_for_instr(&instr),
                            rhs: Box::new(HilExpr::Number(num)),
                        },
                    );
                }

                // const(number) op reg — operands are flipped; only Sub and Div have this form.
                Instr::SubRK { dest, k, reg } | Instr::DivRK { dest, k, reg } => {
                    let num = match self.consts[*k as usize] {
                        Constant::Number(x) => x,
                        _ => unreachable!(
                            "*RK arithmetic instructions can only reference number constants"
                        ),
                    };
                    let rhs_sym = self.get_reg_symbol(*reg);
                    self.assign_reg(
                        *dest,
                        HilExpr::Binary {
                            lhs: Box::new(HilExpr::Number(num)),
                            op: binop_for_instr(&instr),
                            rhs: Box::new(HilExpr::Symbol(rhs_sym)),
                        },
                    );
                }

                // reg op const(any) — And/Or can short-circuit against any constant type.
                Instr::AndK { dest, reg, k } | Instr::OrK { dest, reg, k } => {
                    let lhs_sym = self.get_reg_symbol(*reg);
                    self.assign_reg(
                        *dest,
                        HilExpr::Binary {
                            lhs: Box::new(HilExpr::Symbol(lhs_sym)),
                            op: binop_for_instr(&instr),
                            rhs: Box::new(const_expr(self.consts, usize::from(*k))),
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
                    let sym = self.get_reg_symbol(*reg);
                    self.assign_reg(
                        *dest,
                        HilExpr::Unary {
                            op: unop_for_instr(&instr),
                            expr: Box::new(HilExpr::Symbol(sym)),
                        },
                    )
                }

                // Both variants produce an empty table that SETLIST fills in.
                Instr::NewTable { dest, .. } | Instr::DupTable { dest, .. } => {
                    self.assign_reg(*dest, HilExpr::Table { items: Vec::new() });
                }

                Instr::SetList {
                    table,
                    base,
                    count,
                    index,
                } => self.lift_setlist(*table, *base, *count, *index),

                Instr::NewClosure { dest, proto: index } => {
                    let resolved = self.parent_proto.protos[*index as usize];
                    let n_captures = self.proto_upval_count(resolved);
                    let captures = self.consume_captures(n_captures);
                    self.assign_reg(
                        *dest,
                        HilExpr::Closure {
                            proto: resolved,
                            captures,
                        },
                    );
                }

                Instr::DupClosure { dest, k } => {
                    let resolved = match self.consts.get(*k as usize) {
                        Some(Constant::Closure(proto_idx)) => *proto_idx as usize,
                        _ => panic!("DUPCLOSURE constant at index {} is not a closure", k),
                    };
                    let n_captures = self.proto_upval_count(resolved);
                    let captures = self.consume_captures(n_captures);
                    self.assign_reg(
                        *dest,
                        HilExpr::Closure {
                            proto: resolved,
                            captures,
                        },
                    );
                }

                // Bookkeeping-only opcodes that the decompiler does not need to model.
                Instr::FastCall1 { .. }
                | Instr::FastCall2 { .. }
                | Instr::FastCall2K { .. }
                | Instr::FastCall3 { .. }
                | Instr::FastCall { .. }
                | Instr::PrepVarArgs { .. }
                | Instr::CloseUpvals { .. } => {}

                Instr::Capture { .. } => unreachable!(
                    "CAPTURE instructions should have been consumed by NEWCLOSURE/DUPCLOSURE handling"
                ),

                Instr::GetVarArgs { dest, count } => match *count {
                    0 => {
                        self.pending_multiret = Some(MultiRet {
                            base: *dest,
                            expr: HilExpr::VarArgs.to_spanned(self.current_pc()),
                        });
                    }
                    n => {
                        let left = self.alloc_regs(*dest, n);
                        self.push(HilStmt::AssignMany {
                            left,
                            value: HilExpr::VarArgs,
                        });
                    }
                },

                other => eprintln!("Unsupported lifter instruction: {:#?}", other),
            }
        }

        // Any deferred variadic source that survives to the end still has runtime
        // effects (e.g. a variadic call), so materialize it before returning.
        self.flush_multiret();
        self.stmts
    }

    fn lift_call(&mut self, func: u8, arg_count: u8, ret_count: u8) {
        let first_arg = func + 1;
        let args = match decoded_count(arg_count) {
            Count::Number(argc) => {
                if argc > 0 {
                    self.read_regs(first_arg, argc)
                } else {
                    Vec::new()
                }
            }
            Count::Variadic => self.take_variadic_from(first_arg).unwrap_or_default(),
        };
        let call = HilExpr::Call {
            fun: Box::new(HilExpr::Symbol(self.get_reg_symbol(func))),
            args,
        };
        self.emit_call_result(func, ret_count, call);
    }

    fn lift_namecall(&mut self, dest: u8, object: u8, method: u32) {
        let (func, arg_count, ret_count) = match self.next() {
            Some(Instr::Call {
                func,
                arg_count,
                ret_count,
            }) => (func, arg_count, ret_count),
            Some(other) => panic!("NAMECALL not followed by CALL, got instr: {other:#?}"),
            None => {
                panic!("NAMECALL at end of stream with no following CALL")
            }
        };

        debug_assert_eq!(
            func, dest,
            "CALL func reg {func} does not match NAMECALL dest reg {dest}"
        );

        let method = self.const_string(method as usize);

        let first_arg = func + 2; // receiver is at func+1, user args start at func+2
        let variadic_args = match decoded_count(arg_count) {
            Count::Variadic => self.take_variadic_from(first_arg),
            Count::Number(_) => None,
        };

        if variadic_args.is_none() {
            let should_flush = self.pending_multiret.as_ref().is_some_and(|m| {
                !instr_preserves_multiret(
                    &Instr::Call {
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

        let args = match decoded_count(arg_count) {
            Count::Number(argc) if argc > 1 => self.read_regs(first_arg, argc - 1),
            Count::Variadic => variadic_args.unwrap_or_default(),
            _ => Vec::new(),
        };

        let method_call = HilExpr::MethodCall {
            object: Box::new(HilExpr::Symbol(self.get_reg_symbol(object))),
            method: method.into(),
            args,
        };
        self.emit_call_result(func, ret_count, method_call);
    }

    fn lift_setlist(&mut self, table: u8, base: u8, count: u8, index: u32) {
        let (values, has_variadic_tail) = match decoded_count(count) {
            Count::Number(n) => (self.read_regs(base, n), false),
            Count::Variadic => (
                self.take_variadic_from(base)
                    .unwrap_or_else(|| vec![HilExpr::Symbol(self.get_reg_symbol(base))]),
                true,
            ),
        };

        let table_sym = self.get_reg_symbol(table);
        self.push(HilStmt::SetList {
            table: table_sym,
            index,
            values,
            has_variadic_tail,
        });
    }

    /// Emit the result of a CALL or NAMECALL depending on the return count.
    fn emit_call_result(&mut self, dest: u8, ret_count: u8, expr: HilExpr) {
        match decoded_count(ret_count) {
            Count::Number(0) => self.push(HilStmt::Call(expr)),
            Count::Number(1) => self.assign_reg(dest, expr),
            Count::Number(n) => {
                let left = self.alloc_regs(dest, n);
                self.push(HilStmt::AssignMany { left, value: expr });
            }
            Count::Variadic => {
                self.pending_multiret = Some(MultiRet {
                    base: dest,
                    expr: expr.to_spanned(self.current_pc()),
                });
            }
        }
    }

    /// Build a variadic argument list from the pending multiret starting no
    /// later than `first`. The result is a fixed-prefix of `HilExpr::Reg`
    /// values followed by the multiret expression.
    fn take_variadic_from(&mut self, first: u8) -> Option<Vec<HilExpr>> {
        if self
            .pending_multiret
            .as_ref()
            .is_none_or(|m| m.base < first)
        {
            return None;
        }
        let MultiRet { base, expr } = self.pending_multiret.take().unwrap();
        let mut args = self.read_regs(first, base - first);
        args.push(expr.inner);
        Some(args)
    }

    /// Consume `count` CAPTURE instructions immediately following the current
    /// cursor position.
    ///
    /// # Panics
    /// Panics if any expected instruction is not a `CAPTURE`.
    fn consume_captures(&mut self, count: u8) -> Vec<SymbolId> {
        if count == 0 {
            return Vec::new();
        }

        let mut captures = Vec::with_capacity(count as usize);
        for i in 0..count {
            match self.next() {
                Some(Instr::Capture { capture_type, reg }) => {
                    let symbol = match capture_type {
                        0 | 1 => self.get_reg_symbol(reg),
                        2 => self.upvalues[reg as usize],
                        _ => unreachable!("unknown capture type: {capture_type}"),
                    };
                    captures.push(symbol);
                }
                Some(other) => panic!("expected CAPTURE #{i} after closure got instr: {other:#?}"),
                None => panic!("unexpected end of instructions while consuming CAPTURE #{i}"),
            }
        }
        captures
    }

    /// Flush the pending multiret to `self.stmts` as a standalone call-stmt or
    /// a plain `local = ...` assignment.
    fn flush_multiret(&mut self) {
        let Some(MultiRet { base, expr }) = self.pending_multiret.take() else {
            return;
        };
        match expr.inner {
            HilExpr::Call { .. } | HilExpr::MethodCall { .. } => self
                .stmts
                .push(HilStmt::Call(expr.inner).to_spanned(expr.pc)),
            HilExpr::VarArgs => {
                let sym = self.ssa.alloc_symbol(Symbol::new(base));
                self.ssa.write_reg(self.block_idx, base, sym);

                self.stmts.push(
                    HilStmt::Assign {
                        left: HilExpr::Symbol(sym),
                        value: HilExpr::VarArgs,
                    }
                    .to_spanned(expr.pc),
                );
            }
            _ => unreachable!("unexpected deferred variadic source"),
        }
    }

    /// See: [const_expr](crate::hil::common::const_expr)
    fn const_expr(&self, index: usize) -> HilExpr {
        const_expr(self.consts, index)
    }

    /// Retrieves a string constant from the constant table.
    ///
    /// # Panics
    /// Panics if the constant at the given index is not a string.
    fn const_string(&self, index: usize) -> String {
        match self.consts.get(index) {
            Some(Constant::String(s)) => s.clone(),
            _ => panic!("expected string constant at index {}", index),
        }
    }

    /// Returns the number of upvalues of a child proto.
    ///
    /// # Panics
    /// Panics if the given proto id is invalid.
    fn proto_upval_count(&self, proto_id: usize) -> u8 {
        match self.protos.get(proto_id) {
            Some(p) => p.num_upvals,
            None => panic!("invalid proto id: {}", proto_id),
        }
    }

    fn decode_import_path(&self, path: u32) -> Option<String> {
        let count = (path >> 30) as usize;
        if !(1..=3).contains(&count) {
            return None;
        }

        let ids = [(path >> 20) & 0x3ff, (path >> 10) & 0x3ff, path & 0x3ff];

        let first = self.const_string(ids[0] as usize);
        let mut out = if is_lua_ident(&first) {
            first
        } else {
            format!("_G[\"{}\"]", escape_string(&first))
        };

        for id in ids.iter().skip(1).take(count - 1) {
            let key = self.const_string(*id as usize);
            if is_lua_ident(&key) {
                out.push('.');
                out.push_str(&key);
            } else {
                out.push_str(&format!("[\"{}\"]", escape_string(&key)));
            }
        }

        Some(out)
    }
}

/// Lifts one instruction slice into raw HIL statements.
#[must_use]
pub fn lift<'a, 'cfg>(ctx: LiftContext<'a, 'cfg>) -> Vec<Spanned<HilStmt>> {
    let lifter = Lifter::new(ctx);
    let stmts = lifter.run();

    // let stmts = run_passes(stmts);

    stmts
}
