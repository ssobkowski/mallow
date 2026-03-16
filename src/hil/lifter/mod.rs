mod passes;

use crate::{
    ast::{BinOp, UnOp},
    common::{escape_string, is_lua_ident},
    disasm::Proto,
    hil::{
        common::{const_expr, decoded_count, local_range, return_values},
        ir::{HilCapture, HilExpr, HilStmt, Spanned, ToSpanned},
        lifter::passes::run_passes,
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

/// Reconstructs Luau's register-range `CONCAT` as a right-associated expression tree.
fn concat_expr_range(start: u8, end: u8) -> HilExpr {
    debug_assert!(
        start <= end,
        "invalid CONCAT register range: {start}..{end}"
    );

    let mut expr = HilExpr::Reg(end);
    for reg in (start..end).rev() {
        expr = HilExpr::Binary {
            lhs: Box::new(HilExpr::Reg(reg)),
            op: BinOp::Concat,
            rhs: Box::new(expr),
        };
    }
    expr
}

/// Decodes Luau capture metadata into the captured HIL capture operand.
fn decode_capture(capture_type: u8, reg: u8) -> HilCapture {
    match capture_type {
        // Luau splits local captures into by-value (0) and by-ref (1), but
        // both decompile to capturing the same local name.
        0 | 1 => HilCapture::Local(reg),
        // Capture an already-existing parent upvalue.
        2 => HilCapture::Upval(reg),
        _ => unreachable!("unknown capture type: {capture_type}"),
    }
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

struct Lifter<'a> {
    ip: usize,

    instrs: &'a [Instr],
    instr_word_pcs: &'a [usize],
    consts: &'a [Constant],
    parent_proto: &'a Proto,
    protos: &'a [Proto],

    stmts: Vec<Spanned<HilStmt>>,
    pending_multiret: Option<MultiRet>,
}

impl<'a> Lifter<'a> {
    fn new(
        instrs: &'a [Instr],
        instr_word_pcs: &'a [usize],
        consts: &'a [Constant],
        parent_proto: &'a Proto,
        protos: &'a [Proto],
    ) -> Self {
        Self {
            ip: 0,
            instrs,
            instr_word_pcs,
            consts,
            parent_proto,
            protos,
            stmts: Vec::new(),
            pending_multiret: None,
        }
    }

    fn next(&mut self) -> Option<Instr> {
        let instr = self.instrs.get(self.ip).copied();
        if instr.is_some() {
            self.ip += 1;
        }
        instr
    }

    /// Returns the source bytecode word PC for one decoded instruction index.
    fn instr_word_pc(&self, instr_idx: usize) -> usize {
        debug_assert_eq!(self.instr_word_pcs.len(), self.instrs.len());
        self.instr_word_pcs[instr_idx]
    }

    /// Pushes one statement tagged with the current instruction PC.
    fn push(&mut self, stmt: HilStmt) {
        self.stmts.push(Spanned::new(
            stmt,
            self.instr_word_pc(self.ip.saturating_sub(1)),
        ));
    }

    /// Pushes one statement with an explicit source PC span.
    fn push_with_pc(&mut self, stmt: HilStmt, pc: usize) {
        self.stmts.push(Spanned::new(stmt, pc));
    }

    /// Emits a plain assignment statement at the current PC span.
    fn assign(&mut self, left: HilExpr, value: HilExpr) {
        self.push(HilStmt::Assign { left, value });
    }

    /// Lifts all instructions into pc-spanned HIL statements in bytecode order.
    fn run(mut self) -> Vec<Spanned<HilStmt>> {
        while let Some(instr) = self.next() {
            match &instr {
                Instr::Nop => {}
                Instr::LoadNil { reg } => self.assign(HilExpr::Reg(*reg), HilExpr::Nil),
                Instr::LoadB { reg, value, .. } => {
                    self.assign(HilExpr::Reg(*reg), HilExpr::Bool(*value))
                }
                Instr::LoadN { reg, value } => {
                    self.assign(HilExpr::Reg(*reg), HilExpr::Number(*value as f64))
                }
                Instr::LoadK { reg, index } => {
                    self.assign(HilExpr::Reg(*reg), self.const_expr(*index as usize));
                }
                Instr::Move { dest, src } => self.assign(HilExpr::Reg(*dest), HilExpr::Reg(*src)),
                Instr::GetGlobal { dest, key, .. } => {
                    self.assign(
                        HilExpr::Reg(*dest),
                        HilExpr::Global(self.const_string(*key as usize).into()),
                    );
                }
                Instr::SetGlobal { src, key, .. } => {
                    self.assign(
                        HilExpr::Global(self.const_string(*key as usize).into()),
                        HilExpr::Reg(*src),
                    );
                }
                Instr::GetUpval { dest, upval } => {
                    self.assign(HilExpr::Reg(*dest), HilExpr::Upval(*upval))
                }
                Instr::SetUpval { src, upval } => {
                    self.assign(HilExpr::Upval(*upval), HilExpr::Reg(*src))
                }
                Instr::GetImport { dest, index, path } => {
                    let name = self
                        .decode_import_path(*path)
                        .unwrap_or_else(|| format!("import_k{}", index));
                    self.assign(HilExpr::Reg(*dest), HilExpr::Import(name.into()));
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
                Instr::Return { base, count } => self.lift_return(*base, *count),

                Instr::GetTableKS {
                    dest, table, key, ..
                } => {
                    let key_str = self.const_string(*key as usize);
                    self.assign(
                        HilExpr::Reg(*dest),
                        HilExpr::GetField {
                            obj: Box::new(HilExpr::Reg(*table)),
                            field: key_str.into(),
                        },
                    );
                }
                Instr::GetTable { dest, table, key } => {
                    self.assign(
                        HilExpr::Reg(*dest),
                        HilExpr::GetIndex {
                            obj: Box::new(HilExpr::Reg(*table)),
                            index: Box::new(HilExpr::Reg(*key)),
                        },
                    );
                }
                Instr::GetTableN { dest, table, index } => {
                    self.assign(
                        HilExpr::Reg(*dest),
                        HilExpr::GetIndex {
                            obj: Box::new(HilExpr::Reg(*table)),
                            index: Box::new(HilExpr::Number(*index as f64)),
                        },
                    );
                }
                Instr::SetTableKS {
                    src, table, key, ..
                } => {
                    self.push(HilStmt::SetField {
                        table: *table,
                        key: self.const_string(*key as usize).into(),
                        value: HilExpr::Reg(*src),
                    });
                }
                Instr::SetTableN { src, table, index } => {
                    self.assign(
                        HilExpr::GetIndex {
                            obj: Box::new(HilExpr::Reg(*table)),
                            index: Box::new(HilExpr::Number(*index as f64)),
                        },
                        HilExpr::Reg(*src),
                    );
                }
                Instr::SetTable { src, table, key } => {
                    self.assign(
                        HilExpr::GetIndex {
                            obj: Box::new(HilExpr::Reg(*table)),
                            index: Box::new(HilExpr::Reg(*key)),
                        },
                        HilExpr::Reg(*src),
                    );
                }

                // reg op reg — covers all arithmetic and logical RR forms.
                instr @ (Instr::Add { dest, a, b }
                | Instr::Sub { dest, a, b }
                | Instr::Mul { dest, a, b }
                | Instr::Div { dest, a, b }
                | Instr::Mod { dest, a, b }
                | Instr::Pow { dest, a, b }
                | Instr::And { dest, a, b }
                | Instr::Or { dest, a, b }) => {
                    self.assign(
                        HilExpr::Reg(*dest),
                        HilExpr::Binary {
                            lhs: Box::new(HilExpr::Reg(*a)),
                            op: binop_for_instr(instr),
                            rhs: Box::new(HilExpr::Reg(*b)),
                        },
                    );
                }

                // reg op const(number) — the RHS is always a numeric constant.
                instr @ (Instr::AddK { dest, reg, k }
                | Instr::SubK { dest, reg, k }
                | Instr::MulK { dest, reg, k }
                | Instr::DivK { dest, reg, k }
                | Instr::ModK { dest, reg, k }
                | Instr::PowK { dest, reg, k }) => {
                    let num = match self.consts[*k as usize] {
                        Constant::Number(x) => x,
                        _ => unreachable!(
                            "*K arithmetic instructions can only reference number constants"
                        ),
                    };
                    self.assign(
                        HilExpr::Reg(*dest),
                        HilExpr::Binary {
                            lhs: Box::new(HilExpr::Reg(*reg)),
                            op: binop_for_instr(instr),
                            rhs: Box::new(HilExpr::Number(num)),
                        },
                    );
                }

                // const(number) op reg — operands are flipped; only Sub and Div have this form.
                instr @ (Instr::SubRK { dest, k, reg } | Instr::DivRK { dest, k, reg }) => {
                    let num = match self.consts[*k as usize] {
                        Constant::Number(x) => x,
                        _ => unreachable!(
                            "*RK arithmetic instructions can only reference number constants"
                        ),
                    };
                    self.assign(
                        HilExpr::Reg(*dest),
                        HilExpr::Binary {
                            lhs: Box::new(HilExpr::Number(num)),
                            op: binop_for_instr(instr),
                            rhs: Box::new(HilExpr::Reg(*reg)),
                        },
                    );
                }

                // reg op const(any) — And/Or can short-circuit against any constant type.
                instr @ (Instr::AndK { dest, reg, k } | Instr::OrK { dest, reg, k }) => {
                    self.assign(
                        HilExpr::Reg(*dest),
                        HilExpr::Binary {
                            lhs: Box::new(HilExpr::Reg(*reg)),
                            op: binop_for_instr(instr),
                            rhs: Box::new(const_expr(self.consts, usize::from(*k))),
                        },
                    );
                }

                Instr::Concat { dest, a, b } => {
                    self.assign(HilExpr::Reg(*dest), concat_expr_range(*a, *b))
                }

                Instr::Not { dest, reg } => self.assign(
                    HilExpr::Reg(*dest),
                    HilExpr::Unary {
                        op: UnOp::Not,
                        expr: Box::new(HilExpr::Reg(*reg)),
                    },
                ),
                Instr::Minus { dest, reg } => self.assign(
                    HilExpr::Reg(*dest),
                    HilExpr::Unary {
                        op: UnOp::Minus,
                        expr: Box::new(HilExpr::Reg(*reg)),
                    },
                ),
                Instr::Length { dest, reg } => self.assign(
                    HilExpr::Reg(*dest),
                    HilExpr::Unary {
                        op: UnOp::Length,
                        expr: Box::new(HilExpr::Reg(*reg)),
                    },
                ),

                // Both variants produce an empty table that SETLIST fills in.
                Instr::NewTable { dest, .. } | Instr::DupTable { dest, .. } => {
                    self.push(HilStmt::Assign {
                        left: HilExpr::Reg(*dest),
                        value: HilExpr::Table { items: Vec::new() },
                    });
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
                    self.assign(
                        HilExpr::Reg(*dest),
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
                    self.assign(
                        HilExpr::Reg(*dest),
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
                            expr: HilExpr::VarArgs
                                .to_spanned(self.instr_word_pc(self.ip.saturating_sub(1))),
                        });
                    }
                    n => self.push(HilStmt::AssignMany {
                        left: local_range(*dest, n),
                        value: HilExpr::VarArgs,
                    }),
                },

                other => eprintln!("Unsupported instruction: {:#?}", other),
            }
        }

        // Any deferred variadic source that survives to the end still has runtime
        // effects (e.g. a variadic call), so materialize it before returning.
        self.flush_multiret();
        self.stmts
    }

    fn lift_return(&mut self, base: u8, count: u8) {
        let rets = match decoded_count(count) {
            Count::Variadic => self
                .take_variadic_from(base)
                .unwrap_or_else(|| return_values(base, count)),
            Count::Number(_) => return_values(base, count),
        };
        self.push(HilStmt::Return(rets));
    }

    fn lift_call(&mut self, func: u8, arg_count: u8, ret_count: u8) {
        let first_arg = func + 1;
        let args = match decoded_count(arg_count) {
            Count::Number(argc) => {
                if argc > 0 {
                    local_range(first_arg, argc)
                } else {
                    Vec::new()
                }
            }
            Count::Variadic => self.take_variadic_from(first_arg).unwrap_or_default(),
        };
        let call = HilExpr::Call {
            fun: Box::new(HilExpr::Reg(func)),
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
            Count::Number(argc) if argc > 1 => local_range(first_arg, argc - 1),
            Count::Variadic => variadic_args.unwrap_or_default(),
            _ => Vec::new(),
        };

        let method_call = HilExpr::MethodCall {
            object: Box::new(HilExpr::Reg(object)),
            method: method.into(),
            args,
        };
        self.emit_call_result(func, ret_count, method_call);
    }

    fn lift_setlist(&mut self, table: u8, base: u8, count: u8, index: u32) {
        let (values, has_variadic_tail) = match decoded_count(count) {
            Count::Number(n) => (local_range(base, n), false),
            Count::Variadic => (
                self.take_variadic_from(base)
                    .unwrap_or_else(|| vec![HilExpr::Reg(base)]),
                true,
            ),
        };

        self.push(HilStmt::SetList {
            table,
            index,
            values,
            has_variadic_tail,
        });
    }

    /// Emit the result of a CALL or NAMECALL depending on the return count.
    fn emit_call_result(&mut self, dest: u8, ret_count: u8, expr: HilExpr) {
        match decoded_count(ret_count) {
            Count::Number(0) => self.push(HilStmt::Call(expr)),
            Count::Number(1) => self.assign(HilExpr::Reg(dest), expr),
            Count::Number(n) => self.push(HilStmt::AssignMany {
                left: local_range(dest, n),
                value: expr,
            }),
            Count::Variadic => {
                self.pending_multiret = Some(MultiRet {
                    base: dest,
                    expr: expr.to_spanned(self.instr_word_pc(self.ip.saturating_sub(1))),
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
        let mut args = local_range(first, base - first);
        args.push(expr.inner);
        Some(args)
    }

    /// Consume `count` CAPTURE instructions immediately following the current
    /// cursor position.
    ///
    /// # Panics
    /// Panics if any expected instruction is not a `CAPTURE`.
    fn consume_captures(&mut self, count: u8) -> Vec<HilCapture> {
        if count == 0 {
            return Vec::new();
        }

        let mut captures = Vec::with_capacity(count as usize);
        for i in 0..count {
            match self.next() {
                Some(Instr::Capture { capture_type, reg }) => {
                    captures.push(decode_capture(capture_type, reg));
                }
                Some(other) => panic!("expected CAPTURE #{i} after closure got instr: {other:#?}"),
                None => panic!(
                    "unexpected end of instructions while consuming CAPTURE #{i} after closure"
                ),
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
            HilExpr::Call { .. } | HilExpr::MethodCall { .. } => {
                self.push_with_pc(HilStmt::Call(expr.inner), expr.pc)
            }
            HilExpr::VarArgs => self.push_with_pc(
                HilStmt::Assign {
                    left: HilExpr::Reg(base),
                    value: HilExpr::VarArgs,
                },
                expr.pc,
            ),
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
pub fn lift(
    instrs: &[Instr],
    instr_word_pcs: &[usize],
    consts: &[Constant],
    parent_proto: &Proto,
    protos: &[Proto],
) -> Vec<Spanned<HilStmt>> {
    let lifter = Lifter::new(instrs, instr_word_pcs, consts, parent_proto, protos);
    let stmts = lifter.run();

    let stmts = run_passes(stmts);

    stmts
}
