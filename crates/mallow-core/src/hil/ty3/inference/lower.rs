//! Lowering from lifted SSA HIL to immutable inference relations.

use crate::hil::{
    cflow::cfg::BlockExit,
    ir::{Expr, Stmt, TableItem, ValuePack},
    lifted::LiftedFunction,
    lifter::ssa::SymbolId,
    ty2::{
        builtins::{BuiltinEnvironment, BuiltinPath},
        canonical::PrimitiveIds,
    },
};

use super::{
    keys::{ObjectKey, PackKey, ValueKey},
    program::{InferenceProgram, PackRelation, ValueRelation},
};

/// Lowers all lifted functions into one whole-program relation graph.
pub fn lower_functions(
    functions: &[LiftedFunction],
    builtins: &BuiltinEnvironment,
    primitives: PrimitiveIds,
) -> InferenceProgram {
    let mut program = InferenceProgram::default();
    for function in functions {
        FunctionLowerer::new(function, functions, builtins, primitives, &mut program).lower();
    }
    program
}

/// Proto-local allocator and relation writer.
struct FunctionLowerer<'a> {
    /// Function being lowered.
    function: &'a LiftedFunction,
    /// All lifted functions indexed by proto ID.
    functions: &'a [LiftedFunction],
    /// Builtins used for path recognition.
    builtins: &'a BuiltinEnvironment,
    /// Canonical primitive IDs for literal facts.
    primitives: PrimitiveIds,
    /// Whole-program relation graph.
    program: &'a mut InferenceProgram,
    /// Next proto-local temporary value.
    next_value: u32,
    /// Next proto-local temporary pack.
    next_pack: u32,
    /// Next proto-local table object.
    next_object: u32,
    /// Whether the function has an explicit return edge.
    has_return: bool,
}

impl<'a> FunctionLowerer<'a> {
    /// Creates a lowerer for one lifted function.
    fn new(
        function: &'a LiftedFunction,
        functions: &'a [LiftedFunction],
        builtins: &'a BuiltinEnvironment,
        primitives: PrimitiveIds,
        program: &'a mut InferenceProgram,
    ) -> Self {
        Self {
            function,
            functions,
            builtins,
            primitives,
            program,
            next_value: 0,
            next_pack: 0,
            next_object: 0,
            has_return: false,
        }
    }

    /// Lowers one function body into the shared program.
    fn lower(mut self) {
        self.program.touch_pack(self.return_pack());
        if self.function.is_vararg {
            self.program.touch_pack(self.vararg_pack());
        }
        for parameter in &self.function.symbols.params {
            self.program.touch_value(self.symbol_value(*parameter));
        }
        for upvalue in &self.function.symbols.upvalues {
            self.program.touch_value(self.symbol_value(*upvalue));
        }

        for block in self.function.cfg.blocks() {
            for statement in block.stmts() {
                self.lower_statement(statement);
            }
            self.lower_exit(block.exit());
        }

        if !self.has_return {
            self.program.push_pack(
                self.return_pack(),
                PackRelation::Sequence {
                    head: Vec::new(),
                    tail: None,
                },
            );
        }
    }

    /// Returns the key for a symbol in the current proto.
    fn symbol_value(&self, symbol: SymbolId) -> ValueKey {
        ValueKey::Symbol(self.function.proto, symbol)
    }

    /// Allocates a temporary scalar value.
    fn temp_value(&mut self) -> ValueKey {
        let value = ValueKey::Temp(self.function.proto, self.next_value);
        self.next_value = self
            .next_value
            .checked_add(1)
            .expect("one proto exhausted ty3 temporary values");
        self.program.touch_value(value);
        value
    }

    /// Allocates a temporary pack.
    fn temp_pack(&mut self) -> PackKey {
        let pack = PackKey::Temp(self.function.proto, self.next_pack);
        self.next_pack = self
            .next_pack
            .checked_add(1)
            .expect("one proto exhausted ty3 temporary packs");
        self.program.touch_pack(pack);
        pack
    }

    /// Allocates a table object key.
    fn object_key(&mut self) -> ObjectKey {
        let key = ObjectKey {
            proto: self.function.proto,
            index: self.next_object,
        };
        self.next_object = self
            .next_object
            .checked_add(1)
            .expect("one proto exhausted ty3 object keys");
        key
    }

    /// Returns the current function's vararg pack.
    fn vararg_pack(&self) -> PackKey {
        PackKey::VarArgs(self.function.proto)
    }

    /// Returns the current function's return pack.
    fn return_pack(&self) -> PackKey {
        PackKey::Returns(self.function.proto)
    }

    /// Lowers one statement.
    fn lower_statement(&mut self, statement: &Stmt) {
        match statement {
            Stmt::Assign { left, value } => {
                let value = self.lower_expr(value);
                self.assign_lvalue(left, value);
            }
            Stmt::AssignMany { left, values } => {
                let values = self.lower_value_pack(values);
                for (index, lvalue) in left.iter().enumerate() {
                    let value = self.project_pack(values, index);
                    self.assign_lvalue(lvalue, value);
                }
            }
            Stmt::SetList { table, values, .. } => {
                let object = self.symbol_value(*table);
                let values = self.lower_value_pack(values);
                let aggregate = self.temp_value();
                self.program
                    .push_value(aggregate, ValueRelation::FromPackValues { pack: values });
                let index = self.temp_value();
                self.program
                    .push_value(index, ValueRelation::Observe(self.primitives.number));
                self.program.push_value(
                    object,
                    ValueRelation::WriteIndex {
                        index,
                        value: aggregate,
                    },
                );
            }
            Stmt::Call(call) => {
                self.lower_call(call);
            }
            Stmt::Phi(phi) => {
                let target = self.symbol_value(phi.target);
                for (_, operand) in &phi.operands {
                    let operand = self.symbol_value(*operand);
                    self.program
                        .push_value(target, ValueRelation::FlowFrom(operand));
                }
            }
        }
    }

    /// Assigns a lowered value to one lvalue expression.
    fn assign_lvalue(&mut self, lvalue: &Expr, value: ValueKey) {
        match lvalue {
            Expr::Symbol(symbol) => {
                let target = self.symbol_value(*symbol);
                if matches!(value, ValueKey::Symbol(_, _)) {
                    self.program
                        .push_value(target, ValueRelation::SameAs(value));
                } else {
                    self.program
                        .push_value(target, ValueRelation::FlowFrom(value));
                }
            }
            Expr::GetField { obj, field } => {
                let object = self.lower_expr(obj);
                self.program.push_value(
                    object,
                    ValueRelation::WriteField {
                        field: field.clone(),
                        value,
                        definite: false,
                    },
                );
            }
            Expr::GetIndex { obj, index } => {
                let object = self.lower_expr(obj);
                let index = self.lower_expr(index);
                self.program
                    .push_value(object, ValueRelation::WriteIndex { index, value });
            }
            _ => {
                let target = self.lower_expr(lvalue);
                self.program
                    .push_value(target, ValueRelation::FlowFrom(value));
            }
        }
    }

    /// Lowers one expression list.
    fn lower_value_pack(&mut self, values: &ValuePack) -> PackKey {
        let head = values
            .head()
            .iter()
            .map(|value| self.lower_expr(value))
            .collect();
        let tail = values.tail().map(|value| self.lower_expr_pack(value));
        let pack = self.temp_pack();
        self.program
            .push_pack(pack, PackRelation::Sequence { head, tail });
        pack
    }

    /// Lowers one expression in multivalue context.
    fn lower_expr_pack(&mut self, expression: &Expr) -> PackKey {
        match expression {
            Expr::Call { .. } | Expr::MethodCall { .. } => self.lower_call(expression),
            Expr::VarArgs => self.vararg_pack(),
            _ => {
                let value = self.lower_expr(expression);
                let pack = self.temp_pack();
                self.program.push_pack(
                    pack,
                    PackRelation::Sequence {
                        head: vec![value],
                        tail: None,
                    },
                );
                pack
            }
        }
    }

    /// Creates a scalar projection from one pack.
    fn project_pack(&mut self, pack: PackKey, index: usize) -> ValueKey {
        let value = self.temp_value();
        self.program
            .push_value(value, ValueRelation::FromPack { pack, index });
        value
    }

    /// Lowers one call expression and returns its result pack.
    fn lower_call(&mut self, expression: &Expr) -> PackKey {
        let returns = self.temp_pack();
        match expression {
            Expr::Call { fun, args } => {
                let callee = self.lower_expr(fun);
                let args = self.lower_value_pack(args);
                self.program
                    .push_value(callee, ValueRelation::Call { args, returns });
            }
            Expr::MethodCall {
                object,
                method,
                args,
            } => {
                let object = self.lower_expr(object);
                let callee = self.temp_value();
                self.program.push_value(
                    object,
                    ValueRelation::ReadField {
                        field: method.clone(),
                        output: callee,
                    },
                );
                let user_args = self.lower_value_pack(args);
                let args = self.temp_pack();
                self.program.push_pack(
                    args,
                    PackRelation::Sequence {
                        head: vec![object],
                        tail: Some(user_args),
                    },
                );
                self.program
                    .push_value(callee, ValueRelation::Call { args, returns });
            }
            _ => unreachable!("call lowering requires a call expression"),
        }
        returns
    }

    /// Lowers one scalar expression.
    fn lower_expr(&mut self, expression: &Expr) -> ValueKey {
        if let Some(path) = BuiltinPath::from_expr(expression)
            && self.builtins.get_path(&path).is_some()
        {
            let value = self.temp_value();
            self.program.push_value(value, ValueRelation::Builtin(path));
            return value;
        }

        match expression {
            Expr::Nil => self.observed_temp(self.primitives.nil),
            Expr::Number(_) => self.observed_temp(self.primitives.number),
            Expr::String(_) => self.observed_temp(self.primitives.string),
            Expr::Bool(_) => self.observed_temp(self.primitives.boolean),
            Expr::Symbol(symbol) => self.symbol_value(*symbol),
            Expr::Closure { proto, captures } => {
                let value = self.temp_value();
                self.program
                    .push_value(value, ValueRelation::Closure(*proto));
                let function = self
                    .functions
                    .get(proto.0 as usize)
                    .filter(|function| function.proto == *proto)
                    .expect("closure proto must index its lifted function");
                assert_eq!(
                    captures.len(),
                    function.symbols.upvalues.len(),
                    "closure captures must match child upvalues"
                );
                for (&capture, &upvalue) in captures.iter().zip(&function.symbols.upvalues) {
                    let parent = self.symbol_value(capture);
                    let child = ValueKey::Symbol(*proto, upvalue);
                    self.program
                        .push_value(parent, ValueRelation::SameAs(child));
                }
                value
            }
            Expr::Global(_) => self.temp_value(),
            Expr::VarArgs => {
                let pack = self.vararg_pack();
                self.project_pack(pack, 0)
            }
            Expr::Table { items } => {
                let value = self.temp_value();
                let object = self.object_key();
                self.program
                    .push_value(value, ValueRelation::NewObject(object));
                for item in items {
                    match item {
                        TableItem::List(values) => {
                            let values = self.lower_value_pack(values);
                            let aggregate = self.temp_value();
                            self.program.push_value(
                                aggregate,
                                ValueRelation::FromPackValues { pack: values },
                            );
                            let index = self.observed_temp(self.primitives.number);
                            self.program.push_value(
                                value,
                                ValueRelation::WriteIndex {
                                    index,
                                    value: aggregate,
                                },
                            );
                        }
                        TableItem::Index(Expr::String(field), item_value) => {
                            let item_value = self.lower_expr(item_value);
                            self.program.push_value(
                                value,
                                ValueRelation::WriteField {
                                    field: field.as_str().into(),
                                    value: item_value,
                                    definite: true,
                                },
                            );
                        }
                        TableItem::Index(index, item_value) => {
                            let index = self.lower_expr(index);
                            let item_value = self.lower_expr(item_value);
                            self.program.push_value(
                                value,
                                ValueRelation::WriteIndex {
                                    index,
                                    value: item_value,
                                },
                            );
                        }
                    }
                }
                value
            }
            Expr::Call { .. } | Expr::MethodCall { .. } => {
                let returns = self.lower_call(expression);
                self.project_pack(returns, 0)
            }
            Expr::Binary { lhs, op, rhs } => {
                let lhs = self.lower_expr(lhs);
                let rhs = self.lower_expr(rhs);
                let output = self.temp_value();
                self.program.push_value(
                    lhs,
                    ValueRelation::Binary {
                        op: *op,
                        rhs,
                        output,
                    },
                );
                output
            }
            Expr::Unary { op, expr } => {
                let operand = self.lower_expr(expr);
                let output = self.temp_value();
                self.program
                    .push_value(operand, ValueRelation::Unary { op: *op, output });
                output
            }
            Expr::GetField { obj, field } => {
                let object = self.lower_expr(obj);
                let output = self.temp_value();
                self.program.push_value(
                    object,
                    ValueRelation::ReadField {
                        field: field.clone(),
                        output,
                    },
                );
                output
            }
            Expr::GetIndex { obj, index } => {
                let object = self.lower_expr(obj);
                let index = self.lower_expr(index);
                let output = self.temp_value();
                self.program
                    .push_value(object, ValueRelation::ReadIndex { index, output });
                output
            }
            Expr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => {
                self.lower_expr(condition);
                let then_value = self.lower_expr(then_expr);
                let else_value = self.lower_expr(else_expr);
                let output = self.temp_value();
                self.program
                    .push_value(output, ValueRelation::FlowFrom(then_value));
                self.program
                    .push_value(output, ValueRelation::FlowFrom(else_value));
                output
            }
        }
    }

    /// Creates a temporary with one concrete observation.
    fn observed_temp(&mut self, ty: crate::hil::ty2::canonical::TypeId) -> ValueKey {
        let value = self.temp_value();
        self.program.push_value(value, ValueRelation::Observe(ty));
        value
    }

    /// Lowers one CFG exit.
    fn lower_exit(&mut self, exit: &BlockExit) {
        match exit {
            BlockExit::CondJump { cond, .. } => {
                self.lower_expr(cond);
            }
            BlockExit::Return(values) => {
                self.has_return = true;
                let values = self.lower_value_pack(values);
                self.program.push_pack(
                    self.return_pack(),
                    PackRelation::Sequence {
                        head: Vec::new(),
                        tail: Some(values),
                    },
                );
            }
            BlockExit::FornPrep {
                var,
                start,
                end,
                step,
                ..
            } => {
                let variable = self.symbol_value(*var);
                self.program
                    .push_value(variable, ValueRelation::Observe(self.primitives.number));
                self.lower_expr(start);
                self.lower_expr(end);
                self.lower_expr(step);
            }
            BlockExit::ForgPrep { exprs, .. } => {
                for expression in exprs {
                    self.lower_expr(expression);
                }
            }
            BlockExit::ForgLoop { vars, .. } => {
                for variable in vars {
                    self.program.touch_value(self.symbol_value(*variable));
                }
            }
            BlockExit::FornLoop { .. } | BlockExit::Jump(_) | BlockExit::Fallthrough(_) => {}
        }
    }
}
