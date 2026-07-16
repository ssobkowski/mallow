use std::fmt::Display;

use anyhow::{Context, Result, bail};
use smol_str::{SmolStr, ToSmolStr};

use crate::disasm::Chunk;
use crate::hil::lifter::ssa::SymbolId;
use crate::il::{Constant, ImportPath, Proto, ProtoId};
use crate::operator::{BinOp, UnOp};

/// A numeric literal.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Number {
    /// A 64-bit Luau integer literal.
    Integer(i64),
    /// A floating-point literal.
    Float(f64),
}

impl std::fmt::Display for Number {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Number::Integer(n) => write!(f, "{}i", n),
            Number::Float(n) => write!(f, "{}", n),
        }
    }
}

/// An expression in the high-level intermediate representation.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// The `nil` value.
    Nil,
    /// A numeric literal.
    Number(Number),
    /// A string literal.
    String(String),
    /// A boolean literal.
    Bool(bool),
    /// A symbol, an universal variable reference.
    Symbol(SymbolId),
    /// A closure literal and the proto/captures needed to rebuild nested functions.
    Closure {
        proto: ProtoId,
        captures: Vec<SymbolId>,
    },
    /// A global variable, identified by its name.
    Global(SmolStr),
    /// A field access expression (`obj.field`).
    GetField { obj: Box<Expr>, field: SmolStr },
    /// An index access expression (`obj[index]`).
    GetIndex { obj: Box<Expr>, index: Box<Expr> },
    /// A function call expression (`fun(args...)`).
    Call { fun: Box<Expr>, args: Vec<Expr> },
    /// A method call expression (`obj:method(args...)`).
    MethodCall {
        object: Box<Expr>,
        method: SmolStr,
        args: Vec<Expr>,
    },
    /// A binary expression.
    Binary {
        lhs: Box<Expr>,
        op: BinOp,
        rhs: Box<Expr>,
    },
    /// An unary expression.
    Unary { op: UnOp, expr: Box<Expr> },
    /// A Luau if-expression (`if cond then a else b`).
    IfElse {
        condition: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    /// A table constructor with a list of implicit values.
    Table { items: Vec<TableItem> },
    /// Vararg expression (`...`).
    VarArgs,
}

impl Expr {
    /// Returns a new [`Expr::Binary`] expression with the given operands,
    /// and the [`BinOp::And`] operator.
    pub fn and(lhs: Expr, rhs: Expr) -> Self {
        Expr::Binary {
            lhs: Box::new(lhs),
            op: BinOp::And,
            rhs: Box::new(rhs),
        }
    }

    /// Returns a new [`Expr::Binary`] expression with the given operands,
    /// and the [`BinOp::Or`] operator.
    pub fn or(lhs: Expr, rhs: Expr) -> Self {
        Expr::Binary {
            lhs: Box::new(lhs),
            op: BinOp::Or,
            rhs: Box::new(rhs),
        }
    }

    /// Returns a new [`Expr::Unary`] expression with the given operand and the
    /// [`UnOp::Not`] operator.
    pub fn not(expr: Expr) -> Self {
        Expr::Unary {
            op: UnOp::Not,
            expr: Box::new(expr),
        }
    }

    /// Returns whether this expressions reads a given symbol.
    pub fn reads_symbol(&self, sym: &SymbolId) -> bool {
        match self {
            Expr::Symbol(s) => s == sym,
            Expr::GetField { obj, .. } => obj.reads_symbol(sym),
            Expr::GetIndex { obj, index } => obj.reads_symbol(sym) || index.reads_symbol(sym),
            Expr::Call { fun, args } => {
                fun.reads_symbol(sym) || args.iter().any(|arg| arg.reads_symbol(sym))
            }
            Expr::MethodCall { object, args, .. } => {
                object.reads_symbol(sym) || args.iter().any(|arg| arg.reads_symbol(sym))
            }
            Expr::Binary { lhs, rhs, .. } => lhs.reads_symbol(sym) || rhs.reads_symbol(sym),
            Expr::Unary { expr, .. } => expr.reads_symbol(sym),
            Expr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => {
                condition.reads_symbol(sym)
                    || then_expr.reads_symbol(sym)
                    || else_expr.reads_symbol(sym)
            }
            Expr::Table { items } => items.iter().any(|item| match item {
                TableItem::List(expr) => expr.reads_symbol(sym),
                TableItem::Index(key, value) => key.reads_symbol(sym) || value.reads_symbol(sym),
            }),
            _ => false,
        }
    }

    /// Returns whether this expression is pure, i.e. it does not have any side effects.
    pub const fn is_pure(&self) -> bool {
        match self {
            Expr::Nil
            | Expr::Number(_)
            | Expr::String(_)
            | Expr::Bool(_)
            | Expr::Symbol(_)
            | Expr::Global(_) => true,
            Expr::GetField { obj, .. } => obj.is_pure(),
            Expr::GetIndex { obj, index } => obj.is_pure() && index.is_pure(),
            Expr::Unary { expr, .. } => expr.is_pure(),
            Expr::Binary { lhs, rhs, .. } => lhs.is_pure() && rhs.is_pure(),
            Expr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => condition.is_pure() && then_expr.is_pure() && else_expr.is_pure(),
            Expr::Closure { .. }
            | Expr::Call { .. }
            | Expr::MethodCall { .. }
            | Expr::Table { .. }
            | Expr::VarArgs => false,
        }
    }

    /// Returns whether this expression is a literal expression.
    pub const fn is_literal(&self) -> bool {
        matches!(
            self,
            Expr::Nil | Expr::Number(_) | Expr::String(_) | Expr::Bool(_)
        )
    }

    /// Returns whether this expression is truthy.
    ///
    /// Returns `Some(true)` for truthy values, `Some(false)` for falsy values,
    /// and `None` for values that are not determinable at compile time.
    pub const fn truthiness(&self) -> Option<bool> {
        match self {
            Expr::Nil => Some(false),
            Expr::Bool(value) => Some(*value),
            Expr::Number(_) | Expr::String(_) | Expr::Closure { .. } | Expr::Table { .. } => {
                Some(true)
            }
            _ => None,
        }
    }

    /// Returns the semantic negation of this expression.
    ///
    /// Ordered comparisons are wrapped in `not` instead of being converted to
    /// the opposite comparison because values such as NaN make those forms
    /// observably different.
    pub fn invert(self) -> Expr {
        match self {
            Expr::Bool(b) => Expr::Bool(!b),
            Expr::Binary {
                lhs,
                op: op @ (BinOp::Eq | BinOp::Ne),
                rhs,
            } => {
                let inverted = op.invert().expect("equality operators are invertible");
                Expr::Binary {
                    lhs: Box::new(*lhs),
                    op: inverted,
                    rhs: Box::new(*rhs),
                }
            }
            Expr::Unary {
                op: UnOp::Not,
                expr: inner,
            } => *inner,
            other => Expr::not(other),
        }
    }

    /// Returns the HIL expression corresponding to the given constant value.
    pub fn from_constant(ct: &Constant, chunk: &Chunk, proto: &Proto) -> Result<Self> {
        match ct {
            Constant::Nil => Ok(Self::Nil),
            Constant::Boolean(b) => Ok(Self::Bool(*b)),
            Constant::Number(n) => Ok(Self::Number(Number::Float(*n))),
            Constant::String(s) => Ok(Self::String(
                chunk
                    .get_string(*s)
                    .with_context(|| format!("invalid string key {:?}", *s))?
                    .to_string(),
            )),
            Constant::Import(i) => Self::import(*i, chunk, proto),
            Constant::Table => Ok(Self::Table { items: Vec::new() }),
            Constant::Closure(_) => bail!("constant closures aren't supported"),
            Constant::Vector { x, y, z, w } => Ok({
                Self::Call {
                    fun: Box::new(Self::GetField {
                        obj: Box::new(Self::Global("vector".into())),
                        field: "create".into(),
                    }),
                    args: [x, y, z, w]
                        .map(|x| Self::Number(Number::Float(*x as f64)))
                        .to_vec(),
                }
            }),
            Constant::TableWithConstants(consts) => {
                let mut items = Vec::with_capacity(consts.len());
                for (key_id, value_id) in consts {
                    let Some(value_id) = value_id else {
                        continue;
                    };
                    let key = proto
                        .get_constant(*key_id)
                        .with_context(|| format!("constant with key {:?} was not found", key_id))?;
                    let value = proto.get_constant(*value_id).with_context(|| {
                        format!("constant with value {:?} was not found", value_id)
                    })?;
                    items.push(TableItem::Index(
                        Self::from_constant(key, chunk, proto)?,
                        Self::from_constant(value, chunk, proto)?,
                    ));
                }
                Ok(Self::Table { items })
            }
            Constant::Integer(n) => Ok(Self::Number(Number::Integer(*n))),
        }
    }

    /// Returns the access expression built from a packed import path.
    pub fn import(path: ImportPath, chunk: &Chunk, proto: &Proto) -> Result<Expr> {
        let mut names = Vec::new();

        for id in path.const_ids()? {
            let Some(Constant::String(string_id)) = proto.get_constant(id) else {
                bail!("import path component {id:?} is not a string constant");
            };

            names.push(
                chunk
                    .get_string(*string_id)
                    .with_context(|| format!("invalid import string id {string_id:?}"))?
                    .to_smolstr(),
            );
        }

        let first = names.remove(0);
        let mut expr = Expr::Global(first);

        for field in names {
            expr = Expr::GetField {
                obj: Box::new(expr),
                field,
            };
        }

        Ok(expr)
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Nil => write!(f, "nil"),
            Expr::Number(n) => write!(f, "{}", n),
            Expr::String(s) => write!(f, "\"{}\"", s),
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::Symbol(s) => write!(f, "v{}", s.index()),
            Expr::Closure { proto, .. } => write!(f, "<closure {}>", proto),
            Expr::Global(g) => write!(f, "{}", g),
            Expr::GetField { obj, field } => write!(f, "{}.{}", obj, field),
            Expr::GetIndex { obj, index } => write!(f, "{}[{}]", obj, index),
            Expr::Call { fun, args } => {
                write!(f, "call {}(", fun)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            Expr::MethodCall {
                object,
                method,
                args,
            } => {
                write!(f, "call {}:{}(", object, method)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            Expr::Binary { lhs, op, rhs } => write!(f, "{} {} {}", lhs, op, rhs),
            Expr::Unary { op, expr } => {
                if op == &UnOp::Not {
                    write!(f, "not ({})", expr)
                } else {
                    write!(f, "{}{}", op, expr)
                }
            }
            Expr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => {
                write!(f, "if {} then {} else {}", condition, then_expr, else_expr)
            }
            Expr::Table { items } => {
                if items.is_empty() {
                    write!(f, "{{}}")
                } else {
                    unimplemented!()
                }
            }
            Expr::VarArgs => write!(f, "..."),
        }
    }
}

/// An entry in the table constructor.
#[derive(Debug, Clone, PartialEq)]
pub enum TableItem {
    /// An array-part value, e.g., `value` in `{ value }`
    List(Expr),
    /// A generic expression-keyed dictionary value, e.g., `[key] = value`
    Index(Expr, Expr),
}

#[derive(Debug, Clone)]
pub struct PhiNode {
    pub target: SymbolId,
    pub operands: Vec<(usize, SymbolId)>,
}

/// A statement in the high-level intermediate representation.
#[derive(Debug, Clone)]
pub enum Stmt {
    /// An assignment statement, like `foo = 123`.
    Assign { left: Expr, value: Expr },
    /// A multi-variable assignment statement, like `a, b = returns_tuple()`.
    AssignMany { left: Vec<Expr>, value: Expr },
    /// A bulk array write lowered from `SETLIST`.
    SetList {
        table: SymbolId,
        index: u32,
        values: Vec<Expr>,
        has_variadic_tail: bool,
    },
    /// A call statement.
    Call(Expr),
    /// A "Phi-Node", used for merging symbols between region blocks.
    Phi(PhiNode),
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::Assign { left, value } => write!(f, "{} = {}", left, value),
            Stmt::AssignMany { left, value } => {
                for (i, lv) in left.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", lv)?;
                }
                write!(f, " = {}", value)
            }
            Stmt::SetList {
                table,
                index,
                values,
                has_variadic_tail,
            } => {
                write!(
                    f,
                    "setlist v{}[{}..{}] = [",
                    table.index(),
                    index,
                    *index as usize + values.len()
                )?;
                for (i, v) in values.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                if *has_variadic_tail {
                    write!(f, ", ...")?;
                }
                write!(f, "]")
            }
            Stmt::Call(expr) => write!(f, "{}", expr),
            Stmt::Phi(_) => Ok(()),
        }
    }
}
