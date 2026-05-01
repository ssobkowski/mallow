use std::fmt::Display;

use smol_str::SmolStr;

use crate::ast::{BinOp, UnOp};
use crate::common::ToSpanned;
use crate::hil::lifter::ssa::SymbolId;

/// An expression in the high-level intermediate representation.
#[derive(Debug, Clone, PartialEq)]
pub enum HilExpr {
    /// The `nil` value.
    Nil,
    /// A numeric literal.
    Number(f64),
    /// A string literal.
    String(String),
    /// A boolean literal.
    Bool(bool),
    /// A symbol, an universal variable reference.
    Symbol(SymbolId),
    /// A closure literal and the proto/captures needed to rebuild nested functions.
    Closure {
        proto: usize,
        captures: Vec<SymbolId>,
    },
    /// A global variable, identified by its name.
    Global(SmolStr),
    /// A Luau import path, identified by its printable source name.
    Import(SmolStr),
    /// A field access expression (`obj.field`).
    GetField { obj: Box<HilExpr>, field: SmolStr },
    /// An index access expression (`obj[index]`).
    GetIndex {
        obj: Box<HilExpr>,
        index: Box<HilExpr>,
    },
    /// A function call expression (`fun(args...)`).
    Call {
        fun: Box<HilExpr>,
        args: Vec<HilExpr>,
    },
    /// A method call expression (`obj:method(args...)`).
    MethodCall {
        object: Box<HilExpr>,
        method: SmolStr,
        args: Vec<HilExpr>,
    },
    /// A binary expression.
    Binary {
        lhs: Box<HilExpr>,
        op: BinOp,
        rhs: Box<HilExpr>,
    },
    /// An unary expression.
    Unary { op: UnOp, expr: Box<HilExpr> },
    /// A table constructor with a list of implicit values.
    Table { items: Vec<HilTableItem> },
    /// Vararg expression (`...`).
    VarArgs,
}

impl HilExpr {
    /// Returns whether this expressions reads a given symbol.
    pub fn reads_symbol(&self, sym: &SymbolId) -> bool {
        match self {
            HilExpr::Symbol(s) => s == sym,
            HilExpr::GetField { obj, .. } => obj.reads_symbol(sym),
            HilExpr::GetIndex { obj, index } => obj.reads_symbol(sym) || index.reads_symbol(sym),
            HilExpr::Call { fun, args } => {
                fun.reads_symbol(sym) || args.iter().any(|arg| arg.reads_symbol(sym))
            }
            HilExpr::MethodCall { object, args, .. } => {
                object.reads_symbol(sym) || args.iter().any(|arg| arg.reads_symbol(sym))
            }
            HilExpr::Binary { lhs, rhs, .. } => lhs.reads_symbol(sym) || rhs.reads_symbol(sym),
            HilExpr::Unary { expr, .. } => expr.reads_symbol(sym),
            HilExpr::Table { items } => items.iter().any(|item| match item {
                HilTableItem::List(expr) => expr.reads_symbol(sym),
                HilTableItem::Index(key, value) => key.reads_symbol(sym) || value.reads_symbol(sym),
            }),
            _ => false,
        }
    }

    /// Returns whether this expression is pure, i.e. it does not have any side effects.
    pub const fn is_pure(&self) -> bool {
        match self {
            HilExpr::Nil
            | HilExpr::Number(_)
            | HilExpr::String(_)
            | HilExpr::Bool(_)
            | HilExpr::Symbol(_)
            | HilExpr::Global(_)
            | HilExpr::Import(_) => true,
            HilExpr::GetField { obj, .. } => obj.is_pure(),
            HilExpr::GetIndex { obj, index } => obj.is_pure() && index.is_pure(),
            HilExpr::Unary { expr, .. } => expr.is_pure(),
            HilExpr::Binary { lhs, rhs, .. } => lhs.is_pure() && rhs.is_pure(),
            HilExpr::Closure { .. }
            | HilExpr::Call { .. }
            | HilExpr::MethodCall { .. }
            | HilExpr::Table { .. }
            | HilExpr::VarArgs => false,
        }
    }

    /// Returns whether this expression is truthy.
    ///
    /// Returns `Some(true)` for truthy values, `Some(false)` for falsy values,
    /// and `None` for values that are not determinable at compile time.
    pub const fn truthiness(&self) -> Option<bool> {
        match self {
            HilExpr::Nil => Some(false),
            HilExpr::Bool(value) => Some(*value),
            HilExpr::Number(_)
            | HilExpr::String(_)
            | HilExpr::Closure { .. }
            | HilExpr::Table { .. } => Some(true),
            _ => None,
        }
    }

    /// Returns the inverted expression, i.e. `!expr`.
    pub fn invert(self) -> HilExpr {
        match self {
            HilExpr::Bool(b) => HilExpr::Bool(!b),
            HilExpr::Binary { lhs, op, rhs } if let Some(inverted) = op.invert() => {
                HilExpr::Binary {
                    lhs: Box::new(*lhs),
                    op: inverted,
                    rhs: Box::new(*rhs),
                }
            }
            HilExpr::Unary {
                op: UnOp::Not,
                expr: inner,
            } => *inner,
            other => HilExpr::Unary {
                op: UnOp::Not,
                expr: Box::new(other),
            },
        }
    }
}

impl Display for HilExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HilExpr::Nil => write!(f, "nil"),
            HilExpr::Number(n) => write!(f, "{}", n),
            HilExpr::String(s) => write!(f, "\"{}\"", s),
            HilExpr::Bool(b) => write!(f, "{}", b),
            HilExpr::Symbol(s) => write!(f, "v{}", s.index()),
            HilExpr::Closure { proto, .. } => write!(f, "<closure {}>", proto),
            HilExpr::Global(g) => write!(f, "{}", g),
            HilExpr::Import(i) => write!(f, "import(\"{}\")", i),
            HilExpr::GetField { obj, field } => write!(f, "{}.{}", obj, field),
            HilExpr::GetIndex { obj, index } => write!(f, "{}[{}]", obj, index),
            HilExpr::Call { fun, args } => {
                write!(f, "call {}(", fun)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            HilExpr::MethodCall {
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
            HilExpr::Binary { lhs, op, rhs } => write!(f, "{} {} {}", lhs, op, rhs),
            HilExpr::Unary { op, expr } => {
                if op == &UnOp::Not {
                    write!(f, "not ({})", expr)
                } else {
                    write!(f, "{}{}", op, expr)
                }
            }
            HilExpr::Table { items } => {
                if items.is_empty() {
                    write!(f, "{{}}")
                } else {
                    unimplemented!()
                }
            }
            HilExpr::VarArgs => write!(f, "..."),
        }
    }
}

/// An entry in the table constructor.
#[derive(Debug, Clone, PartialEq)]
pub enum HilTableItem {
    /// An array-part value, e.g., `value` in `{ value }`
    List(HilExpr),
    /// A generic expression-keyed dictionary value, e.g., `[key] = value`
    Index(HilExpr, HilExpr),
}

#[derive(Debug, Clone)]
pub struct PhiNode {
    pub target: SymbolId,
    pub operands: Vec<(usize, SymbolId)>,
}

/// A statement in the high-level intermediate representation.
#[derive(Debug, Clone)]
pub enum HilStmt {
    /// An assignment statement, like `foo = 123`.
    Assign { left: HilExpr, value: HilExpr },
    /// A multi-variable assignment statement, like `a, b = returns_tuple()`.
    AssignMany { left: Vec<HilExpr>, value: HilExpr },
    /// A bulk array write lowered from `SETLIST`.
    SetList {
        table: SymbolId,
        index: u32,
        values: Vec<HilExpr>,
        has_variadic_tail: bool,
    },
    /// A call statement.
    Call(HilExpr),
    /// A "Phi-Node", used for merging symbols between region blocks.
    Phi(PhiNode),
}

impl Display for HilStmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HilStmt::Assign { left, value } => write!(f, "{} = {}", left, value),
            HilStmt::AssignMany { left, value } => {
                for (i, lv) in left.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", lv)?;
                }
                write!(f, " = {}", value)
            }
            HilStmt::SetList {
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
            HilStmt::Call(expr) => write!(f, "{}", expr),
            HilStmt::Phi(_) => Ok(()),
        }
    }
}

impl ToSpanned for HilExpr {}
impl ToSpanned for HilStmt {}
