use std::fmt::Display;

use smol_str::SmolStr;

use crate::ast::{BinOp, UnOp};
use crate::hil::lifter::ssa::SymbolId;

/// A wrapper that attaches a bytecode PC to any IR node.
#[derive(Debug, Clone)]
pub struct Spanned<T> {
    pub inner: T,
    pub pc: usize,
}

impl<T> Spanned<T> {
    pub fn new(inner: T, pc: usize) -> Self {
        Self { inner, pc }
    }
}

/// An expression in the high-level intermediate representation.
#[derive(Debug, Clone)]
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
    /// A Luau if-expression (`if cond then a else b`).
    If {
        condition: Box<HilExpr>,
        then_expr: Box<HilExpr>,
        else_expr: Box<HilExpr>,
    },
    /// A table constructor with a list of implicit values.
    Table { items: Vec<HilTableItem> },
    /// Vararg expression (`...`).
    VarArgs,
}

impl HilExpr {
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
            HilExpr::If {
                condition,
                then_expr,
                else_expr,
            } => {
                condition.reads_symbol(sym)
                    || then_expr.reads_symbol(sym)
                    || else_expr.reads_symbol(sym)
            }
            HilExpr::Table { items } => items.iter().any(|item| match item {
                HilTableItem::List(expr) => expr.reads_symbol(sym),
                HilTableItem::Index(key, value) => key.reads_symbol(sym) || value.reads_symbol(sym),
                HilTableItem::Packed(expr) => expr.reads_symbol(sym),
            }),
            _ => false,
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
            HilExpr::If {
                condition,
                then_expr,
                else_expr,
            } => write!(f, "if {} then {} else {}", condition, then_expr, else_expr),
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

/// One closure capture operand attached to a nested function literal.
#[derive(Debug, Clone)]
pub enum HilCapture {
    /// Capture a local from the current frame by its value.
    Value(SymbolId),
    /// Capture a local from the current frame by its reference.
    Ref(SymbolId),
}

/// An entry in the table constructor.
#[derive(Debug, Clone)]
pub enum HilTableItem {
    /// An array-part value, e.g., `value` in `{ value }`
    List(HilExpr),
    /// A generic expression-keyed dictionary value, e.g., `[key] = value`
    Index(HilExpr, HilExpr),
    /// An array of packed expressions, that needs to be unpacked into the target
    /// table. Used to carry over multirets into the table constructor.
    Packed(HilExpr),
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
    ///
    /// Unlike the [regular Assign](HilStmt::Assign), the left hand side of this assignment
    /// holds [SymbolId]s for the sake of simplicity, as no other lvalue gets emitted by the luau compiler.
    AssignMany { left: Vec<SymbolId>, value: HilExpr },
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
                    write!(f, "v{}", lv.index())?;
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

pub trait ToSpanned {
    fn to_spanned(self, pc: usize) -> Spanned<Self>
    where
        Self: Sized,
    {
        Spanned::new(self, pc)
    }
}

impl ToSpanned for HilExpr {}
impl ToSpanned for HilStmt {}
