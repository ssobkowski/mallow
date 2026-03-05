use crate::ast::{BinOp, UnOp};

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
    /// A value captured by a closure.
    CaptureValue(Box<HilExpr>),
    /// A local variable, identified by its register index.
    Local(u8),
    /// An upvalue, identified by its index in the function's upvalue list.
    Upval(u8),
    /// A closure literal and the proto/captures needed to rebuild nested functions.
    Closure {
        proto: usize,
        captures: Vec<HilExpr>,
    },
    /// A global variable, identified by its name.
    Global(String),
    /// A Luau import path, identified by its printable source name.
    Import(String),
    /// A field access expression (`obj.field`).
    GetField { obj: Box<HilExpr>, field: String },
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
        method: String,
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
    Table { items: Vec<HilExpr> },
    /// Vararg expression (`...`).
    VarArgs,
}

/// A statement in the high-level intermediate representation.
#[derive(Debug, Clone)]
pub enum HilStmt {
    /// An assignment statement, like `foo = 123`.
    Assign { left: HilExpr, value: HilExpr },
    /// A multi-variable assignment statement, like `a, b = returns_tuple()`.
    AssignMany { left: Vec<HilExpr>, value: HilExpr },
    /// A table-field assignment lowered from opcodes such as `SETTABLEKS`.
    SetField {
        table: u8,
        key: String,
        value: HilExpr,
    },
    /// A bulk array write lowered from `SETLIST`.
    SetList {
        table: u8,
        index: u32,
        values: Vec<HilExpr>,
        has_variadic_tail: bool,
    },
    /// A call statement.
    Call(HilExpr),
    /// A return statement.
    Return(Vec<HilExpr>),
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
