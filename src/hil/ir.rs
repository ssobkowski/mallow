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
    /// A table constructor with a list of implicit values.
    Table { items: Vec<HilTableItem> },
    /// Vararg expression (`...`).
    VarArgs,
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
    /// A table-field assignment lowered from opcodes such as `SETTABLEKS`.
    SetField {
        table: SymbolId,
        key: SmolStr,
        value: HilExpr,
    },
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
