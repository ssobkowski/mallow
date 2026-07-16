use smol_str::SmolStr;

use crate::{
    hil::ty::Type,
    operator::{BinOp, CompoundBinOp, UnOp},
};

/// An identifier such as `foo`.
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(pub SmolStr);

impl Identifier {
    /// Creates a new identifier from any string-like input.
    pub fn new(name: impl Into<SmolStr>) -> Self {
        Self(name.into())
    }

    /// Returns the identifier as `&str`.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl<T> From<T> for Identifier
where
    T: Into<SmolStr>,
{
    fn from(value: T) -> Self {
        Identifier::new(value)
    }
}

/// Represents a block of statements.
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    /// Statements in lexical order.
    pub stmts: Vec<Stmt>,
}

impl Block {
    /// Creates a block with pre-populated statements.
    pub fn with_stmts(stmts: Vec<Stmt>) -> Self {
        Self { stmts }
    }

    /// Returns an iterator over statements in this block.
    pub fn stmts(&self) -> impl Iterator<Item = &Stmt> {
        self.stmts.iter()
    }
}

/// A standalone statement.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// Assignment, e.g. `a, b = 1, 2`.
    Assignment {
        /// Left-hand side expressions.
        lhs: Vec<Expr>,
        /// Right-hand side expressions.
        rhs: Vec<Expr>,
    },
    /// `break`.
    Break,
    /// A single line comment.
    Comment {
        /// The comment text.
        text: String,
    },
    /// Compount assignment statement, e.g. `a += 5`
    CompoundAssignment {
        /// Left-hand side expression.
        lhs: Expr,
        /// Operator.
        op: CompoundBinOp,
        /// Right-hand side expression.
        rhs: Expr,
    },
    /// `continue`.
    Continue,
    /// `do ... end`.
    Do {
        /// Body of the do-block.
        body: Block,
    },
    /// Standalone expression statement.
    Expression {
        /// Expression being evaluated.
        expr: Expr,
    },
    /// Generic `for ... in ... do`.
    GenericFor {
        /// Iteration variables.
        vars: Vec<Identifier>,
        /// Iterator/source expressions.
        exprs: Vec<Expr>,
        /// Loop body.
        body: Block,
    },
    /// `if ... then ... [else ...] end`.
    If(If),
    /// `local function name(params): type body end`.
    LocalFunction {
        /// Function name.
        name: Identifier,
        /// Generic parameters declared by the function.
        generics: Vec<SmolStr>,
        /// Function parameters.
        params: Vec<Typed<Parameter>>,
        /// Function body.
        body: Block,
        /// Optional return type.
        ty: Option<Type>,
    },
    /// `local a, b = ...`.
    LocalDeclaration {
        /// Declared local names with optional types.
        names: Vec<Typed<Identifier>>,
        /// Optional initial values.
        values: Vec<Expr>,
    },
    /// Numeric `for`.
    NumericFor {
        /// Loop variable.
        var: Identifier,
        /// Start expression.
        start: Expr,
        /// End expression.
        end: Expr,
        /// Optional step expression.
        step: Option<Expr>,
        /// Loop body.
        body: Block,
    },
    /// `return ...`.
    Return {
        /// Returned values.
        values: Vec<Expr>,
    },
    /// `while ... do ... end`.
    While {
        /// Loop condition.
        condition: Expr,
        /// Loop body.
        body: Block,
    },
    /// `repeat ... until ...` loop.
    RepeatUntil {
        /// Loop condition.
        condition: Expr,
        /// Loop body.
        body: Block,
    },
}

/// An if statement.
#[derive(Debug, Clone, PartialEq)]
pub struct If {
    /// Condition expression.
    pub condition: Expr,
    /// Then branch body.
    pub then_body: Block,
    /// Optional else clause.
    pub else_clause: Option<ElseClause>,
}

/// An else clause.
#[derive(Debug, Clone, PartialEq)]
pub enum ElseClause {
    /// Elseif clause.
    If(Box<If>),
    /// Else clause.
    Else(Block),
}

/// An expression node.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Identifier reference.
    Named(Identifier),
    /// Binary expression.
    Binary {
        /// Left operand.
        lhs: Box<Expr>,
        /// Binary operator.
        op: BinOp,
        /// Right operand.
        rhs: Box<Expr>,
    },
    /// Unary expression.
    Unary {
        /// Unary operator.
        op: UnOp,
        /// Operand expression.
        expr: Box<Expr>,
    },
    /// An explicitly parenthesized expression.
    Parenthesized(Box<Expr>),
    /// Function call expression.
    FunctionCall {
        /// Callee expression.
        func: Box<Expr>,
        /// Call arguments.
        args: Vec<Expr>,
    },
    /// Method call expression (`obj:method(...)`).
    MethodCall {
        /// Method receiver/object.
        object: Box<Expr>,
        /// Method name.
        method: Identifier,
        /// Method arguments.
        args: Vec<Expr>,
    },
    /// Luau if-expression (`if cond then a else b`).
    IfElse {
        /// Condition expression.
        condition: Box<Expr>,
        /// Then branch value.
        then_expr: Box<Expr>,
        /// Else branch value.
        else_expr: Box<Expr>,
    },
    /// Anonymous function expression.
    AnonymousFunction {
        /// Generic parameters declared by the function expression.
        generics: Vec<SmolStr>,
        /// Function parameters.
        params: Vec<Typed<Parameter>>,
        /// Function body.
        body: Block,
    },
    /// Field access (`base.field`).
    Field {
        /// Base expression.
        base: Box<Expr>,
        /// Field identifier.
        field: Identifier,
    },
    /// Index access (`base[index]`).
    Index {
        /// Base expression.
        base: Box<Expr>,
        /// Index expression.
        index: Box<Expr>,
    },
    /// Table constructor expression.
    Table {
        /// Table items.
        items: Vec<TableItem>,
    },
    /// Vararg expression (`...`).
    Vararg,
    /// Literal expression.
    Literal(Literal),
}

/// Literal values.
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    /// `nil`.
    Nil,
    /// Luau integer literal.
    Integer(i64),
    /// Float literal.
    Float(f64),
    /// String literal.
    String(SmolStr),
    /// Boolean literal.
    Bool(bool),
}

/// A field in a table constructor.
#[derive(Debug, Clone, PartialEq)]
pub enum TableItem {
    /// Named field (`foo = value`).
    Named { name: Identifier, value: Expr },
    /// Indexed field (`[key] = value`).
    Indexed { index: Expr, value: Expr },
    /// Implicit array-style field (`value`).
    Implicit { value: Expr },
}

/// Function parameter.
#[derive(Debug, Clone, PartialEq)]
pub enum Parameter {
    /// Regular parameter name with an optional type.
    Regular(Identifier),
    /// Typed vararg parameter (`...`).
    Vararg,
}

/// A wrapper for a node with an optional type annotation.
#[derive(Debug, Clone, PartialEq)]
pub struct Typed<T> {
    node: T,
    ty: Option<Type>,
}

impl<T> Typed<T> {
    pub const fn new(node: T, ty: Type) -> Self {
        Self { node, ty: Some(ty) }
    }

    pub const fn untyped(node: T) -> Self {
        Self { node, ty: None }
    }

    pub const fn as_ref(&self) -> &T {
        &self.node
    }

    pub const fn ty(&self) -> Option<&Type> {
        self.ty.as_ref()
    }
}
