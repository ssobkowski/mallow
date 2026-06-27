use std::fmt::Display;

use smol_str::SmolStr;

use crate::hil::ty::Type;

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

/// Binary operator.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
    Eq,
    Ne,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    Concat,
}

impl BinOp {
    /// Returns the string representation of this operator.
    pub const fn as_str(&self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::IDiv => "//",
            BinOp::Mod => "%",
            BinOp::Pow => "^",
            BinOp::Eq => "==",
            BinOp::Ne => "~=",
            BinOp::Lt => "<",
            BinOp::Lte => "<=",
            BinOp::Gt => ">",
            BinOp::Gte => ">=",
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Concat => "..",
        }
    }

    /// Returns the precedence level of this binary operator.
    pub const fn precedence(&self) -> u8 {
        match self {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => 3,
            BinOp::Concat => 4,
            BinOp::Add | BinOp::Sub => 5,
            BinOp::Mul | BinOp::Div | BinOp::IDiv | BinOp::Mod => 6,
            BinOp::Pow => 8,
        }
    }

    /// Inverts this binary operator, if it is a comparison operator.
    ///
    /// Returns `None` for non-comparison operators.
    pub const fn invert(self) -> Option<Self> {
        match self {
            BinOp::Eq => Some(BinOp::Ne),
            BinOp::Ne => Some(BinOp::Eq),
            BinOp::Lt => Some(BinOp::Gte),
            BinOp::Lte => Some(BinOp::Gt),
            BinOp::Gt => Some(BinOp::Lte),
            BinOp::Gte => Some(BinOp::Lt),
            _ => None,
        }
    }

    /// Returns the flipped comparison operator.
    ///
    /// Returns `None` if the operator is not a comparison operator.
    /// For operators that cannot be flipped, returns `self`.
    pub const fn flip(self) -> Option<Self> {
        match self {
            BinOp::Eq => Some(BinOp::Eq),
            BinOp::Ne => Some(BinOp::Ne),
            BinOp::Lt => Some(BinOp::Gt),
            BinOp::Lte => Some(BinOp::Gte),
            BinOp::Gt => Some(BinOp::Lt),
            BinOp::Gte => Some(BinOp::Lte),
            _ => None,
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Compound assignment operator.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CompoundBinOp {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
    Concat,
}

impl CompoundBinOp {
    /// Returns the string representation of this compound assignment operator.
    pub const fn as_str(&self) -> &'static str {
        match self {
            CompoundBinOp::Add => "+=",
            CompoundBinOp::Sub => "-=",
            CompoundBinOp::Mul => "*=",
            CompoundBinOp::Div => "/=",
            CompoundBinOp::IDiv => "//=",
            CompoundBinOp::Mod => "%=",
            CompoundBinOp::Pow => "^=",
            CompoundBinOp::Concat => "..=",
        }
    }
}

impl Display for CompoundBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl TryFrom<BinOp> for CompoundBinOp {
    type Error = ();

    fn try_from(op: BinOp) -> Result<Self, Self::Error> {
        match op {
            BinOp::Add => Ok(CompoundBinOp::Add),
            BinOp::Sub => Ok(CompoundBinOp::Sub),
            BinOp::Mul => Ok(CompoundBinOp::Mul),
            BinOp::Div => Ok(CompoundBinOp::Div),
            BinOp::IDiv => Ok(CompoundBinOp::IDiv),
            BinOp::Mod => Ok(CompoundBinOp::Mod),
            BinOp::Pow => Ok(CompoundBinOp::Pow),
            BinOp::Concat => Ok(CompoundBinOp::Concat),
            _ => Err(()),
        }
    }
}

/// Unary operator.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnOp {
    Minus,
    Length,
    Not,
}

impl UnOp {
    /// Returns the string representation of this unary operator.
    pub const fn as_str(&self) -> &'static str {
        match self {
            UnOp::Minus => "-",
            UnOp::Length => "#",
            UnOp::Not => "not",
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
