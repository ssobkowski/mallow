use smol_str::SmolStr;

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
    /// Creates an empty block.
    pub fn new() -> Self {
        Self { stmts: Vec::new() }
    }

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
    /// Function declaration.
    Function {
        /// Function name.
        name: Identifier,
        /// Function parameters.
        params: Vec<Parameter>,
        /// Function body.
        body: Block,
        /// Whether this is `local function ...`.
        local: bool,
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
    If {
        /// Condition expression.
        condition: Expr,
        /// Then branch body.
        then_body: Block,
        /// Optional else branch body.
        else_body: Option<Block>,
    },
    /// `local a, b = ...`.
    LocalDeclaration {
        /// Declared local names.
        names: Vec<Identifier>,
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
    /// `repeat ... until ...`.
    Repeat {
        /// Repeat body.
        body: Block,
        /// Termination condition.
        condition: Expr,
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
        /// Function parameters.
        params: Vec<Parameter>,
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
    /// Numeric literal.
    Number(f64),
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
    /// Regular parameter name.
    Regular(Identifier),
    /// Vararg parameter (`...`).
    Vararg,
}

/// Binary operator.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
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
    /// Returns the precedence level of this binary operator.
    pub fn precedence(&self) -> u8 {
        match self {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => 3,
            BinOp::Concat => 4,
            BinOp::Add | BinOp::Sub => 5,
            BinOp::Mul | BinOp::Div | BinOp::Mod => 6,
            BinOp::Pow => 8,
        }
    }
}

/// Compound assignment operator.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CompoundBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Concat,
}

/// Unary operator.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnOp {
    Minus,
    Length,
    Not,
}
