//! Nested intermediate representation used after control-flow recognition.

pub(crate) mod materialize;
pub(crate) mod passes;
pub(crate) mod visitor;

use id_arena::{Arena, Id};
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::hil::ir::CellId;
use crate::il::ProtoId;
use crate::ir::fir::{Constant, PackId, ValueId};
use crate::ir::nir::visitor::{Visitor, walk_expr, walk_pack_expr};
use crate::operator::{BinOp, UnOp};

/// Stable identity for one NIR scalar local.
pub(crate) type LocalId = Id<Local>;

/// Stable identity for one materialized value pack.
pub(crate) type PackLocalId = Id<PackLocal>;

/// One scalar local.
#[derive(Debug, Clone)]
pub(crate) struct Local {
    /// Canonical FIR value represented by this local.
    pub(crate) source: ValueId,
}

/// One materialized pack with FIR provenance.
#[derive(Debug, Clone)]
pub(crate) struct PackLocal {
    /// FIR pack represented by this local.
    pub(crate) source: PackId,
}

/// A value or cell captured by a closure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Capture {
    /// Copies one local value into the closure.
    Copy(LocalId),
    /// Shares one mutable cell with the closure.
    Share(CellId),
}

/// One nested value expression.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Expr {
    /// Reads one stable local.
    Local(LocalId),
    /// Evaluates one literal.
    Constant(Constant),
    /// Creates a closure.
    Closure {
        /// Child function prototype.
        proto: ProtoId,
        /// Values and cells captured by the closure.
        captures: Vec<Capture>,
    },
    /// Reads a table entry.
    GetTable {
        /// Table expression.
        table: Box<Expr>,
        /// Key expression.
        key: Box<Expr>,
    },
    /// Reads a global value.
    GetGlobal(SmolStr),
    /// Applies a binary operator.
    Binary {
        /// Left operand.
        lhs: Box<Expr>,
        /// Binary operator.
        op: BinOp,
        /// Right operand.
        rhs: Box<Expr>,
    },
    /// Applies a unary operator.
    Unary {
        /// Unary operator.
        op: UnOp,
        /// Operand.
        value: Box<Expr>,
    },
    /// Concatenates values in evaluation order.
    Concat(Vec<Expr>),
    /// Evaluates one of two values.
    Select {
        /// Selection condition.
        condition: Box<Expr>,
        /// Value used when the condition succeeds.
        then_value: Box<Expr>,
        /// Value used when the condition fails.
        else_value: Box<Expr>,
    },
    /// Creates a new table with the given items.
    Table { items: Vec<TableItem> },
    /// Reads one value from a pack.
    Project {
        /// Pack being projected.
        pack: Box<PackExpr>,
        /// Zero-based projected index.
        index: usize,
    },
    /// Reads one mutable cell.
    LoadCell(CellId),
}

impl Expr {
    /// Creates a local reference.
    #[inline]
    const fn local(local: LocalId) -> Self {
        Self::Local(local)
    }

    /// Creates a literal boolean.
    #[inline]
    const fn boolean(value: bool) -> Self {
        Self::Constant(Constant::Bool(value))
    }

    /// Creates a nil value.
    #[inline]
    const fn nil() -> Self {
        Self::Constant(Constant::Nil)
    }

    /// Creates a 'or' expression with the given operands.
    #[inline]
    pub fn or(left: Self, right: Self) -> Self {
        Self::Binary {
            op: BinOp::Or,
            lhs: Box::new(left),
            rhs: Box::new(right),
        }
    }

    /// Creates an 'and' expression with the given operands.
    #[inline]
    pub fn and(left: Self, right: Self) -> Self {
        Self::Binary {
            op: BinOp::And,
            lhs: Box::new(left),
            rhs: Box::new(right),
        }
    }

    /// Returns whether this expression contains a given [`LocalId`].
    pub fn contains_local(&self, id: LocalId) -> bool {
        let mut contains = Contains {
            target: id,
            found: false,
        };
        contains.visit_expr(self);
        contains.found
    }
}

/// An entry in the table constructor.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TableItem {
    /// Array-part values produced by an expression list.
    List(PackExpr),
    /// A generic expression-keyed dictionary value, e.g., `[key] = value`
    Index(Expr, Expr),
}

/// One nested value-pack expression.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PackExpr {
    /// Reads one stable pack local.
    Local(PackLocalId),
    /// Joins fixed head values with an optional pack tail.
    Values {
        /// Fixed leading values.
        head: Vec<Expr>,
        /// Optional multivalue tail.
        tail: Option<Box<PackExpr>>,
    },
    /// Calls a function and keeps all returned values.
    Call {
        /// Function expression.
        function: Box<Expr>,
        /// Argument pack.
        args: Box<PackExpr>,
    },
    /// Calls one object method and keeps all returned values.
    MethodCall {
        /// Object expression.
        object: Box<Expr>,
        /// Method name.
        method: SmolStr,
        /// Argument pack.
        args: Box<PackExpr>,
    },
    /// Reads all variadic arguments.
    VarArgs,
}

impl PackExpr {
    /// Creates a pack-local reference.
    #[inline]
    #[must_use]
    fn local(local: PackLocalId) -> Self {
        Self::Local(local)
    }

    /// Returns whether this pack expression has a multi-value tail.
    #[inline]
    pub const fn is_open(&self) -> bool {
        matches!(self, Self::Values { tail, .. } if tail.is_some())
    }

    /// Returns the statically stored values in this pack expression, consuming it.
    #[inline]
    pub fn into_iter(self) -> impl Iterator<Item = Expr> {
        let (head, mut tail) = match self {
            Self::Values { head, tail } => (head, tail),
            Self::Local(_) | Self::Call { .. } | Self::MethodCall { .. } | Self::VarArgs => {
                (Vec::new(), None)
            }
        };
        let mut head = head.into_iter();

        std::iter::from_fn(move || {
            loop {
                if let Some(expr) = head.next() {
                    return Some(expr);
                }

                let next = tail.take()?;
                match *next {
                    Self::Values {
                        head: next_head,
                        tail: next_tail,
                    } => {
                        head = next_head.into_iter();
                        tail = next_tail;
                    }
                    Self::Local(_)
                    | Self::Call { .. }
                    | Self::MethodCall { .. }
                    | Self::VarArgs => return None,
                }
            }
        })
    }

    /// Returns the fixed number of values produced by a pack when statically known.
    #[inline]
    pub fn fixed_len(&self) -> Option<usize> {
        match self {
            Self::Values { head, tail } => {
                let tail_len = match tail {
                    Some(tail) => tail.fixed_len()?,
                    None => 0,
                };
                Some(head.len() + tail_len)
            }
            Self::Local(_) | Self::Call { .. } | Self::MethodCall { .. } | Self::VarArgs => None,
        }
    }
}

/// One writable NIR location.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Place {
    /// Writes one source local.
    Local(LocalId),
    /// Writes one mutable cell.
    Cell(CellId),
    /// Writes one global.
    Global(SmolStr),
    /// Writes one table entry.
    Table {
        /// Table expression.
        table: Expr,
        /// Key expression.
        key: Expr,
    },
    /// Drops one multivalue slot without storing it anywhere.
    Discard,
}

/// One materialized NIR statement.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Stmt {
    /// Writes one value into one location.
    Bind {
        /// Destination place.
        target: Place,
        /// Value being written.
        value: Expr,
    },
    /// Binds one multivalue result into a list of places.
    ///
    /// This variant is only constructed by NIR passes, never by lowering.
    BindMany {
        /// Destinations bound left-to-right.
        targets: Vec<Place>,
        /// Expression producing the bindings.
        values: Box<PackExpr>,
    },
    /// Introduces one materialized pack local that outlived folding.
    BindPack {
        /// Pack local being introduced.
        local: PackLocalId,
        /// Pack assigned to the local.
        value: PackExpr,
    },
    /// Evaluates one pack for its effects and drops every result.
    Eval {
        /// Pack being evaluated.
        value: PackExpr,
    },
    /// Opens one mutable captured cell.
    OpenCell {
        /// Cell being opened.
        cell: CellId,
        /// Initial cell value.
        value: Expr,
    },
    /// Writes a sequence into a table array part.
    SetList {
        /// Destination table.
        table: Expr,
        /// One-based array index.
        index: u32,
        /// Values being written.
        values: PackExpr,
    },
}

/// Materialized nested control flow.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Region {
    /// Executes statements originating in one FIR block.
    Block {
        /// FIR block that owns the statements.
        origin: usize,
        /// Statements in evaluation order.
        stmts: Vec<Stmt>,
    },
    /// Executes child regions in lexical order.
    Sequence(Vec<Region>),
    /// Selects one of two lexical regions.
    If {
        /// Selection condition.
        condition: Expr,
        /// Region used when the condition succeeds.
        then_branch: Box<Region>,
        /// Region used when the condition fails.
        else_branch: Option<Box<Region>>,
    },
    /// Executes one pre-test loop.
    While {
        /// Loop continuation condition.
        condition: Expr,
        /// Loop body.
        body: Box<Region>,
    },
    /// Executes one post-test loop.
    RepeatUntil {
        /// Loop termination condition.
        condition: Expr,
        /// Loop body.
        body: Box<Region>,
    },
    /// Executes one numeric loop.
    NumericFor {
        /// Loop variable local.
        variable: LocalId,
        /// Initial value.
        start: Expr,
        /// Final value.
        end: Expr,
        /// Step value.
        step: Expr,
        /// Loop body.
        body: Box<Region>,
    },
    /// Executes one generic loop.
    GenericFor {
        /// Loop variable locals.
        variables: SmallVec<[LocalId; 3]>,
        /// Iterator, state, and control values.
        values: [Expr; 3],
        /// Loop body.
        body: Box<Region>,
    },
    /// Starts the next loop iteration.
    Continue,
    /// Leaves the current loop.
    Break,
    /// Returns one value pack.
    Return(PackExpr),
}

impl Region {
    /// Returns whether the region is empty.
    ///
    /// A region is empty if it contains no statements or child regions.
    pub const fn is_empty(&self) -> bool {
        matches!(self, Region::Block { stmts, .. } if stmts.is_empty())
            || matches!(self, Region::Sequence(nodes) if nodes.is_empty())
    }
}

/// One nested function before AST naming and emission.
#[derive(Debug, Clone)]
pub(crate) struct Function {
    /// Bytecode prototype represented by this function.
    pub(crate) id: ProtoId,
    /// Source-representable locals.
    pub(crate) locals: Arena<Local>,
    /// First-class pack locals.
    pub(crate) packs: Arena<PackLocal>,
    /// Formal parameter locals in source order.
    pub(crate) params: Vec<LocalId>,
    /// Whether the function accepts variadic arguments.
    pub(crate) is_vararg: bool,
    /// Upvalue cells in closure capture order.
    pub(crate) upvalues: Vec<CellId>,
    /// Statements that declare storage before control flow starts.
    pub(crate) prologue: Vec<Stmt>,
    /// Nested function body.
    pub(crate) body: Region,
}

/// A visitor that searches for a [`LocalId`].
struct Contains {
    target: LocalId,
    found: bool,
}

impl Visitor for Contains {
    fn visit_capture(&mut self, _: usize, _: Capture) {
        // Captures do not count as contained locals.
    }

    fn visit_expr(&mut self, expr: &Expr) {
        if self.found {
            return;
        }

        walk_expr(self, expr);
    }

    fn visit_pack_expr(&mut self, pack: &PackExpr) {
        if self.found {
            return;
        }

        walk_pack_expr(self, pack);
    }

    fn visit_local(&mut self, id: LocalId) {
        if id == self.target {
            self.found = true;
        }
    }
}
