//! Nested intermediate representation used after control-flow recognition.

use id_arena::{Arena, Id};
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::hil::ir::CellId;
use crate::il::ProtoId;
use crate::ir::{Constant, PackId, ValueId};
use crate::operator::{BinOp, UnOp};

/// Stable identity for one source-representable local.
pub(crate) type LocalId = Id<Local>;

/// Stable identity for one materialized value pack.
pub(crate) type PackLocalId = Id<PackLocal>;

/// One source-representable local with FIR provenance.
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

/// Location of one instruction in the FIR function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct InstrOrigin {
    /// Block that contains the instruction.
    pub(crate) block: usize,
    /// Instruction index inside the block.
    pub(crate) instr: usize,
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
pub(crate) struct Expr {
    /// FIR instruction represented by this expression node.
    pub(crate) origin: Option<InstrOrigin>,
    /// Semantic expression operation.
    pub(crate) kind: ExprKind,
}

impl Expr {
    /// Creates a local reference with no instruction provenance.
    #[inline]
    #[must_use]
    fn local(local: LocalId) -> Self {
        Self {
            origin: None,
            kind: ExprKind::Local(local),
        }
    }

    /// Creates a literal boolean with no instruction provenance.
    #[inline]
    #[must_use]
    fn boolean(value: bool) -> Self {
        Self {
            origin: None,
            kind: ExprKind::Constant(Constant::Bool(value)),
        }
    }

    /// Creates a nil value with no instruction provenance.
    fn nil() -> Self {
        Self {
            origin: None,
            kind: ExprKind::Constant(Constant::Nil),
        }
    }

    /// Creates one expression produced by a FIR instruction.
    #[inline]
    #[must_use]
    fn produced(origin: InstrOrigin, kind: ExprKind) -> Self {
        Self {
            origin: Some(origin),
            kind,
        }
    }
}

/// Semantic operation of one nested expression.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ExprKind {
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
    /// Creates a new table.
    NewTable,
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

/// One nested value-pack expression.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct PackExpr {
    /// FIR instruction represented by this pack node.
    pub(crate) origin: Option<InstrOrigin>,
    /// Semantic pack operation.
    pub(crate) kind: PackExprKind,
}

impl PackExpr {
    /// Creates a pack-local reference with no instruction provenance.
    #[inline]
    #[must_use]
    fn local(local: PackLocalId) -> Self {
        Self {
            origin: None,
            kind: PackExprKind::Local(local),
        }
    }

    /// Creates one pack produced by a FIR instruction.
    #[inline]
    #[must_use]
    fn produced(origin: InstrOrigin, kind: PackExprKind) -> Self {
        Self {
            origin: Some(origin),
            kind,
        }
    }
}

/// Semantic operation of one nested pack expression.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PackExprKind {
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
}

/// One materialized NIR statement.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Stmt {
    /// Binds one immutable local value.
    Let {
        /// Local being introduced.
        local: LocalId,
        /// Value assigned to the local.
        value: Expr,
    },
    /// Binds one immutable pack.
    LetPack {
        /// Pack local being introduced.
        local: PackLocalId,
        /// Pack assigned to the local.
        value: PackExpr,
    },
    /// Writes one place.
    Assign {
        /// FIR effect represented by this statement, when one exists.
        origin: Option<InstrOrigin>,
        /// Destination place.
        target: Place,
        /// Assigned value.
        value: Expr,
    },
    /// Opens one mutable captured cell.
    OpenCell {
        /// FIR effect represented by this statement.
        origin: InstrOrigin,
        /// Cell being opened.
        cell: CellId,
        /// Initial cell value.
        value: Expr,
    },
    /// Writes a sequence into a table array part.
    SetList {
        /// FIR effect represented by this statement.
        origin: InstrOrigin,
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

/// One nested function before AST naming and emission.
#[derive(Debug, Clone)]
pub(crate) struct Function {
    /// Source-representable locals.
    pub(crate) locals: Arena<Local>,
    /// First-class pack locals.
    pub(crate) packs: Arena<PackLocal>,
    /// Formal parameter locals in source order.
    pub(crate) params: Vec<LocalId>,
    /// Statements that declare storage before control flow starts.
    pub(crate) prologue: Vec<Stmt>,
    /// Nested function body.
    pub(crate) body: Region,
}

mod inline;
pub(crate) mod materialize;
mod verify;

#[cfg(test)]
mod tests {
    use id_arena::Arena;

    use super::*;
    use crate::hil::ir::Cell;
    use crate::ir::{self, Block, Pack, Value};
    use crate::logging::Diagnostics;

    /// Builds an acyclic branch whose condition has one concrete definition.
    fn branch_function() -> ir::Function {
        let mut values = Arena::new();
        let lhs = values.alloc(Value);
        let rhs = values.alloc(Value);
        let condition = values.alloc(Value);
        let mut packs = Arena::new();
        let then_pack = packs.alloc(Pack);
        let else_pack = packs.alloc(Pack);

        ir::Function {
            proto: ProtoId(0),
            params: vec![lhs, rhs],
            upvalues: Vec::new(),
            values,
            packs,
            cells: Arena::<Cell>::new(),
            blocks: vec![
                Block {
                    outputs: Vec::new(),
                    instrs: vec![ir::Instr::Binary {
                        out: condition,
                        lhs,
                        op: BinOp::Lt,
                        rhs,
                    }],
                    exit: ir::BlockExit::Branch {
                        condition,
                        then_block: 1,
                        else_block: 2,
                    },
                },
                Block {
                    outputs: Vec::new(),
                    instrs: vec![ir::Instr::MakePack {
                        out: then_pack,
                        head: Vec::new(),
                        tail: None,
                    }],
                    exit: ir::BlockExit::Return(then_pack),
                },
                Block {
                    outputs: Vec::new(),
                    instrs: vec![ir::Instr::MakePack {
                        out: else_pack,
                        head: Vec::new(),
                        tail: None,
                    }],
                    exit: ir::BlockExit::Return(else_pack),
                },
            ],
        }
    }

    /// Materializes and concretely inlines an adjacent branch condition.
    #[test]
    fn materializes_condition_without_virtual_ownership() {
        let fir = branch_function();
        fir.verify().unwrap();
        let function = materialize::lower(&fir, &Diagnostics::default()).unwrap();
        function.verify(&fir).unwrap();

        let Region::Sequence(nodes) = &function.body else {
            panic!("root must be a sequence");
        };
        let Region::Block { stmts, .. } = &nodes[0] else {
            panic!("condition source must remain a concrete block");
        };
        assert!(stmts.is_empty());
        assert!(matches!(
            &nodes[1],
            Region::If {
                condition: Expr {
                    origin: Some(InstrOrigin { block: 0, instr: 0 }),
                    kind: ExprKind::Binary { op: BinOp::Lt, .. },
                },
                ..
            }
        ));
    }

    /// Builds a diamond with one value Phi at its merge block.
    fn phi_function() -> ir::Function {
        let mut values = Arena::new();
        let lhs = values.alloc(Value);
        let rhs = values.alloc(Value);
        let condition = values.alloc(Value);
        let then_value = values.alloc(Value);
        let else_value = values.alloc(Value);
        let merged = values.alloc(Value);
        let mut packs = Arena::new();
        let result = packs.alloc(Pack);

        ir::Function {
            proto: ProtoId(0),
            params: vec![lhs, rhs],
            upvalues: Vec::new(),
            values,
            packs,
            cells: Arena::<Cell>::new(),
            blocks: vec![
                Block {
                    outputs: Vec::new(),
                    instrs: vec![ir::Instr::Binary {
                        out: condition,
                        lhs,
                        op: BinOp::Lt,
                        rhs,
                    }],
                    exit: ir::BlockExit::Branch {
                        condition,
                        then_block: 1,
                        else_block: 2,
                    },
                },
                Block {
                    outputs: Vec::new(),
                    instrs: vec![ir::Instr::Copy {
                        out: then_value,
                        value: lhs,
                    }],
                    exit: ir::BlockExit::Jump(3),
                },
                Block {
                    outputs: Vec::new(),
                    instrs: vec![ir::Instr::Copy {
                        out: else_value,
                        value: rhs,
                    }],
                    exit: ir::BlockExit::Jump(3),
                },
                Block {
                    outputs: Vec::new(),
                    instrs: vec![
                        ir::Instr::Phi {
                            out: merged,
                            inputs: vec![(1, then_value), (2, else_value)],
                        },
                        ir::Instr::MakePack {
                            out: result,
                            head: vec![merged],
                            tail: None,
                        },
                    ],
                    exit: ir::BlockExit::Return(result),
                },
            ],
        }
    }

    /// Lowers a Phi into shared storage writes and removes the Phi owner.
    #[test]
    fn materializes_phi_as_shared_storage() {
        let fir = phi_function();
        fir.verify().unwrap();
        let function = materialize::lower(&fir, &Diagnostics::default()).unwrap();
        function.verify(&fir).unwrap();

        assert!(function.prologue.is_empty());
        let Region::Sequence(nodes) = &function.body else {
            panic!("root must be a sequence");
        };
        let Region::Block { stmts, .. } = &nodes[0] else {
            panic!("entry must remain a block");
        };
        assert!(matches!(stmts.first(), Some(Stmt::Let { .. })));
        let Region::If {
            then_branch,
            else_branch: Some(else_branch),
            ..
        } = &nodes[1]
        else {
            panic!("merge must be represented as an if");
        };
        for branch in [then_branch.as_ref(), else_branch.as_ref()] {
            let Region::Block { stmts, .. } = branch else {
                panic!("branch must remain a block");
            };
            assert!(matches!(
                stmts.as_slice(),
                [Stmt::Assign {
                    target: Place::Local(_),
                    ..
                }]
            ));
        }
    }
}
