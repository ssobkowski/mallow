//! Flat intermediate representation used before source structuring.

mod lifter;
pub(crate) mod region;
mod ssa;

use std::collections::HashSet;
use std::fmt;

use anyhow::{Result, ensure};
use id_arena::{Arena, Id};
use smallvec::{SmallVec, smallvec};
use smol_str::SmolStr;

use crate::common::ByteString;
use crate::hil::cflow::graph::build_graph;
use crate::hil::ir::{Cell, CellId, CellOrigin, Number};
use crate::il::ProtoId;
use crate::operator::{BinOp, UnOp};

pub(crate) use lifter::lift;

/// Stable identity for one immutable IR value.
pub type ValueId = Id<Value>;

/// Stable identity for one IR value pack.
pub type PackId = Id<Pack>;

// TODO: Once type inference gets solved, see whether those two structs will hold the types,
//       or the types will be held in the centralized type store and indexed dynamically.
//       If the latter, then remove these structs and arena allocators for them, and use
//       a monotonically increasing counter instead.

/// One immutable IR value identity.
#[derive(Debug, Clone, Default)]
pub struct Value;

/// Metadata for one IR value pack.
#[derive(Debug, Clone, Default)]
pub struct Pack;

/// One literal stored by a constant instruction.
#[derive(Debug, Clone, PartialEq)]
pub enum Constant {
    /// The nil value.
    Nil,
    /// A number value.
    Number(Number),
    /// A byte string value.
    String(ByteString),
    /// A boolean value.
    Bool(bool),
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Number(num) => write!(f, "{}", num),
            Self::String(s) => write!(f, "'{}'", s),
            Self::Bool(b) => write!(f, "{}", b),
        }
    }
}

/// A value or cell captured by one closure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Capture {
    /// Copies an immutable value.
    Copy(ValueId),
    /// Shares a mutable cell.
    Share(CellId),
}

/// An IR instruction.
#[derive(Debug, Clone)]
pub enum Instr {
    /// Binds a constant value to an output.
    Const { out: ValueId, value: Constant },
    /// Creates a new binding to the same value.
    Copy { out: ValueId, value: ValueId },
    /// Creates a closure from a function prototype and captures referenced values.
    Closure {
        out: ValueId,
        proto: ProtoId,
        captures: Vec<Capture>,
    },
    /// Reads a value from a table at the given key and binds it to an output.
    GetTable {
        out: ValueId,
        table: ValueId,
        key: ValueId,
    },
    /// Writes a value to a table at the given key.
    SetTable {
        table: ValueId,
        key: ValueId,
        value: ValueId,
    },
    /// Reads a global variable and binds it to an output.
    GetGlobal { out: ValueId, name: SmolStr },
    /// Writes a value to a global variable.
    SetGlobal { name: SmolStr, value: ValueId },
    /// Applies a binary operation and binds the result to an output.
    Binary {
        out: ValueId,
        lhs: ValueId,
        op: BinOp,
        rhs: ValueId,
    },
    /// Applies a unary operation and binds the result to an output.
    Unary {
        out: ValueId,
        op: UnOp,
        value: ValueId,
    },
    /// Concats a list of values and binds the result to an output.
    Concat {
        out: ValueId,
        operands: SmallVec<[ValueId; 3]>,
    },
    /// Evaluates a condition and binds either `then_value` or `else_value` to an output.
    Select {
        out: ValueId,
        condition: ValueId,
        then_value: ValueId,
        else_value: ValueId,
    },
    /// Creates an empty table and binds it to an output.
    NewTable { out: ValueId },
    /// Groups values into a pack. `head` contains the initial values; `tail` can reference another pack to extend it.
    MakePack {
        out: PackId,
        head: Vec<ValueId>,
        tail: Option<PackId>,
    },
    /// Reads the value at `index` from a pack and binds it to an output.
    Project {
        out: ValueId,
        pack: PackId,
        index: usize,
    },
    /// Calls a function with the given arguments and binds return values to a pack.
    Call {
        out: PackId,
        function: ValueId,
        args: PackId,
    },
    /// Calls a method on an object with the given arguments and binds return values to a pack.
    MethodCall {
        out: PackId,
        object: ValueId,
        method: SmolStr,
        args: PackId,
    },
    /// Reads all variadic arguments passed to the current function into a pack.
    VarArgs { out: PackId },
    /// Initializes a mutable cell with a value.
    OpenCell { cell: CellId, value: ValueId },
    /// Reads the current value from a mutable cell and binds it to an output.
    LoadCell { out: ValueId, cell: CellId },
    /// Writes a value to a mutable cell.
    StoreCell { cell: CellId, value: ValueId },
    /// Writes a sequence of values to a table's array part, starting at `index`.
    SetList {
        table: ValueId,
        index: u32,
        values: PackId,
    },
    /// Selects a value based on which predecessor code path was taken (for control flow merges).
    Phi {
        out: ValueId,
        /// Each pair: (predecessor block index, value from that path).
        inputs: Vec<(usize, ValueId)>,
    },
}

/// An exit from a block.
#[derive(Debug, Clone)]
pub enum BlockExit {
    /// Continues into the next bytecode block.
    Fallthrough(usize),
    /// Transfers control to one block.
    Jump(usize),
    /// Transfers control based on one value.
    Branch {
        condition: ValueId,
        then_block: usize,
        else_block: usize,
    },
    /// Starts a numeric loop.
    NumericFor {
        body_block: usize,
        exit_block: usize,
        variable: ValueId,
        start: ValueId,
        end: ValueId,
        step: ValueId,
    },
    /// Continues a numeric loop.
    NumericForLoop {
        body_block: usize,
        exit_block: usize,
    },
    /// Starts a generic loop.
    GenericFor {
        /// First block in the loop body.
        body_block: usize,
        /// Block containing the generic loop operation.
        loop_block: usize,
        /// Values produced for the source loop variables.
        variables: SmallVec<[ValueId; 3]>,
        /// Iterator, state, and initial control values.
        values: [ValueId; 3],
    },
    /// Continues a generic loop.
    GenericForLoop {
        body_block: usize,
        exit_block: usize,
        variables: SmallVec<[ValueId; 3]>,
    },
    /// Returns a value pack.
    Return(PackId),
}

/// A block in the control flow graph.
#[derive(Debug, Clone)]
pub struct Block {
    /// Values produced by the bytecode block exit.
    pub outputs: Vec<ValueId>,
    /// Instructions in evaluation order.
    pub instrs: Vec<Instr>,
    /// Control flow leaving this block.
    pub exit: BlockExit,
}

/// A lifted function.
#[derive(Debug, Clone)]
pub struct Function {
    /// Bytecode proto represented by this function.
    pub proto: ProtoId,
    /// Formal parameter values in source order.
    pub params: Vec<ValueId>,
    /// Whether the function accepts variadic arguments.
    pub is_vararg: bool,
    /// Declared upvalue cells in slot order.
    pub upvalues: Vec<CellId>,
    /// Immutable values owned by this function.
    pub values: Arena<Value>,
    /// Value packs owned by this function.
    pub packs: Arena<Pack>,
    /// Mutable cells owned by this function.
    pub cells: Arena<Cell>,
    /// Basic blocks in bytecode order.
    pub blocks: Vec<Block>,
}

impl Function {
    /// Verifies identity, definition, and reference invariants.
    pub fn verify(&self) -> Result<()> {
        let mut value_defs = HashSet::new();
        let mut value_uses = HashSet::new();
        let mut pack_defs = HashSet::new();
        let (_, predecessors) = build_graph(self.blocks.iter().map(|block| block.exit.targets()));

        for &parameter in &self.params {
            ensure!(
                value_defs.insert(parameter),
                "value %v{} is defined twice",
                parameter.index()
            );
        }

        for (block_index, block) in self.blocks.iter().enumerate() {
            for &output in &block.outputs {
                ensure!(
                    value_defs.insert(output),
                    "value %v{} is defined twice",
                    output.index()
                );
            }
            for instr in &block.instrs {
                for value in instr.used_values() {
                    ensure!(
                        self.values.get(value).is_some(),
                        "instruction in bb{block_index} uses invalid value %v{}",
                        value.index()
                    );
                    value_uses.insert(value);
                }
                for pack in instr.used_packs() {
                    ensure!(
                        self.packs.get(pack).is_some(),
                        "instruction in bb{block_index} uses invalid pack %pack{}",
                        pack.index()
                    );
                }
                if let Some(value) = instr.defined_value() {
                    ensure!(
                        value_defs.insert(value),
                        "value %v{} is defined twice",
                        value.index()
                    );
                }
                if let Some(pack) = instr.defined_pack() {
                    ensure!(
                        pack_defs.insert(pack),
                        "pack %pack{} is defined twice",
                        pack.index()
                    );
                }
                if let Instr::Phi { inputs, .. } = instr {
                    let mut input_predecessors = HashSet::new();
                    for &(predecessor, _) in inputs {
                        ensure!(
                            predecessor < self.blocks.len(),
                            "phi in bb{block_index} references invalid predecessor bb{predecessor}"
                        );
                        ensure!(
                            input_predecessors.insert(predecessor),
                            "phi in bb{block_index} lists predecessor bb{predecessor} twice"
                        );
                    }
                    let actual_predecessors: HashSet<_> =
                        predecessors[block_index].iter().copied().collect();
                    ensure!(
                        input_predecessors == actual_predecessors,
                        "phi in bb{block_index} does not describe every predecessor"
                    );
                }
                for cell in instr.cells() {
                    ensure!(
                        self.cells.get(cell).is_some(),
                        "instruction in bb{block_index} uses invalid cell ${}",
                        cell.index()
                    );
                }
            }

            for value in block.exit.used_values() {
                ensure!(
                    self.values.get(value).is_some(),
                    "block exit in bb{block_index} uses invalid value %v{}",
                    value.index()
                );
                value_uses.insert(value);
            }
            for pack in block.exit.used_packs() {
                ensure!(
                    self.packs.get(pack).is_some(),
                    "block exit in bb{block_index} uses invalid pack %pack{}",
                    pack.index()
                );
            }
            for target in block.exit.targets() {
                ensure!(
                    target < self.blocks.len(),
                    "block exit in bb{block_index} targets invalid bb{target}"
                );
            }
        }

        for value in value_uses {
            ensure!(
                value_defs.contains(&value),
                "used value %v{} has no definition",
                value.index()
            );
        }
        for (pack, _) in &self.packs {
            ensure!(
                pack_defs.contains(&pack),
                "pack %pack{} has no definition",
                pack.index()
            );
        }
        Ok(())
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "func @P{}", self.proto.0)?;
        if !self.params.is_empty() {
            write!(
                f,
                " params({})",
                Punctuated::new(&self.params, DisplayValue)
            )?;
        }
        if !self.upvalues.is_empty() {
            write!(
                f,
                " upvalues({})",
                Punctuated::new(&self.upvalues, |id| DisplayCell(self, id))
            )?;
        }

        writeln!(f, " {{")?;
        for (block_index, block) in self.blocks.iter().enumerate() {
            if block_index > 0 {
                writeln!(f)?;
            }
            writeln!(f, "bb{}:", block_index)?;
            for instr in &block.instrs {
                writeln!(f, "    {}", DisplayInstr(self, instr))?;
            }
            writeln!(f, "    {}", DisplayBlockExit(&block.exit))?;
        }

        write!(f, "}}")
    }
}

struct DisplayValue<'a>(&'a ValueId);

impl fmt::Display for DisplayValue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%v{}", self.0.index())
    }
}

struct DisplayPack<'a>(&'a PackId);

impl fmt::Display for DisplayPack<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%q{}", self.0.index())
    }
}

struct DisplayCell<'a>(&'a Function, &'a CellId);

impl fmt::Display for DisplayCell<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.cells[*self.1].origin {
            CellOrigin::Upvalue(x) => write!(f, "$u{}", x),
            CellOrigin::CapturedRegister { .. } => write!(f, "$c{}", self.1.index()),
        }
    }
}

struct DisplayCapture<'a>(&'a Function, &'a Capture);

impl fmt::Display for DisplayCapture<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1 {
            Capture::Copy(value) => write!(f, "copy {}", DisplayValue(value)),
            Capture::Share(cell) => write!(f, "ref {}", DisplayCell(self.0, cell)),
        }
    }
}

struct DisplayInstr<'a>(&'a Function, &'a Instr);

impl fmt::Display for DisplayInstr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1 {
            Instr::Const { out, value } => {
                write!(f, "{} = const {}", DisplayValue(out), value)
            }
            Instr::Copy { out, value } => {
                write!(f, "{} = copy {}", DisplayValue(out), DisplayValue(value))
            }

            Instr::Closure {
                out,
                proto,
                captures,
            } => {
                write!(
                    f,
                    "{} = closure @P{} [{}]",
                    DisplayValue(out),
                    proto.0,
                    Punctuated::new(captures, |cap| DisplayCapture(self.0, cap))
                )
            }
            Instr::GetTable { out, table, key } => {
                write!(
                    f,
                    "{} = index.get {}, {}",
                    DisplayValue(out),
                    DisplayValue(table),
                    DisplayValue(key)
                )
            }
            Instr::SetTable { table, key, value } => {
                write!(
                    f,
                    "index.set {}, {}, {}",
                    DisplayValue(table),
                    DisplayValue(key),
                    DisplayValue(value)
                )
            }
            Instr::GetGlobal { out, name } => {
                write!(f, "{} = global.get '{}'", DisplayValue(out), name)
            }
            Instr::SetGlobal { name, value } => {
                write!(f, "global.set '{}' {}", name, DisplayValue(value))
            }
            Instr::Binary { out, lhs, op, rhs } => {
                write!(
                    f,
                    "{} = {} {}, {}",
                    DisplayValue(out),
                    DisplayBinOp(*op),
                    DisplayValue(lhs),
                    DisplayValue(rhs)
                )
            }
            Instr::Unary { out, op, value } => {
                write!(
                    f,
                    "{} = {} {}",
                    DisplayValue(out),
                    DisplayUnOp(*op),
                    DisplayValue(value)
                )
            }
            Instr::Concat { out, operands } => {
                write!(
                    f,
                    "{} = concat [{}]",
                    DisplayValue(out),
                    Punctuated::new(operands, DisplayValue)
                )
            }
            Instr::Select {
                out,
                condition,
                then_value,
                else_value,
            } => {
                write!(
                    f,
                    "{} = select {}, {}, {}",
                    DisplayValue(out),
                    DisplayValue(condition),
                    DisplayValue(then_value),
                    DisplayValue(else_value)
                )
            }
            Instr::NewTable { out } => {
                write!(f, "{} = table", DisplayValue(out))
            }
            Instr::MakePack { out, head, tail } => {
                write!(
                    f,
                    "{} = pack [{}",
                    DisplayPack(out),
                    Punctuated::new(head, DisplayValue)
                )?;
                if let Some(tail) = tail {
                    write!(f, "; {}", DisplayPack(tail))?;
                }
                write!(f, "]")
            }
            Instr::Project { out, pack, index } => {
                write!(
                    f,
                    "{} = project {}, {}",
                    DisplayValue(out),
                    DisplayPack(pack),
                    index
                )
            }
            Instr::Call {
                out,
                function,
                args,
            } => {
                write!(
                    f,
                    "{} = call {}({})",
                    DisplayPack(out),
                    DisplayValue(function),
                    DisplayPack(args)
                )
            }
            Instr::MethodCall {
                out,
                object,
                method,
                args,
            } => {
                write!(
                    f,
                    "{} = methodcall ({}, '{}')({})",
                    DisplayPack(out),
                    DisplayValue(object),
                    method,
                    DisplayPack(args)
                )
            }
            Instr::VarArgs { out } => write!(f, "{} = %va", DisplayPack(out)),
            Instr::OpenCell { cell, value } => write!(
                f,
                "{} = cell {}",
                DisplayCell(self.0, cell),
                DisplayValue(value)
            ),
            Instr::LoadCell { out, cell } => {
                write!(
                    f,
                    "{} = load {}",
                    DisplayValue(out),
                    DisplayCell(self.0, cell)
                )
            }
            Instr::StoreCell { cell, value } => {
                write!(
                    f,
                    "store {}, {}",
                    DisplayCell(self.0, cell),
                    DisplayValue(value)
                )
            }
            Instr::SetList {
                table,
                index,
                values,
            } => {
                write!(
                    f,
                    "setlist {}, {}, {}",
                    DisplayValue(table),
                    index,
                    DisplayPack(values)
                )
            }
            Instr::Phi { out, inputs } => {
                write!(
                    f,
                    "{} = phi [{}]",
                    DisplayValue(out),
                    Punctuated::new(inputs, PhiInput)
                )
            }
        }
    }
}

struct DisplayBlockExit<'a>(&'a BlockExit);

impl fmt::Display for DisplayBlockExit<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            BlockExit::Fallthrough(target) => write!(formatter, "fallthrough bb{target}"),
            BlockExit::Jump(target) => write!(formatter, "jump bb{target}"),
            BlockExit::Branch {
                condition,
                then_block,
                else_block,
            } => write!(
                formatter,
                "branch {}, bb{then_block}, bb{else_block}",
                DisplayValue(condition)
            ),
            BlockExit::NumericFor {
                body_block,
                exit_block,
                variable,
                start,
                end,
                step,
            } => write!(
                formatter,
                "forn.prep {}, {}, {}, {} -> bb{body_block}, bb{exit_block}",
                DisplayValue(variable),
                DisplayValue(start),
                DisplayValue(end),
                DisplayValue(step)
            ),
            BlockExit::NumericForLoop {
                body_block,
                exit_block,
            } => write!(formatter, "forn.loop bb{body_block}, bb{exit_block}"),
            BlockExit::GenericFor {
                body_block,
                loop_block,
                variables,
                values,
            } => write!(
                formatter,
                "forg.prep [{}] in [{}] -> bb{body_block}, loop bb{loop_block}",
                Punctuated::new(variables, DisplayValue),
                Punctuated::new(values, DisplayValue)
            ),
            BlockExit::GenericForLoop {
                body_block,
                exit_block,
                variables,
            } => write!(
                formatter,
                "forg.loop [{}] -> bb{body_block}, bb{exit_block}",
                Punctuated::new(variables, DisplayValue)
            ),
            BlockExit::Return(values) => {
                write!(formatter, "return {}", DisplayPack(values))
            }
        }
    }
}

struct PhiInput<'a>(&'a (usize, ValueId));

impl fmt::Display for PhiInput<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "bb{}: {}", self.0.0, DisplayValue(&self.0.1))
    }
}

struct DisplayBinOp(BinOp);

impl fmt::Display for DisplayBinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinOp::Add => write!(f, "add"),
            BinOp::Sub => write!(f, "sub"),
            BinOp::Mul => write!(f, "mul"),
            BinOp::Div => write!(f, "div"),
            BinOp::IDiv => write!(f, "idiv"),
            BinOp::Mod => write!(f, "mod"),
            BinOp::Pow => write!(f, "pow"),
            BinOp::Eq => write!(f, "eq"),
            BinOp::Ne => write!(f, "ne"),
            BinOp::Lt => write!(f, "lt"),
            BinOp::Lte => write!(f, "lte"),
            BinOp::Gt => write!(f, "gt"),
            BinOp::Gte => write!(f, "gte"),
            BinOp::And => write!(f, "and"),
            BinOp::Or => write!(f, "or"),
            BinOp::Concat => write!(f, "concat"),
        }
    }
}

struct DisplayUnOp(UnOp);

impl fmt::Display for DisplayUnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnOp::Minus => write!(f, "neg"),
            UnOp::Not => write!(f, "not"),
            UnOp::Length => write!(f, "len"),
        }
    }
}

impl Instr {
    /// Returns the value defined by this instruction, if it exists.
    pub(crate) fn defined_value(&self) -> Option<ValueId> {
        match self {
            Self::Const { out, .. }
            | Self::Copy { out, .. }
            | Self::GetGlobal { out, .. }
            | Self::Closure { out, .. }
            | Self::GetTable { out, .. }
            | Self::Binary { out, .. }
            | Self::Unary { out, .. }
            | Self::Concat { out, .. }
            | Self::Select { out, .. }
            | Self::NewTable { out }
            | Self::Project { out, .. }
            | Self::LoadCell { out, .. }
            | Self::Phi { out, .. } => Some(*out),
            Self::SetTable { .. }
            | Self::SetGlobal { .. }
            | Self::MakePack { .. }
            | Self::Call { .. }
            | Self::MethodCall { .. }
            | Self::VarArgs { .. }
            | Self::OpenCell { .. }
            | Self::StoreCell { .. }
            | Self::SetList { .. } => None,
        }
    }

    /// Returns the value pack defined by this instruction, if it exists.
    fn defined_pack(&self) -> Option<PackId> {
        match self {
            Self::MakePack { out, .. }
            | Self::Call { out, .. }
            | Self::MethodCall { out, .. }
            | Self::VarArgs { out } => Some(*out),
            _ => None,
        }
    }

    /// Returns immutable values read by this instruction.
    pub(crate) fn used_values(&self) -> SmallVec<[ValueId; 3]> {
        match self {
            Self::Const { .. }
            | Self::GetGlobal { .. }
            | Self::NewTable { .. }
            | Self::VarArgs { .. }
            | Self::LoadCell { .. } => SmallVec::new(),
            Self::Copy { value, .. }
            | Self::SetGlobal { value, .. }
            | Self::Unary { value, .. }
            | Self::OpenCell { value, .. }
            | Self::StoreCell { value, .. } => smallvec![*value],
            Self::Closure { captures, .. } => captures
                .iter()
                .filter_map(|capture| match capture {
                    Capture::Copy(value) => Some(*value),
                    Capture::Share(_) => None,
                })
                .collect(),
            Self::GetTable { table, key, .. } => smallvec![*table, *key],
            Self::SetTable { table, key, value } => smallvec![*table, *key, *value],
            Self::Binary { lhs, rhs, .. } => smallvec![*lhs, *rhs],
            Self::Concat { operands, .. } => operands.clone(),
            Self::Select {
                condition,
                then_value,
                else_value,
                ..
            } => smallvec![*condition, *then_value, *else_value],
            Self::MakePack { head, .. } => head.iter().copied().collect(),
            Self::Project { .. } => SmallVec::new(),
            Self::Call { function, .. } => smallvec![*function],
            Self::MethodCall { object, .. } => smallvec![*object],
            Self::SetList { table, .. } => smallvec![*table],
            Self::Phi { inputs, .. } => inputs.iter().map(|(_, value)| *value).collect(),
        }
    }

    /// Returns value packs read by this instruction.
    fn used_packs(&self) -> SmallVec<[PackId; 3]> {
        match self {
            Self::MakePack { tail, .. } => tail.iter().copied().collect(),
            Self::Project { pack, .. } => smallvec![*pack],
            Self::Call { args, .. } | Self::MethodCall { args, .. } => smallvec![*args],
            Self::SetList { values, .. } => smallvec![*values],
            _ => SmallVec::new(),
        }
    }

    /// Returns mutable cells referenced by this instruction.
    fn cells(&self) -> SmallVec<[CellId; 3]> {
        match self {
            Self::Closure { captures, .. } => captures
                .iter()
                .filter_map(|capture| match capture {
                    Capture::Copy(_) => None,
                    Capture::Share(cell) => Some(*cell),
                })
                .collect(),
            Self::OpenCell { cell, .. }
            | Self::LoadCell { cell, .. }
            | Self::StoreCell { cell, .. } => smallvec![*cell],
            _ => SmallVec::new(),
        }
    }
}

impl BlockExit {
    /// Returns immutable values read by this block exit.
    fn used_values(&self) -> SmallVec<[ValueId; 3]> {
        match self {
            Self::Fallthrough(_)
            | Self::Jump(_)
            | Self::NumericForLoop { .. }
            | Self::Return(_) => SmallVec::new(),
            Self::Branch { condition, .. } => smallvec![*condition],
            Self::NumericFor {
                start, end, step, ..
            } => smallvec![*start, *end, *step],
            Self::GenericFor { values, .. } => SmallVec::from_slice(values),
            Self::GenericForLoop { .. } => SmallVec::new(),
        }
    }

    /// Returns value packs read by this block exit.
    fn used_packs(&self) -> SmallVec<[PackId; 3]> {
        match self {
            Self::Return(pack) => smallvec![*pack],
            _ => SmallVec::new(),
        }
    }

    /// Returns successor blocks referenced by this block exit.
    pub(crate) fn targets(&self) -> SmallVec<[usize; 3]> {
        match self {
            Self::Fallthrough(target) | Self::Jump(target) => smallvec![*target],
            Self::Branch {
                then_block,
                else_block,
                ..
            }
            | Self::NumericFor {
                body_block: then_block,
                exit_block: else_block,
                ..
            }
            | Self::NumericForLoop {
                body_block: then_block,
                exit_block: else_block,
            }
            | Self::GenericForLoop {
                body_block: then_block,
                exit_block: else_block,
                ..
            } => smallvec![*then_block, *else_block],
            Self::GenericFor { body_block, .. } => smallvec![*body_block],
            Self::Return(_) => SmallVec::new(),
        }
    }
}

struct Punctuated<'a, C: ?Sized, F> {
    values: &'a C,
    display: F,
}

impl<'a, C, F, D> Punctuated<'a, C, F>
where
    C: ?Sized,
    &'a C: IntoIterator,
    F: Fn(<&'a C as IntoIterator>::Item) -> D,
    D: fmt::Display,
{
    fn new(values: &'a C, display: F) -> Self {
        Self { values, display }
    }
}

impl<'a, C, F, D> fmt::Display for Punctuated<'a, C, F>
where
    &'a C: IntoIterator,
    F: Fn(<&'a C as IntoIterator>::Item) -> D,
    D: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut iter = self.values.into_iter();
        if let Some(first) = iter.next() {
            write!(f, "{}", (self.display)(first))?;
            for value in iter {
                write!(f, ", {}", (self.display)(value))?;
            }
        }
        Ok(())
    }
}
