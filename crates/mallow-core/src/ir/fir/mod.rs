//! Flat intermediate representation used before source structuring.

pub(crate) mod region;

mod cflow;
mod lifter;
mod ssa;

use std::collections::HashSet;
use std::fmt;

use anyhow::{Result, ensure};
use id_arena::{Arena, Id};
pub(crate) use lifter::lift;
use smallvec::{SmallVec, smallvec};
use smol_str::SmolStr;

use crate::common::ByteString;
use crate::il::{ProtoId, ProtoTypeInfo};
use crate::ir::Debug;
use crate::ir::graph::{GraphView, GraphViewMut};
use crate::operator::{BinOp, UnOp};

/// Stable identity for one immutable IR value.
pub type ValueId = Id<Value>;

/// Stable identity for one IR value pack.
pub type PackId = Id<Pack>;

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

/// A numeric literal.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Number {
    /// A 64-bit Luau integer literal.
    Integer(i64),
    /// A floating-point literal.
    Float(f64),
}

impl std::fmt::Display for Number {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Number::Integer(n) => write!(f, "{}i", n),
            Number::Float(n) => write!(f, "{}", n),
        }
    }
}

/// Stable identity for one mutable HIL storage cell.
pub type CellId = Id<Cell>;

/// One mutable storage cell used by closure upvalues.
#[derive(Debug, Clone)]
pub struct Cell {
    /// Bytecode storage that introduced this cell.
    pub origin: CellOrigin,
}

/// The bytecode storage represented by one cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CellOrigin {
    /// One declared upvalue slot in the current function.
    Upvalue(u8),
    /// One generation of an open captured register.
    CapturedRegister { reg: u8, generation: u16 },
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
}

impl Instr {
    /// Returns the value defined by this instruction, if it exists.
    #[inline]
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
            | Self::LoadCell { out, .. } => Some(*out),
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
    #[inline]
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
    #[inline]
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
        }
    }

    /// Returns value packs read by this instruction.
    #[inline]
    fn used_packs(&self) -> SmallVec<[PackId; 3]> {
        match self {
            Self::MakePack { tail, .. } => tail.iter().copied().collect(),
            Self::Project { pack, .. } => smallvec![*pack],
            Self::Call { args, .. } | Self::MethodCall { args, .. } => smallvec![*args],
            Self::SetList { values, .. } => smallvec![*values],
            _ => SmallVec::new(),
        }
    }
}

/// A block in the control flow graph.
#[derive(Debug, Clone)]
pub struct Block {
    /// Values defined when control enters the block, supplied by an incoming [`Edge`].
    pub params: Vec<ValueId>,
    /// Values produced by the bytecode block exit.
    pub outputs: Vec<ValueId>,
    /// Instructions in evaluation order.
    pub instrs: Vec<Instr>,
    /// Control flow leaving this block.
    pub exit: BlockExit,
}

/// An edge between two blocks.
#[derive(Debug, Clone)]
pub struct Edge {
    /// The target block of this edge.
    pub target: usize,
    /// Values bound to the target block's parameters.
    pub params: Vec<ValueId>,
}

impl Edge {
    /// Creates a new edge pointing to a target with no parameters.
    #[inline]
    pub const fn empty(target: usize) -> Self {
        Self {
            target,
            params: Vec::new(),
        }
    }
}

/// An exit from a block.
#[derive(Debug, Clone)]
pub enum BlockExit {
    /// Continues into the next bytecode block.
    Fallthrough(Edge),
    /// Transfers control to one block.
    Jump(Edge),
    /// Transfers control based on a condition value.
    Branch {
        condition: ValueId,
        then_edge: Edge,
        else_edge: Edge,
    },
    /// Starts a numeric loop.
    NumericFor {
        body_edge: Edge,
        exit_edge: Edge,
        variable: ValueId,
        start: ValueId,
        end: ValueId,
        step: ValueId,
    },
    /// Continues a numeric loop.
    NumericForLoop { body_edge: Edge, exit_edge: Edge },
    /// Starts a generic loop.
    GenericFor {
        /// First block in the loop body.
        body_edge: Edge,
        /// Block containing the generic loop operation.
        loop_block: usize, // this is structural metadata, not an actual edge.
        /// Values produced for the source loop variables.
        variables: SmallVec<[ValueId; 3]>,
        /// Iterator, state, and initial control values.
        values: [ValueId; 3],
    },
    /// Continues a generic loop.
    GenericForLoop {
        body_edge: Edge,
        exit_edge: Edge,
        variables: SmallVec<[ValueId; 3]>,
    },
    /// Returns a value pack.
    Return(PackId),
}

impl BlockExit {
    /// Returns immutable values read by this block exit.
    #[inline]
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

    /// Returns outgoing edge references from this block exit.
    #[inline]
    pub(crate) fn edges(&self) -> SmallVec<[&Edge; 2]> {
        match self {
            Self::Fallthrough(edge) | Self::Jump(edge) => smallvec![edge],
            Self::Branch {
                then_edge,
                else_edge,
                ..
            }
            | Self::NumericFor {
                body_edge: then_edge,
                exit_edge: else_edge,
                ..
            }
            | Self::NumericForLoop {
                body_edge: then_edge,
                exit_edge: else_edge,
            }
            | Self::GenericForLoop {
                body_edge: then_edge,
                exit_edge: else_edge,
                ..
            } => smallvec![then_edge, else_edge],
            Self::GenericFor { body_edge, .. } => smallvec![body_edge],
            Self::Return(_) => SmallVec::new(),
        }
    }

    /// Returns outgoing mutable edge references from this block exit.
    #[inline]
    pub(crate) fn edges_mut(&mut self) -> SmallVec<[&mut Edge; 2]> {
        match self {
            Self::Fallthrough(edge) | Self::Jump(edge) => smallvec![edge],
            Self::Branch {
                then_edge,
                else_edge,
                ..
            }
            | Self::NumericFor {
                body_edge: then_edge,
                exit_edge: else_edge,
                ..
            }
            | Self::NumericForLoop {
                body_edge: then_edge,
                exit_edge: else_edge,
            }
            | Self::GenericForLoop {
                body_edge: then_edge,
                exit_edge: else_edge,
                ..
            } => smallvec![then_edge, else_edge],
            Self::GenericFor { body_edge, .. } => smallvec![body_edge],
            Self::Return(_) => SmallVec::new(),
        }
    }

    /// Returns successor blocks referenced by this block exit.
    pub(crate) fn targets(&self) -> SmallVec<[usize; 2]> {
        self.edges().iter().map(|e| e.target).collect()
    }

    /// Returns a formatter for this block exit.
    #[cfg(feature = "visualize")]
    pub(crate) fn display(&self) -> impl fmt::Display + '_ {
        DisplayBlockExit(self)
    }
}

/// A CSR representation of a Control Flow Graph.
#[derive(Debug, Clone)]
pub struct ControlFlowGraph<T> {
    nodes: Box<[T]>,

    // Outgoing edges (successors)
    out_offsets: Box<[usize]>,
    out_edges: Box<[usize]>,

    // Incoming edges (predecessors)
    in_offsets: Box<[usize]>,
    in_edges: Box<[usize]>,
}

impl<T> ControlFlowGraph<T> {
    pub fn from_nodes_and_exits<I, E>(nodes_iter: I) -> Self
    where
        I: IntoIterator<Item = (T, E)>,
        I::IntoIter: ExactSizeIterator,
        E: IntoIterator<Item = usize>,
    {
        let iter = nodes_iter.into_iter();
        let count = iter.len();

        let mut nodes = Vec::with_capacity(count);
        let mut out_offsets = Vec::with_capacity(count + 1);
        out_offsets.push(0);

        let mut out_edges = Vec::new();
        let mut in_degrees = vec![0; count];

        for (payload, exits) in iter {
            nodes.push(payload);
            let edge_start = out_edges.len();
            for target in exits {
                // This duplication check exists because of a true edge case, a Luau optimization miss where
                // the compiler generates a branch with identical exits. Occurs in controlflow35 testcase,
                // tested on releases 0.720 through 0.736 (bytecode v9 - v14) on all optimization levels.
                //
                // FIR out-degree is at most two, so this is effectivelly free (even though it hurts, conceptually.)
                //
                // ```
                // 16:     JUMPXEQKN R0 K8 L3 [100]
                //  2: L3: JUMPBACK L0
                // ```
                //
                // FIR:
                //
                // ```
                // %v22 = eq %v20, %v21
                // branch %v22, bb1, bb1
                // ```
                //
                // R0 is provably numeric here, but if it were an object that carried a metatable with overwritten `__eq`
                // with a side effect, the eval of that expression would have been necessary - that being said, the jump
                // itself is still useless :^)
                if target < count && !out_edges[edge_start..].contains(&target) {
                    out_edges.push(target);
                    in_degrees[target] += 1;
                }
            }
            out_offsets.push(out_edges.len());
        }

        let mut in_offsets = vec![0; count + 1];
        for i in 0..count {
            in_offsets[i + 1] = in_offsets[i] + in_degrees[i];
        }

        let mut in_edges = vec![0; out_edges.len()];
        let mut in_cursor = in_offsets.clone();

        for u in 0..count {
            let start = out_offsets[u];
            let end = out_offsets[u + 1];
            for &v in &out_edges[start..end] {
                in_edges[in_cursor[v]] = u;
                in_cursor[v] += 1;
            }
        }

        Self {
            nodes: nodes.into_boxed_slice(),
            out_offsets: out_offsets.into_boxed_slice(),
            out_edges: out_edges.into_boxed_slice(),
            in_offsets: in_offsets.into_boxed_slice(),
            in_edges: in_edges.into_boxed_slice(),
        }
    }
}

impl<T> GraphView for ControlFlowGraph<T> {
    type Node = usize;
    type Item = T;

    fn entry(&self) -> Self::Node {
        // Control Flow Graphs always start at zero.
        0
    }

    fn get(&self, node: Self::Node) -> Option<&Self::Item> {
        self.nodes.get(node)
    }

    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        let start = self.out_offsets[node];
        let end = self.out_offsets[node + 1];
        self.out_edges[start..end].iter().copied()
    }

    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        let start = self.in_offsets[node];
        let end = self.in_offsets[node + 1];
        self.in_edges[start..end].iter().copied()
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        0..self.nodes.len()
    }

    fn items(&self) -> impl Iterator<Item = &Self::Item> {
        self.nodes.iter()
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }
}

impl<T> GraphViewMut for ControlFlowGraph<T> {
    fn items_mut(&mut self) -> impl Iterator<Item = &mut Self::Item> {
        self.nodes.iter_mut()
    }
}

impl<T> std::ops::Index<usize> for ControlFlowGraph<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.nodes.index(index)
    }
}

impl<T> std::ops::IndexMut<usize> for ControlFlowGraph<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.nodes.index_mut(index)
    }
}

impl<T> std::ops::Index<Edge> for ControlFlowGraph<T> {
    type Output = T;

    fn index(&self, index: Edge) -> &Self::Output {
        self.nodes.index(index.target)
    }
}

/// FIR identities associated with one named bytecode local.
#[derive(Debug, Clone, Default)]
pub struct DebugBinding {
    /// Immutable values held by the local during its lifetime.
    pub values: Vec<ValueId>,
    /// Mutable captured cells held by the local during its lifetime.
    pub cells: Vec<CellId>,
}

/// A lifted function.
#[derive(Debug, Clone)]
pub struct Function {
    /// Bytecode proto represented by this function.
    pub id: ProtoId,
    /// Source information preserved from the bytecode proto.
    pub debug: Debug,
    /// Type info sourced from the bytecode.
    pub type_info: ProtoTypeInfo,
    /// FIR identities associated with each entry in [`Debug::locals`].
    pub bindings: Vec<DebugBinding>,
    /// Parameters in source order.
    pub params: Vec<ValueId>,
    /// The entry edge of this function.
    pub entry: Edge,
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
    /// Control flow graph of this function.
    pub cfg: ControlFlowGraph<Block>,
}

impl Function {
    /// Verifies definitions and the block edges.
    pub fn verify(&self) -> Result<()> {
        ensure!(self.entry.params.len() == self.cfg[self.entry.target].params.len());

        // Each block must have a valid incoming edge from its predecessor, and the arg count
        // must match.
        for block_id in self.cfg.nodes() {
            if self.cfg.is_reachable(block_id) {
                for p in self.cfg.predecessors(block_id) {
                    let edges_from_p = self.cfg[p]
                        .exit
                        .edges()
                        .into_iter()
                        .filter(|e| e.target == block_id);

                    ensure!(
                        edges_from_p.clone().count() > 0,
                        "no edge from predecessor {p} to block {block_id}: {:?}",
                        edges_from_p.collect::<Vec<_>>()
                    );

                    for e in edges_from_p {
                        ensure!(
                            e.params.len() == self.cfg[block_id].params.len(),
                            "param count mismatch between predecessor {p} and block {block_id}: {} edge params, {} block params",
                            e.params.len(),
                            self.cfg[block_id].params.len()
                        );
                    }
                }
            }
        }

        // Each pack and value must be defined before use
        let mut value_defs: HashSet<_> = self.params.iter().copied().collect();
        let mut value_uses = HashSet::new();
        let mut pack_defs = HashSet::new();
        let mut pack_uses = HashSet::new();
        for block in self.cfg.items() {
            value_defs.extend(block.params.iter().copied());
            value_defs.extend(block.outputs.iter().copied());
            for instr in &block.instrs {
                value_uses.extend(instr.used_values());
                pack_uses.extend(instr.used_packs());
                value_defs.extend(instr.defined_value());
                pack_defs.extend(instr.defined_pack());
            }

            value_uses.extend(block.exit.used_values());
            if let BlockExit::Return(pack) = &block.exit {
                pack_uses.insert(*pack);
            }
        }

        for value in value_uses {
            ensure!(
                value_defs.contains(&value),
                "used value %v{} has no definition",
                value.index()
            );
        }
        for pack in pack_uses {
            ensure!(
                pack_defs.contains(&pack),
                "used pack %pack{} has no definition",
                pack.index()
            );
        }
        Ok(())
    }

    /// Returns a formatter for one instruction in this function.
    #[cfg(feature = "visualize")]
    pub(crate) fn display_instr<'a>(&'a self, instr: &'a Instr) -> impl fmt::Display + 'a {
        DisplayInstr(self, instr)
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "func @P{}", self.id.0)?;
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
        for (block_index, block) in self.cfg.enumerate() {
            if block_index > 0 {
                writeln!(f)?;
            }
            write!(f, "bb{}", block_index)?;
            if !block.params.is_empty() {
                write!(f, "({})", Punctuated::new(&block.params, DisplayValue))?;
            }
            writeln!(f, ":")?;
            for instr in &block.instrs {
                writeln!(f, "    {}", DisplayInstr(self, instr))?;
            }
            writeln!(f, "    {}", DisplayBlockExit(&block.exit))?;
        }

        write!(f, "}}")
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
        }
    }
}

struct DisplayEdge<'a>(&'a Edge);

impl fmt::Display for DisplayEdge<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "bb{}", self.0.target)?;
        if !self.0.params.is_empty() {
            write!(
                formatter,
                "({})",
                Punctuated::new(&self.0.params, DisplayValue)
            )?;
        }
        Ok(())
    }
}

struct DisplayBlockExit<'a>(&'a BlockExit);

impl fmt::Display for DisplayBlockExit<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            BlockExit::Fallthrough(edge) => write!(formatter, "fallthrough {}", DisplayEdge(edge)),
            BlockExit::Jump(edge) => write!(formatter, "jump {}", DisplayEdge(edge)),
            BlockExit::Branch {
                condition,
                then_edge,
                else_edge,
            } => write!(
                formatter,
                "branch {}, {}, {}",
                DisplayValue(condition),
                DisplayEdge(then_edge),
                DisplayEdge(else_edge)
            ),
            BlockExit::NumericFor {
                body_edge,
                exit_edge,
                variable,
                start,
                end,
                step,
            } => write!(
                formatter,
                "forn.prep {}, {}, {}, {} -> {}, {}",
                DisplayValue(variable),
                DisplayValue(start),
                DisplayValue(end),
                DisplayValue(step),
                DisplayEdge(body_edge),
                DisplayEdge(exit_edge)
            ),
            BlockExit::NumericForLoop {
                body_edge,
                exit_edge,
            } => write!(
                formatter,
                "forn.loop {}, {}",
                DisplayEdge(body_edge),
                DisplayEdge(exit_edge)
            ),
            BlockExit::GenericFor {
                body_edge,
                loop_block,
                variables,
                values,
            } => write!(
                formatter,
                "forg.prep [{}] in [{}] -> {}, loop bb{loop_block}",
                Punctuated::new(variables, DisplayValue),
                Punctuated::new(values, DisplayValue),
                DisplayEdge(body_edge)
            ),
            BlockExit::GenericForLoop {
                body_edge,
                exit_edge,
                variables,
            } => write!(
                formatter,
                "forg.loop [{}] -> {}, {}",
                Punctuated::new(variables, DisplayValue),
                DisplayEdge(body_edge),
                DisplayEdge(exit_edge)
            ),
            BlockExit::Return(values) => {
                write!(formatter, "return {}", DisplayPack(values))
            }
        }
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
