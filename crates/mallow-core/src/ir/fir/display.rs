//! Text rendering of the flat intermediate representation.

use std::fmt;

use super::{
    BlockExit, Capture, CellId, CellOrigin, Constant, Edge, Function, Instr, PackId, ValueId,
};
use crate::ir::graph::GraphView;
use crate::operator::{BinOp, UnOp};
use crate::style::{Style, StyledWrite, write_styled};

impl Function {
    /// Writes this function as IR text, tagging each piece with a [`Style`].
    pub fn write<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        let mut out = IrWriter { function: self, w };
        out.function()
    }

    /// Returns a formatter for a instruction in this function.
    #[cfg(feature = "visualize")]
    pub(crate) fn display_instr<'a>(&'a self, instr: &'a Instr) -> impl fmt::Display + 'a {
        DisplayInstr {
            function: self,
            instr,
        }
    }

    /// Returns a formatter for a block exit in this function.
    #[cfg(feature = "visualize")]
    pub(crate) fn display_exit<'a>(&'a self, exit: &'a BlockExit) -> impl fmt::Display + 'a {
        DisplayExit {
            function: self,
            exit,
        }
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write(f)
    }
}

/// Displays a instruction, dropping its styles.
#[cfg(feature = "visualize")]
struct DisplayInstr<'a> {
    function: &'a Function,
    instr: &'a Instr,
}

#[cfg(feature = "visualize")]
impl fmt::Display for DisplayInstr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        IrWriter {
            function: self.function,
            w: f,
        }
        .instr(self.instr)
    }
}

/// Displays a block exit, dropping its styles.
#[cfg(feature = "visualize")]
struct DisplayExit<'a> {
    function: &'a Function,
    exit: &'a BlockExit,
}

#[cfg(feature = "visualize")]
impl fmt::Display for DisplayExit<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        IrWriter {
            function: self.function,
            w: f,
        }
        .exit(self.exit)
    }
}

/// Writes the IR of a function to a styled sink.
struct IrWriter<'a, 'w, W: StyledWrite> {
    function: &'a Function,
    w: &'w mut W,
}

impl<W: StyledWrite> IrWriter<'_, '_, W> {
    fn function(&mut self) -> fmt::Result {
        let function = self.function;
        write_styled!(self.w, Style::Heading, "func")?;
        self.w.write_str(" ")?;
        write_styled!(self.w, Style::Name, "@P{}", function.id.0)?;
        if !function.params.is_empty() {
            self.w.write_str(" ")?;
            write_styled!(self.w, Style::Heading, "params")?;
            self.w.write_str("(")?;
            self.punctuated(&function.params, Self::value)?;
            self.w.write_str(")")?;
        }
        if !function.upvalues.is_empty() {
            self.w.write_str(" ")?;
            write_styled!(self.w, Style::Heading, "upvalues")?;
            self.w.write_str("(")?;
            self.punctuated(&function.upvalues, Self::cell)?;
            self.w.write_str(")")?;
        }

        self.w.write_str(" {\n")?;
        for (block_index, block) in function.cfg.enumerate() {
            if block_index > 0 {
                self.w.write_str("\n")?;
            }
            self.block(block_index)?;
            if !block.params.is_empty() {
                self.w.write_str("(")?;
                self.punctuated(&block.params, Self::value)?;
                self.w.write_str(")")?;
            }
            self.w.write_str(":\n")?;
            for instr in &block.instrs {
                self.w.write_str("    ")?;
                self.instr(instr)?;
                self.w.write_str("\n")?;
            }
            self.w.write_str("    ")?;
            self.exit(&block.exit)?;
            self.w.write_str("\n")?;
        }

        self.w.write_str("}")
    }

    fn instr(&mut self, instr: &Instr) -> fmt::Result {
        match instr {
            Instr::Const { out, value } => {
                self.def(out, "const")?;
                self.w.write_str(" ")?;
                self.constant(value)
            }
            Instr::Copy { out, value } => {
                self.def(out, "copy")?;
                self.w.write_str(" ")?;
                self.value(value)
            }
            Instr::Closure {
                out,
                proto,
                captures,
            } => {
                self.def(out, "closure")?;
                self.w.write_str(" ")?;
                write_styled!(self.w, Style::Name, "@P{}", proto.0)?;
                self.w.write_str(" [")?;
                self.punctuated(captures, Self::capture)?;
                self.w.write_str("]")
            }
            Instr::GetTable { out, table, key } => {
                self.def(out, "table.get")?;
                self.w.write_str(" ")?;
                self.values(&[table, key])
            }
            Instr::SetTable { table, key, value } => {
                self.op("table.set")?;
                self.w.write_str(" ")?;
                self.values(&[table, key, value])
            }
            Instr::GetGlobal { out, name } => {
                self.def(out, "global.get")?;
                self.w.write_str(" ")?;
                self.name(name)
            }
            Instr::SetGlobal { name, value } => {
                self.op("global.set")?;
                self.w.write_str(" ")?;
                self.name(name)?;
                self.w.write_str(" ")?;
                self.value(value)
            }
            Instr::Binary { out, lhs, op, rhs } => {
                self.def(out, bin_op_name(*op))?;
                self.w.write_str(" ")?;
                self.values(&[lhs, rhs])
            }
            Instr::Unary { out, op, value } => {
                self.def(out, un_op_name(*op))?;
                self.w.write_str(" ")?;
                self.value(value)
            }
            Instr::Concat { out, operands } => {
                self.def(out, "concat")?;
                self.w.write_str(" [")?;
                self.punctuated(operands, Self::value)?;
                self.w.write_str("]")
            }
            Instr::Select {
                out,
                condition,
                then_value,
                else_value,
            } => {
                self.def(out, "select")?;
                self.w.write_str(" ")?;
                self.values(&[condition, then_value, else_value])
            }
            Instr::NewTable { out } => self.def(out, "table"),
            Instr::MakePack { out, head, tail } => {
                self.pack_def(out, "pack")?;
                self.w.write_str(" [")?;
                self.punctuated(head, Self::value)?;
                if let Some(tail) = tail {
                    self.w.write_str("; ")?;
                    self.pack(tail)?;
                }
                self.w.write_str("]")
            }
            Instr::Project { out, pack, index } => {
                self.def(out, "project")?;
                self.w.write_str(" ")?;
                self.pack(pack)?;
                self.w.write_str(", ")?;
                write_styled!(self.w, Style::Number, "{index}")
            }
            Instr::Call {
                out,
                function,
                args,
            } => {
                self.pack_def(out, "call")?;
                self.w.write_str(" ")?;
                self.value(function)?;
                self.w.write_str("(")?;
                self.pack(args)?;
                self.w.write_str(")")
            }
            Instr::MethodCall {
                out,
                object,
                method,
                args,
            } => {
                self.pack_def(out, "methodcall")?;
                self.w.write_str(" (")?;
                self.value(object)?;
                self.w.write_str(", ")?;
                self.name(method)?;
                self.w.write_str(")(")?;
                self.pack(args)?;
                self.w.write_str(")")
            }
            Instr::VarArgs { out } => {
                self.pack(out)?;
                self.w.write_str(" = ")?;
                write_styled!(self.w, Style::Register, "%va")
            }
            Instr::OpenCell { cell, value } => {
                self.cell(cell)?;
                self.w.write_str(" = ")?;
                self.op("cell")?;
                self.w.write_str(" ")?;
                self.value(value)
            }
            Instr::LoadCell { out, cell } => {
                self.def(out, "load")?;
                self.w.write_str(" ")?;
                self.cell(cell)
            }
            Instr::StoreCell { cell, value } => {
                self.op("store")?;
                self.w.write_str(" ")?;
                self.cell(cell)?;
                self.w.write_str(", ")?;
                self.value(value)
            }
            Instr::SetList {
                table,
                index,
                values,
            } => {
                self.op("setlist")?;
                self.w.write_str(" ")?;
                self.value(table)?;
                self.w.write_str(", ")?;
                write_styled!(self.w, Style::Number, "{index}")?;
                self.w.write_str(", ")?;
                self.pack(values)
            }
        }
    }

    fn exit(&mut self, exit: &BlockExit) -> fmt::Result {
        match exit {
            BlockExit::Fallthrough(edge) => {
                self.op("fallthrough")?;
                self.w.write_str(" ")?;
                self.edge(edge)
            }
            BlockExit::Jump(edge) => {
                self.op("jump")?;
                self.w.write_str(" ")?;
                self.edge(edge)
            }
            BlockExit::Branch {
                condition,
                then_edge,
                else_edge,
            } => {
                self.op("branch")?;
                self.w.write_str(" ")?;
                self.value(condition)?;
                self.w.write_str(", ")?;
                self.edge(then_edge)?;
                self.w.write_str(", ")?;
                self.edge(else_edge)
            }
            BlockExit::NumericFor {
                body_edge,
                exit_edge,
                variable,
                start,
                end,
                step,
            } => {
                self.op("forn.prep")?;
                self.w.write_str(" ")?;
                self.values(&[variable, start, end, step])?;
                self.w.write_str(" -> ")?;
                self.edge(body_edge)?;
                self.w.write_str(", ")?;
                self.edge(exit_edge)
            }
            BlockExit::NumericForLoop {
                body_edge,
                exit_edge,
            } => {
                self.op("forn.loop")?;
                self.w.write_str(" ")?;
                self.edge(body_edge)?;
                self.w.write_str(", ")?;
                self.edge(exit_edge)
            }
            BlockExit::GenericFor {
                body_edge,
                loop_block,
                variables,
                values,
            } => {
                self.op("forg.prep")?;
                self.w.write_str(" [")?;
                self.punctuated(variables, Self::value)?;
                self.w.write_str("] in [")?;
                self.punctuated(values, Self::value)?;
                self.w.write_str("] -> ")?;
                self.edge(body_edge)?;
                self.w.write_str(", loop ")?;
                self.block(*loop_block)
            }
            BlockExit::GenericForLoop {
                body_edge,
                exit_edge,
                variables,
            } => {
                self.op("forg.loop")?;
                self.w.write_str(" [")?;
                self.punctuated(variables, Self::value)?;
                self.w.write_str("] -> ")?;
                self.edge(body_edge)?;
                self.w.write_str(", ")?;
                self.edge(exit_edge)
            }
            BlockExit::Return(values) => {
                self.op("return")?;
                self.w.write_str(" ")?;
                self.pack(values)
            }
        }
    }

    fn def(&mut self, out: &ValueId, op: &str) -> fmt::Result {
        self.value(out)?;
        self.w.write_str(" = ")?;
        self.op(op)
    }

    fn pack_def(&mut self, out: &PackId, op: &str) -> fmt::Result {
        self.pack(out)?;
        self.w.write_str(" = ")?;
        self.op(op)
    }

    fn op(&mut self, op: &str) -> fmt::Result {
        write_styled!(self.w, Style::Opcode, "{op}")
    }

    fn value(&mut self, value: &ValueId) -> fmt::Result {
        write_styled!(self.w, Style::Register, "%v{}", value.index())
    }

    fn values(&mut self, values: &[&ValueId]) -> fmt::Result {
        self.punctuated(values, |this, value| this.value(value))
    }

    fn pack(&mut self, pack: &PackId) -> fmt::Result {
        write_styled!(self.w, Style::Register, "%q{}", pack.index())
    }

    fn cell(&mut self, cell: &CellId) -> fmt::Result {
        match self.function.cells[*cell].origin {
            CellOrigin::Upvalue(x) => write_styled!(self.w, Style::Upvalue, "$u{x}"),
            CellOrigin::CapturedRegister { .. } => {
                write_styled!(self.w, Style::Upvalue, "$c{}", cell.index())
            }
        }
    }

    fn capture(&mut self, capture: &Capture) -> fmt::Result {
        match capture {
            Capture::Copy(value) => {
                self.w.write_str("copy ")?;
                self.value(value)
            }
            Capture::Share(cell) => {
                self.w.write_str("ref ")?;
                self.cell(cell)
            }
        }
    }

    fn block(&mut self, block: usize) -> fmt::Result {
        write_styled!(self.w, Style::Label, "bb{block}")
    }

    fn edge(&mut self, edge: &Edge) -> fmt::Result {
        self.block(edge.target)?;
        if !edge.params.is_empty() {
            self.w.write_str("(")?;
            self.punctuated(&edge.params, Self::value)?;
            self.w.write_str(")")?;
        }
        Ok(())
    }

    fn constant(&mut self, constant: &Constant) -> fmt::Result {
        let style = match constant {
            Constant::String(_) => Style::String,
            Constant::Nil | Constant::Number(_) | Constant::Bool(_) => Style::Number,
        };
        write_styled!(self.w, style, "{constant}")
    }

    fn name(&mut self, name: &impl fmt::Display) -> fmt::Result {
        write_styled!(self.w, Style::Name, "'{name}'")
    }

    fn punctuated<T>(
        &mut self,
        items: &[T],
        mut write: impl FnMut(&mut Self, &T) -> fmt::Result,
    ) -> fmt::Result {
        for (index, item) in items.iter().enumerate() {
            if index > 0 {
                self.w.write_str(", ")?;
            }
            write(self, item)?;
        }
        Ok(())
    }
}

/// Returns the IR mnemonic of a binary operator.
const fn bin_op_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::IDiv => "idiv",
        BinOp::Mod => "mod",
        BinOp::Pow => "pow",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Lte => "lte",
        BinOp::Gt => "gt",
        BinOp::Gte => "gte",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Concat => "concat",
    }
}

/// Returns the IR mnemonic of a unary operator.
const fn un_op_name(op: UnOp) -> &'static str {
    match op {
        UnOp::Minus => "neg",
        UnOp::Not => "not",
        UnOp::Length => "len",
    }
}
