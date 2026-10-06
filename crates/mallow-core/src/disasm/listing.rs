//! Human-readable bytecode listings.

use std::collections::BTreeMap;
use std::fmt;

use super::Chunk;
use crate::il::{ConstId, Constant, Count, DecodedInstr, Instr, Operand, Proto, ProtoId};
use crate::style::{Style, StyledWrite, write_styled};

/// Column width reserved for mnemonics. Fits the longest, `FORGPREP_INEXT`.
const OPCODE_WIDTH: usize = 14;
/// Operand columns wider than this push their annotation out instead of
/// widening the whole listing.
const MAX_OPERANDS_WIDTH: usize = 24;

/// An optionall styled piece of text.
struct Piece {
    style: Option<Style>,
    text: String,
}

impl Piece {
    fn new(style: Style, text: impl Into<String>) -> Self {
        Self {
            style: Some(style),
            text: text.into(),
        }
    }
}

/// A styled line fragment whose display width is known before it is written.
#[derive(Default)]
struct Pieces(Vec<Piece>);

impl Pieces {
    fn push(&mut self, style: Style, text: impl Into<String>) {
        self.0.push(Piece::new(style, text));
    }

    fn push_plain(&mut self, text: impl Into<String>) {
        self.0.push(Piece {
            style: None,
            text: text.into(),
        });
    }

    fn append(&mut self, other: Pieces) {
        self.0.extend(other.0);
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn width(&self) -> usize {
        self.0.iter().map(|piece| piece.text.chars().count()).sum()
    }

    fn write_to<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        for piece in &self.0 {
            match piece.style {
                Some(style) => write_styled!(w, style, "{}", piece.text)?,
                None => w.write_str(&piece.text)?,
            }
        }
        Ok(())
    }
}

/// One rendered instruction, before column alignment.
struct Row {
    word_pc: u32,
    line: Option<i32>,
    label: Option<usize>,
    instr: Instr,
    operands: Pieces,
    annotation: Pieces,
}

impl Chunk {
    /// Writes a listing of every proto in the chunk.
    pub fn write_listing<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        write_styled!(
            w,
            Style::Comment,
            "; luau bytecode version {}, types version {}",
            self.version,
            self.types_version
        )?;
        writeln!(w)?;

        self.write_userdata_types(w)?;

        for proto in &self.protos {
            writeln!(w)?;
            ProtoListing::new(self, proto).write_to(w)?;
        }

        Ok(())
    }
}

impl Chunk {
    /// Writes the table mapping tagged userdata indices to type names.
    fn write_userdata_types<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        let Some(mappings) = self
            .userdata_type_mappings
            .as_ref()
            .filter(|mappings| !mappings.is_empty())
        else {
            return Ok(());
        };

        writeln!(w, "userdata types:")?;
        for mapping in mappings {
            write!(w, "  ")?;
            write_styled!(w, Style::Constant, "tagged-userdata[{}]", mapping.index)?;
            write!(w, "  ")?;
            match self.userdata_name(mapping.index) {
                Some(name) => write_styled!(w, Style::Name, "{name}")?,
                None => write_styled!(w, Style::Comment, "<unnamed>")?,
            }
            writeln!(w)?;
        }
        writeln!(w)
    }
}

/// Renders one proto of a chunk.
struct ProtoListing<'a> {
    chunk: &'a Chunk,
    proto: &'a Proto,
    /// Label numbers keyed by the word position they mark.
    labels: BTreeMap<u32, usize>,
}

impl<'a> ProtoListing<'a> {
    fn new(chunk: &'a Chunk, proto: &'a Proto) -> Self {
        let mut labels: BTreeMap<u32, usize> = proto
            .instrs
            .iter()
            .filter_map(DecodedInstr::branch_target)
            .map(|target| (target, 0))
            .collect();
        for (index, label) in labels.values_mut().enumerate() {
            *label = index;
        }

        Self {
            chunk,
            proto,
            labels,
        }
    }

    fn write_to<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        self.write_header(w)?;
        self.write_upvalues(w)?;
        self.write_local_types(w)?;
        self.write_constants(w)?;
        self.write_code(w)
    }

    fn write_header<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        let proto = self.proto;

        write_styled!(w, Style::Heading, "function ")?;
        write_styled!(w, Style::Name, "{}", self.proto_name(proto.id))?;
        write!(w, "(")?;
        for index in 0..proto.num_params {
            if index > 0 {
                write!(w, ", ")?;
            }
            match self.local_name(index, 0) {
                Some(name) => write_styled!(w, Style::Name, "{name}")?,
                None => write_styled!(w, Style::Register, "R{index}")?,
            }
            let ty = proto
                .type_info
                .function
                .as_ref()
                .and_then(|function| function.params.get(usize::from(index)));
            if let Some(ty) = ty {
                write!(w, ": {}", self.chunk.type_name(*ty))?;
            }
        }
        if proto.is_vararg {
            if proto.num_params > 0 {
                write!(w, ", ")?;
            }
            write!(w, "...")?;
        }
        write!(w, ")")?;

        write_styled!(w, Style::Comment, "  ; proto {}", proto.id)?;
        if proto.id == self.chunk.entry_proto {
            write_styled!(w, Style::Comment, " (entry)")?;
        } else {
            write_styled!(w, Style::Comment, ", line {}", proto.line_defined)?;
        }
        write_styled!(w, Style::Comment, ", {} registers", proto.max_stack_size)?;
        writeln!(w)
    }

    fn write_upvalues<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        if self.proto.num_upvals == 0 {
            return Ok(());
        }

        writeln!(w, "  upvalues:")?;
        for index in 0..self.proto.num_upvals {
            write!(w, "    ")?;
            write_styled!(w, Style::Upvalue, "U{index}")?;
            if let Some(name) = self.upvalue_name(index) {
                write!(w, "  ")?;
                write_styled!(w, Style::Name, "{name}")?;
            }
            if let Some(ty) = self.proto.type_info.upvalues.get(usize::from(index)) {
                write!(w, ": {}", self.chunk.type_name(*ty))?;
            }
            writeln!(w)?;
        }
        Ok(())
    }

    fn write_local_types<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        let locals = &self.proto.type_info.locals;
        if locals.is_empty() {
            return Ok(());
        }

        writeln!(w, "  typed locals:")?;
        for local in locals {
            write!(w, "    ")?;
            write_styled!(w, Style::Register, "R{}", local.register)?;
            if let Some(name) = self.local_name(local.register, local.start_pc) {
                write!(w, "  ")?;
                write_styled!(w, Style::Name, "{name}")?;
            }
            write!(w, ": {}", self.chunk.type_name(local.ty))?;
            write_styled!(
                w,
                Style::Comment,
                "  ; pc {}..{}",
                local.start_pc,
                local.end_pc
            )?;
            writeln!(w)?;
        }
        Ok(())
    }

    fn write_constants<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        if self.proto.consts.is_empty() {
            return Ok(());
        }

        let width = format!("K{}", self.proto.consts.len() - 1).len();
        writeln!(w, "  constants:")?;
        for (index, constant) in self.proto.consts.iter().enumerate() {
            let id = format!("K{index}");
            write!(w, "    ")?;
            write_styled!(w, Style::Constant, "{id:<width$}")?;
            write!(w, "  ")?;
            self.constant(constant).write_to(w)?;
            writeln!(w)?;
        }
        Ok(())
    }

    fn write_code<W: StyledWrite>(&self, w: &mut W) -> fmt::Result {
        let lines = self.proto.line_info.as_ref().map(|info| info.lines());
        let rows: Vec<Row> = self
            .proto
            .instrs
            .iter()
            .map(|decoded| {
                let line = lines
                    .as_ref()
                    .and_then(|lines| lines.get(decoded.word_pc as usize).copied());
                self.row(decoded, line)
            })
            .collect();

        let pc_width = rows.last().map_or(1, |row| row.word_pc.to_string().len());
        let line_width = rows
            .iter()
            .filter_map(|row| row.line)
            .max()
            .map(|line| line.to_string().len());
        let operands_width = rows
            .iter()
            .filter(|row| !row.annotation.is_empty())
            .map(|row| row.operands.width())
            .filter(|width| *width <= MAX_OPERANDS_WIDTH)
            .max()
            .unwrap_or(0);

        writeln!(w, "  code:")?;
        for row in &rows {
            if let Some(label) = row.label {
                write!(w, "  ")?;
                write_styled!(w, Style::Label, "L{label}")?;
                writeln!(w, ":")?;
            }

            write!(w, "    ")?;
            write_styled!(w, Style::Gutter, "{:>pc_width$}", row.word_pc)?;
            if let Some(line_width) = line_width {
                match row.line {
                    Some(line) => write_styled!(w, Style::Gutter, "  {line:>line_width$}")?,
                    None => write!(w, "  {:line_width$}", "")?,
                }
            }
            write!(w, "  ")?;

            let mnemonic = row.instr.mnemonic();
            if row.operands.is_empty() && row.annotation.is_empty() {
                write_styled!(w, Style::Opcode, "{mnemonic}")?;
                writeln!(w)?;
                continue;
            }
            write_styled!(w, Style::Opcode, "{mnemonic}")?;
            let padding = OPCODE_WIDTH.saturating_sub(mnemonic.len());
            write!(w, "{:padding$} ", "")?;
            row.operands.write_to(w)?;

            if !row.annotation.is_empty() {
                let padding = operands_width.saturating_sub(row.operands.width());
                write!(w, "{:padding$}  ", "")?;
                write_styled!(w, Style::Comment, "; ")?;
                row.annotation.write_to(w)?;
            }
            writeln!(w)?;
        }

        Ok(())
    }

    /// Renders the operands and annotation of one instruction.
    fn row(&self, decoded: &DecodedInstr, line: Option<i32>) -> Row {
        let mut operands = Pieces::default();
        let mut notes = Vec::new();

        for (index, operand) in decoded.instr.operands().into_iter().enumerate() {
            if index > 0 {
                operands.push_plain(" ");
            }
            self.operand(decoded, operand, &mut operands, &mut notes);
        }

        let mut annotation = Pieces::default();
        for (index, note) in notes.into_iter().enumerate() {
            if index > 0 {
                annotation.push(Style::Comment, ", ");
            }
            annotation.append(note);
        }

        Row {
            word_pc: decoded.word_pc,
            line,
            label: self.labels.get(&decoded.word_pc).copied(),
            instr: decoded.instr,
            operands,
            annotation,
        }
    }

    /// Renders one operand, collecting anything it refers to into `notes`.
    fn operand(
        &self,
        decoded: &DecodedInstr,
        operand: Operand,
        out: &mut Pieces,
        notes: &mut Vec<Pieces>,
    ) {
        match operand {
            Operand::Reg(reg) => out.push(Style::Register, format!("R{reg}")),
            Operand::Upval(upval) => {
                out.push(Style::Upvalue, format!("U{upval}"));
                if let Some(name) = self.upvalue_name(upval) {
                    notes.push(Pieces(vec![Piece::new(Style::Name, name)]));
                }
            }
            Operand::Const(k) => {
                out.push(Style::Constant, format!("K{k}"));
                notes.push(self.constant_ref(ConstId(k)));
            }
            Operand::Import(k) => {
                out.push(Style::Constant, format!("K{k}"));
                notes.push(self.constant_ref(ConstId(k.into())));
            }
            Operand::ChildProto(index) => {
                out.push(Style::Name, format!("P{index}"));
                notes.push(match self.proto.child_protos.get(usize::from(index)) {
                    Some(id) => self.closure(*id),
                    None => Pieces(vec![Piece::new(Style::Comment, "<missing proto>")]),
                });
            }
            Operand::Int(value) => out.push(Style::Number, value.to_string()),
            Operand::Bool(value) => out.push(Style::Number, value.to_string()),
            Operand::Count(count) => match Count::new(count) {
                Count::Number(n) => out.push(Style::Number, n.to_string()),
                Count::Variadic => out.push(Style::Number, "MULTRET"),
            },
            Operand::HashSize(0) => out.push(Style::Number, "0"),
            Operand::HashSize(size) => {
                let size = 1u64.checked_shl(u32::from(size) - 1);
                out.push(
                    Style::Number,
                    size.map_or("?".to_owned(), |s| s.to_string()),
                );
            }
            Operand::Jump(offset) => match decoded
                .branch_target()
                .and_then(|target| self.labels.get(&target))
            {
                Some(label) => out.push(Style::Label, format!("L{label}")),
                None => out.push(Style::Label, format!("{offset:+}")),
            },
            Operand::Skip(skip) => out.push(Style::Number, format!("+{skip}")),
            Operand::Builtin(builtin) => out.push(Style::Number, builtin.to_string()),
            Operand::Capture(kind) => out.push(
                Style::Opcode,
                match kind {
                    0 => "VAL".to_owned(),
                    1 => "REF".to_owned(),
                    2 => "UPVAL".to_owned(),
                    other => other.to_string(),
                },
            ),
            Operand::Not => out.push(Style::Opcode, "NOT"),
        }
    }

    /// Renders the constant `id` refers to.
    fn constant_ref(&self, id: ConstId) -> Pieces {
        match self.proto.get_constant(id) {
            Some(constant) => self.constant(constant),
            None => Pieces(vec![Piece::new(Style::Comment, "<missing constant>")]),
        }
    }

    /// Renders a constant value.
    fn constant(&self, constant: &Constant) -> Pieces {
        let mut out = Pieces::default();
        match constant {
            Constant::Nil => out.push(Style::Number, "nil"),
            Constant::Boolean(value) => out.push(Style::Number, value.to_string()),
            Constant::Number(value) => out.push(Style::Number, value.to_string()),
            Constant::Integer(value) => out.push(Style::Number, format!("{value}i")),
            Constant::Vector { x, y, z, w } => out.push(
                Style::Number,
                if *w == 0.0 {
                    format!("vector({x}, {y}, {z})")
                } else {
                    format!("vector({x}, {y}, {z}, {w})")
                },
            ),
            Constant::String(id) => match self.chunk.get_string(*id) {
                Some(string) => out.push(Style::String, format!("\"{string}\"")),
                None => out.push(Style::Comment, "<missing string>"),
            },
            Constant::Import(path) => {
                let names: Option<Vec<String>> = path.const_ids().ok().and_then(|ids| {
                    ids.map(|id| match self.proto.get_constant(id)? {
                        Constant::String(id) => Some(self.chunk.get_string(*id)?.to_string()),
                        _ => None,
                    })
                    .collect()
                });
                match names {
                    Some(names) => out.push(Style::Name, names.join(".")),
                    None => out.push(Style::Comment, "<malformed import>"),
                }
            }
            Constant::Closure(id) => out.append(self.closure(*id)),
            Constant::Table => out.push(Style::Comment, "{}"),
            Constant::TableWithConstants(items) => {
                out.push(Style::Comment, "{");
                for (index, (key, value)) in items.iter().enumerate() {
                    if index > 0 {
                        out.push(Style::Comment, ", ");
                    }
                    match self.proto.get_constant(*key) {
                        Some(Constant::String(id)) => match self.chunk.get_string(*id) {
                            Some(name) => out.push(Style::Name, name.to_string()),
                            None => out.push(Style::Comment, "<missing string>"),
                        },
                        Some(key) => {
                            out.push(Style::Comment, "[");
                            out.append(self.constant(key));
                            out.push(Style::Comment, "]");
                        }
                        None => out.push(Style::Comment, "<missing constant>"),
                    }
                    if let Some(value) = value {
                        out.push(Style::Comment, " = ");
                        out.append(self.constant_ref(*value));
                    }
                }
                out.push(Style::Comment, "}");
            }
        }
        out
    }

    /// Renders a reference to the closure built from proto `id`.
    fn closure(&self, id: ProtoId) -> Pieces {
        Pieces(vec![
            Piece::new(Style::Name, self.proto_name(id)),
            Piece::new(Style::Comment, format!(" (proto {id})")),
        ])
    }

    /// Returns the debug name of proto `id`, or a placeholder.
    fn proto_name(&self, id: ProtoId) -> String {
        let name = self
            .chunk
            .get_proto(id)
            .and_then(|proto| proto.debug_name)
            .and_then(|name| self.chunk.get_string(name));
        match name {
            Some(name) => name.to_string(),
            None if id == self.chunk.entry_proto => "<main>".to_owned(),
            None => "<anonymous>".to_owned(),
        }
    }

    /// Returns the debug name of the local living in `register` at `pc`.
    fn local_name(&self, register: u8, pc: u32) -> Option<String> {
        let index = self.proto.local_index_at(register, pc)?;
        let name = self.proto.locals[index].name;
        Some(self.chunk.get_string(name)?.to_string())
    }

    /// Returns the debug name of upvalue `index`.
    fn upvalue_name(&self, index: u8) -> Option<String> {
        let name = (*self.proto.upvalue_names.get(usize::from(index))?)?;
        Some(self.chunk.get_string(name)?.to_string())
    }
}
