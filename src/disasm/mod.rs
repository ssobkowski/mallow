use anyhow::Result;

use crate::il::{Constant, LuauString, Proto, ProtoId, StringId, UserdataTypeMapping};

mod reader;

#[derive(Debug)]
pub struct Chunk {
    pub version: u8,
    pub types_version: u8,
    pub userdata_type_mappings: Option<Vec<UserdataTypeMapping>>,
    pub protos: Vec<Proto>,
    pub strings: Vec<LuauString>,
    pub entry_proto: ProtoId,
}

impl Chunk {
    /// Resolves the [`Proto`] with the given [`ProtoId`].
    #[inline]
    pub fn get_proto(&self, id: ProtoId) -> Option<&Proto> {
        self.protos.get(id.0 as usize)
    }

    /// Resolves the [`LuauString`] with the given [`StringId`].
    #[inline]
    pub fn get_string(&self, id: StringId) -> Option<LuauString> {
        let idx = id.0 as usize;
        self.strings.get(idx.checked_sub(1)?).cloned()
    }

    /// Writes a string representation of the [`Chunk`] to the given formatter.
    pub fn dump(&self, w: &mut impl std::io::Write) -> Result<()> {
        writeln!(w, "Bytecode Version: {}", self.version)?;
        writeln!(w, "Types Version: {}", self.types_version)?;
        writeln!(w)?;

        for proto in &self.protos {
            let name = proto.debug_name.and_then(|id| self.get_string(id));

            write!(w, "Proto {} ", proto.id.0)?;
            match name {
                Some(name) => write!(w, "({}) ", name)?,
                None => write!(w, "(??) ")?,
            }

            if let Some(ty) = &proto.type_info.function {
                write!(w, "(")?;
                for i in 0..ty.num_params {
                    write!(w, "{}", ty.params[i as usize])?;
                    if i < ty.num_params - 1 {
                        write!(w, ", ")?;
                    }
                }
                write!(w, ") ")?;
            }

            writeln!(w, "[{} upvalues]:", proto.num_upvals)?;

            writeln!(w, "  Constants:")?;
            for (i, ct) in proto.consts.iter().enumerate() {
                write!(w, "    K{}: ", i)?;
                self.dump_constant(ct, proto, w)?;
                writeln!(w)?;
            }

            writeln!(w, "  Instructions:")?;
            for sd in &proto.instrs {
                writeln!(w, "    {}: {}", sd.pc, sd.node)?;
            }

            writeln!(w)?;
        }

        Ok(())
    }

    fn dump_constant(
        &self,
        ct: &Constant,
        proto: &Proto,
        w: &mut dyn std::io::Write,
    ) -> Result<()> {
        match ct {
            Constant::Nil => write!(w, "nil")?,
            Constant::Boolean(b) => write!(w, "{}", b)?,
            Constant::Number(n) => write!(w, "{}", n)?,
            Constant::String(id) => match self.get_string(*id) {
                Some(resolved) => write!(w, "\"{}\"", resolved)?,
                None => write!(w, "<missing string>")?,
            },
            Constant::Import(path) => {
                write!(w, "[import] ")?;
                for (i, id) in path.const_ids()?.enumerate() {
                    if i > 0 {
                        write!(w, ".")?;
                    }
                    let s = proto.get_constant(id).and_then(|ct| match ct {
                        Constant::String(id) => self.get_string(*id),
                        _ => None,
                    });
                    match s {
                        Some(resolved) => write!(w, "{}", resolved)?,
                        None => write!(w, "<missing string>")?,
                    }
                }
            }
            Constant::Table => write!(w, "{{}}")?,
            Constant::Closure(c) => write!(w, "closure({})", c)?,
            Constant::Vector { x, y, z, w: vw } => write!(w, "vector({x}, {y}, {z}, {vw})")?,
            Constant::TableWithConstants(items) => {
                write!(w, "{{")?;
                let mut wrote_item = false;
                for (key, value) in items {
                    let Some(value) = value else { continue };
                    let Some(key) = proto.get_constant(*key) else {
                        continue;
                    };
                    let Some(value) = proto.get_constant(*value) else {
                        continue;
                    };

                    if wrote_item {
                        write!(w, ", ")?;
                    }

                    self.dump_constant(key, proto, w)?;
                    write!(w, ": ")?;
                    self.dump_constant(value, proto, w)?;
                    wrote_item = true;
                }
                write!(w, "}}")?;
            }
            Constant::Integer(i) => write!(w, "{}i", i)?,
        };
        Ok(())
    }
}

pub fn disassemble(bytecode: &[u8]) -> Result<Chunk> {
    reader::BytecodeReader::new(bytecode).read_chunk()
}
