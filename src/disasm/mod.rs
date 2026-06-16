use anyhow::Result;

use crate::il::{LuauString, Proto, ProtoId, StringId, UserdataTypeMapping};

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
            for sd in &proto.instrs {
                writeln!(w, "{}: {}", sd.pc, sd.node)?;
            }

            writeln!(w)?;
        }

        Ok(())
    }
}

pub fn disassemble(bytecode: &[u8]) -> Result<Chunk> {
    reader::BytecodeReader::new(bytecode).read_chunk()
}
