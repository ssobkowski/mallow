use anyhow::Result;

use crate::common::ByteString;
use crate::il::{BytecodeType, Proto, ProtoId, StringId, TypeTag, UserdataTypeMapping};

mod listing;
mod reader;

#[derive(Debug)]
pub struct Chunk {
    pub version: u8,
    pub types_version: u8,
    pub userdata_type_mappings: Option<Vec<UserdataTypeMapping>>,
    pub protos: Vec<Proto>,
    pub strings: Vec<ByteString>,
    pub entry_proto: ProtoId,
}

impl Chunk {
    /// Resolves the [`Proto`] with the given [`ProtoId`].
    #[inline]
    pub fn get_proto(&self, id: ProtoId) -> Option<&Proto> {
        self.protos.get(id.0 as usize)
    }

    /// Resolves the [`ByteString`] with the given [`StringId`].
    #[inline]
    pub fn get_string(&self, id: StringId) -> Option<ByteString> {
        let idx = id.0 as usize;
        self.strings.get(idx.checked_sub(1)?).cloned()
    }

    /// Resolves the name the tagged userdata `index` maps to.
    pub(crate) fn userdata_name(&self, index: u8) -> Option<String> {
        let mapping = self
            .userdata_type_mappings
            .as_ref()?
            .iter()
            .find(|mapping| mapping.index == index)?;
        Some(self.get_string(mapping.name?)?.to_string())
    }

    /// Formats a type tag, resolving tagged userdata names through the chunk.
    pub(crate) fn type_name(&self, tag: TypeTag) -> String {
        let mut base = match tag.ty {
            BytecodeType::TaggedUserdata(index) => self
                .userdata_name(index)
                .unwrap_or_else(|| format!("tagged-userdata[{index}]")),
            _ => tag.ty.to_string(),
        };

        if tag.optional {
            base.push('?');
        }

        base
    }
}

pub fn disassemble(bytecode: &[u8]) -> Result<Chunk> {
    reader::BytecodeReader::new(bytecode).read_chunk()
}
