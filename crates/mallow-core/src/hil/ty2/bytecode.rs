use crate::{
    disasm::Chunk,
    il::{BytecodeType, Proto, TypeTag},
};

use super::canonical::TypeId;
use super::store::TypeStore;

/// Decodes one compact bytecode tag into a canonical graph ID.
///
/// Luau bytecode stores only a coarse tag, so this returns `None` when a
/// tagged userdata name cannot be recovered from its chunk.
fn decode_type_tag(tag: TypeTag, chunk: &Chunk, store: &mut TypeStore) -> Option<TypeId> {
    let ty = match tag.ty {
        BytecodeType::Nil => store.primitives().nil,
        BytecodeType::Boolean => store.primitives().boolean,
        BytecodeType::Number => store.primitives().number,
        BytecodeType::String => store.primitives().string,
        BytecodeType::Table => store.primitives().table,
        BytecodeType::Function => store.primitives().function,
        BytecodeType::Thread => store.primitives().thread,
        BytecodeType::Userdata => store.primitives().userdata,
        BytecodeType::Vector => store.primitives().vector,
        BytecodeType::Buffer => store.primitives().buffer,
        BytecodeType::Integer => store.primitives().integer,
        BytecodeType::Any => store.primitives().any,
        BytecodeType::Unknown(_) => store.primitives().unknown,
        BytecodeType::TaggedUserdata(index) => {
            let name = chunk.userdata_type_mappings.as_ref().and_then(|mappings| {
                mappings
                    .iter()
                    .find(|mapping| mapping.index == index)
                    .and_then(|mapping| mapping.name)
                    .and_then(|name| chunk.get_string(name))
                    .map(|name| name.to_string())
            })?;

            store.named(name)
        }
    };

    Some(if tag.optional {
        store.union(ty, store.primitives().nil)
    } else {
        ty
    })
}

/// Associates a bytecode-provided type with one physical register lifetime.
#[derive(Debug, Clone, PartialEq)]
pub struct LocalTypeBinding {
    /// Identifies the decoded canonical graph type.
    pub ty: TypeId,
    /// Identifies the physical register carrying the value.
    pub register: u8,
    /// Marks the first instruction covered by the binding.
    pub start_pc: u32,
    /// Marks the first instruction after the binding's lifetime.
    pub end_pc: u32,
}

/// Collects type facts decoded from one proto's bytecode metadata.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ProtoTypeContext {
    /// Stores decoded parameter types by parameter index.
    params: Vec<Option<TypeId>>,
    /// Stores decoded upvalue types by upvalue index.
    upvalues: Vec<Option<TypeId>>,
    /// Stores register-local types with their instruction lifetimes.
    locals: Vec<LocalTypeBinding>,
}

impl ProtoTypeContext {
    /// Builds a type context from the compact type records attached to `proto`.
    pub fn from_proto(proto: &Proto, chunk: &Chunk, type_store: &mut TypeStore) -> Self {
        let params = proto
            .type_info
            .function
            .as_ref()
            .map(|function| {
                function
                    .params
                    .iter()
                    .map(|tag| alloc_bytecode_tag(type_store, *tag, chunk))
                    .collect()
            })
            .unwrap_or_default();

        let upvalues = proto
            .type_info
            .upvalues
            .iter()
            .map(|tag| alloc_bytecode_tag(type_store, *tag, chunk))
            .collect();

        let locals = proto
            .type_info
            .locals
            .iter()
            .filter_map(|local| {
                let ty = alloc_bytecode_tag(type_store, local.ty, chunk)?;
                Some(LocalTypeBinding {
                    ty,
                    register: local.register,
                    start_pc: local.start_pc,
                    end_pc: local.end_pc,
                })
            })
            .collect();

        Self {
            params,
            upvalues,
            locals,
        }
    }

    /// Returns the bytecode type for a function parameter, if one exists.
    #[inline]
    pub fn param(&self, index: u8) -> Option<TypeId> {
        self.params.get(index as usize).copied().flatten()
    }

    /// Returns the bytecode type for an upvalue, if one exists.
    #[inline]
    pub fn upvalue(&self, index: u8) -> Option<TypeId> {
        self.upvalues.get(index as usize).copied().flatten()
    }

    /// Returns the local type active for `register` at `pc`, if one exists.
    #[inline]
    pub fn local_at(&self, register: u8, pc: u32) -> Option<TypeId> {
        self.locals
            .iter()
            .find(|local| local.register == register && local.start_pc <= pc && pc < local.end_pc)
            .map(|local| local.ty)
    }
}

/// Allocates one decoded bytecode tag in `store`.
fn alloc_bytecode_tag(store: &mut TypeStore, tag: TypeTag, chunk: &Chunk) -> Option<TypeId> {
    decode_type_tag(tag, chunk, store)
}
