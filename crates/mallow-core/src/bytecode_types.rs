use std::collections::HashMap;
use std::hash::Hash;

use crate::ast;
use crate::il::{BytecodeType, ProtoId, TypeTag};
use crate::ir::fir::{CellId, Function, ValueId};
use crate::ir::{Unit, UserdataTypeMapping};

/// Type annotations indexed by FIR identities.
#[derive(Debug, Default)]
pub(crate) struct BytecodeTypes {
    /// Types attached to immutable FIR values.
    values: HashMap<(ProtoId, ValueId), RecoveredType>,
    /// Types attached to mutable FIR cells.
    cells: HashMap<(ProtoId, CellId), RecoveredType>,
}

/// Resolution state for metadata records that map to one FIR identity.
#[derive(Debug)]
enum RecoveredType {
    /// Every mapped record agrees on this type.
    Exact(ast::Type),
    /// Mapped records disagree, so no annotation can be emitted safely.
    Conflict,
}

impl BytecodeTypes {
    /// Recovers all annotations represented directly by one FIR unit's metadata.
    pub(crate) fn read(unit: &Unit<Function>) -> Self {
        let mappings = unit.userdata_names().unwrap_or(&[]);
        let mut output = Self::default();

        for function in unit.functions() {
            if let Some(function_types) = &function.type_info.function {
                for (value, tag) in function.params.iter().zip(&function_types.params) {
                    let Some(ty) = decode_type_tag(*tag, mappings) else {
                        continue;
                    };
                    insert_exact(&mut output.values, (function.id, *value), ty);
                }
            }

            for (cell, tag) in function.upvalues.iter().zip(&function.type_info.upvalues) {
                let Some(ty) = decode_type_tag(*tag, mappings) else {
                    continue;
                };
                insert_exact(&mut output.cells, (function.id, *cell), ty);
            }

            for (local, binding) in function.debug.locals.iter().zip(&function.bindings) {
                let mut recovered = function
                    .type_info
                    .locals
                    .iter()
                    .filter(|candidate| {
                        candidate.register == local.register
                            && candidate.start_pc < local.end_pc
                            && local.start_pc < candidate.end_pc
                    })
                    .filter_map(|candidate| decode_type_tag(candidate.ty, mappings));
                let Some(ty) = recovered.next() else {
                    continue;
                };
                if recovered.any(|candidate| candidate != ty) {
                    continue;
                }

                for value in &binding.values {
                    insert_exact(&mut output.values, (function.id, *value), ty.clone());
                }
                for cell in &binding.cells {
                    insert_exact(&mut output.cells, (function.id, *cell), ty.clone());
                }
            }
        }

        output
    }

    /// Returns the bytecode annotation for an immutable FIR value.
    pub(crate) fn value(&self, proto: ProtoId, value: ValueId) -> Option<ast::Type> {
        match self.values.get(&(proto, value))? {
            RecoveredType::Exact(ty) => Some(ty.clone()),
            RecoveredType::Conflict => None,
        }
    }

    /// Returns the bytecode annotation for a mutable FIR cell.
    pub(crate) fn cell(&self, proto: ProtoId, cell: CellId) -> Option<ast::Type> {
        match self.cells.get(&(proto, cell))? {
            RecoveredType::Exact(ty) => Some(ty.clone()),
            RecoveredType::Conflict => None,
        }
    }
}

/// Inserts one annotation and rejects conflicting metadata for the same identity.
fn insert_exact<K>(types: &mut HashMap<K, RecoveredType>, key: K, ty: ast::Type)
where
    K: Eq + Hash,
{
    types
        .entry(key)
        .and_modify(|current| {
            if matches!(current, RecoveredType::Exact(existing) if *existing != ty) {
                *current = RecoveredType::Conflict;
            }
        })
        .or_insert(RecoveredType::Exact(ty));
}

/// Decodes one compact bytecode type tag into a printable source type.
fn decode_type_tag(tag: TypeTag, mappings: &[UserdataTypeMapping]) -> Option<ast::Type> {
    let ty = match tag.ty {
        BytecodeType::Nil => ast::Type::Nil,
        BytecodeType::Boolean => ast::Type::Boolean,
        BytecodeType::Number => ast::Type::Number,
        BytecodeType::String => ast::Type::String,
        BytecodeType::Table => ast::Type::Table,
        BytecodeType::Function => ast::Type::Function,
        BytecodeType::Thread => ast::Type::Thread,
        BytecodeType::Userdata => ast::Type::Userdata,
        BytecodeType::Vector => ast::Type::Vector,
        BytecodeType::Buffer => ast::Type::Buffer,
        BytecodeType::Integer => ast::Type::Integer,
        BytecodeType::Any => ast::Type::Any,
        BytecodeType::TaggedUserdata(index) => {
            let name = mappings
                .iter()
                .find(|mapping| mapping.index == index)
                .and_then(|mapping| mapping.name.as_ref())
                .and_then(|name| name.as_utf8())?;
            ast::Type::Named(name.into())
        }
        BytecodeType::Unknown(_) => ast::Type::Unknown,
    };

    if tag.optional {
        Some(ast::Type::Union(vec![ty, ast::Type::Nil]))
    } else {
        Some(ty)
    }
}
