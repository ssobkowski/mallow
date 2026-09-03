//! Whole-program type inference for FIR.

mod engine;
mod keys;
mod lower;
mod program;
mod world;

use std::collections::HashMap;

use super::bytecode::ProtoTypeContext;
use super::store::TypeStore;
use crate::il::ProtoId;
use crate::ir::Unit;
use crate::ir::fir::{CellId, Function, ValueId};
use crate::ty::canonical::TypeId;

use keys::ValueKey;
use program::InferenceProgram;

/// Types inferred for one complete FIR unit.
pub(crate) struct Output {
    /// Canonical graph that owns every inferred type.
    store: TypeStore,
    /// Materialized types indexed by stable FIR identity.
    values: HashMap<ValueKey, TypeId>,
}

impl Output {
    /// Returns the inferred type for one immutable FIR value.
    pub(crate) fn value(&self, proto: ProtoId, value: ValueId) -> Option<TypeId> {
        self.values.get(&ValueKey::Value(proto, value)).copied()
    }

    /// Returns the inferred type for one mutable FIR cell.
    pub(crate) fn cell(&self, proto: ProtoId, cell: CellId) -> Option<TypeId> {
        self.values.get(&ValueKey::Cell(proto, cell)).copied()
    }

    /// Joins several inferred types in the output graph.
    pub(crate) fn join(&mut self, types: impl IntoIterator<Item = TypeId>) -> Option<TypeId> {
        let types: std::collections::HashSet<_> = types.into_iter().collect();
        match types.len() {
            0 => None,
            1 => types.into_iter().next(),
            _ => Some(self.store.join_all(types)),
        }
    }

    /// Returns the canonical graph that owns every returned type ID.
    pub(crate) fn into_store(self) -> TypeStore {
        self.store
    }
}

/// Infers types for a complete FIR unit.
pub(crate) fn run(unit: &Unit<Function>) -> Output {
    let mut store = TypeStore::new();
    let mut program = lower::lower_functions(unit, &mut store);
    seed_bytecode_types(&mut program, unit, &mut store);

    engine::run(program, unit, store)
}

/// Seeds parameter and upvalue identities from coarse bytecode type records.
fn seed_bytecode_types(
    program: &mut InferenceProgram,
    unit: &Unit<Function>,
    store: &mut TypeStore,
) {
    for function in unit.functions() {
        let context = ProtoTypeContext::from_type_info(
            &function.type_info,
            unit.userdata_names().unwrap_or(&[]),
            store,
        );
        for (index, value) in function.params.iter().enumerate() {
            let Some(ty) = context.param(index) else {
                continue;
            };
            program.seed(ValueKey::Value(function.id, *value), ty);
        }
        for (index, cell) in function.upvalues.iter().enumerate() {
            let Some(ty) = context.upvalue(index) else {
                continue;
            };
            program.seed(ValueKey::Cell(function.id, *cell), ty);
        }
    }
}
