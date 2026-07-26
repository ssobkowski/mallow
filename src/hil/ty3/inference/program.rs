//! Immutable inference relations produced from lifted SSA.

use std::collections::HashMap;

use smol_str::SmolStr;

use crate::{
    hil::ty2::{builtins::BuiltinPath, canonical::TypeId},
    il::ProtoId,
    operator::{BinOp, UnOp},
};

use super::keys::{BranchPredicate, ObjectKey, PackKey, ValueKey};

/// One relation attached to a scalar value.
#[derive(Debug, Clone, PartialEq)]
pub enum ValueRelation {
    /// Adds concrete producer evidence.
    Observe(TypeId),
    /// Adds concrete consumer evidence.
    Require(TypeId),
    /// Copies value facts from another value.
    FlowFrom(ValueKey),
    /// Equates two SSA values that name the same runtime value.
    SameAs(ValueKey),
    /// Reads one positional value from a pack.
    FromPack {
        /// Pack being projected.
        pack: PackKey,
        /// Zero-based value position.
        index: usize,
    },
    /// Reads every value that a pack can produce.
    FromPackValues {
        /// Pack being aggregated.
        pack: PackKey,
    },
    /// Builds a branch-local value from another value.
    Filter {
        /// Source value before branch filtering.
        source: ValueKey,
        /// Predicate applied to the source.
        predicate: BranchPredicate,
    },
    /// Adds one table allocation identity.
    NewObject(ObjectKey),
    /// Adds one closure identity.
    Closure(ProtoId),
    /// Adds one builtin identity.
    Builtin(BuiltinPath),
    /// Writes a named field into every object carried by this value.
    WriteField {
        /// Field selected by the write.
        field: SmolStr,
        /// Value written to the field.
        value: ValueKey,
        /// Whether construction definitely initialized this field.
        definite: bool,
    },
    /// Reads a named field from every object carried by this value.
    ReadField {
        /// Field selected by the read.
        field: SmolStr,
        /// Destination receiving the read value.
        output: ValueKey,
    },
    /// Writes a dynamic index into every object carried by this value.
    WriteIndex {
        /// Dynamic index value.
        index: ValueKey,
        /// Value written at the index.
        value: ValueKey,
    },
    /// Reads a dynamic index from every object carried by this value.
    ReadIndex {
        /// Dynamic index value.
        index: ValueKey,
        /// Destination receiving the read value.
        output: ValueKey,
    },
    /// Calls this value with argument and result packs.
    Call {
        /// Pack containing supplied arguments.
        args: PackKey,
        /// Pack receiving produced results.
        returns: PackKey,
    },
    /// Relates a binary operation to its result.
    Binary {
        /// Operation being evaluated.
        op: BinOp,
        /// Right operand.
        rhs: ValueKey,
        /// Result value.
        output: ValueKey,
    },
    /// Relates a unary operation to its result.
    Unary {
        /// Operation being evaluated.
        op: UnOp,
        /// Result value.
        output: ValueKey,
    },
}

/// One relation attached to a multivalue pack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PackRelation {
    /// A fixed prefix followed by an optional remaining pack.
    Sequence {
        /// Values guaranteed at the start of this alternative.
        head: Vec<ValueKey>,
        /// Remaining values, or `None` when this alternative ends.
        tail: Option<PackKey>,
    },
}

/// Relations and seeds collected across all lifted SSA protos.
#[derive(Debug, Default)]
pub struct InferenceProgram {
    value_relations: HashMap<ValueKey, Vec<ValueRelation>>,
    pack_relations: HashMap<PackKey, Vec<PackRelation>>,
    seeds: HashMap<ValueKey, Vec<TypeId>>,
}

impl InferenceProgram {
    /// Ensures a scalar value key exists even if no relation is attached yet.
    pub fn touch_value(&mut self, key: ValueKey) {
        self.value_relations.entry(key).or_default();
    }

    /// Ensures a pack key exists even if no relation is attached yet.
    pub fn touch_pack(&mut self, key: PackKey) {
        self.pack_relations.entry(key).or_default();
    }

    /// Adds one scalar relation unless it is already present.
    pub fn push_value(&mut self, key: ValueKey, relation: ValueRelation) {
        let relations = self.value_relations.entry(key).or_default();
        if !relations.contains(&relation) {
            relations.push(relation);
        }
    }

    /// Adds one pack relation unless it is already present.
    pub fn push_pack(&mut self, key: PackKey, relation: PackRelation) {
        let relations = self.pack_relations.entry(key).or_default();
        if !relations.contains(&relation) {
            relations.push(relation);
        }
    }

    /// Adds bytecode evidence for one scalar value.
    pub fn seed(&mut self, key: ValueKey, ty: TypeId) {
        self.seeds.entry(key).or_default().push(ty);
    }

    /// Returns scalar relations in deterministic key order.
    pub fn value_relations(&self) -> Vec<(ValueKey, Vec<ValueRelation>)> {
        let mut relations: Vec<_> = self
            .value_relations
            .iter()
            .map(|(key, relations)| (*key, relations.clone()))
            .collect();
        relations.sort_by_key(|(key, _)| *key);
        relations
    }

    /// Returns pack relations in deterministic key order.
    pub fn pack_relations(&self) -> Vec<(PackKey, Vec<PackRelation>)> {
        let mut relations: Vec<_> = self
            .pack_relations
            .iter()
            .map(|(key, relations)| (*key, relations.clone()))
            .collect();
        relations.sort_by_key(|(key, _)| *key);
        relations
    }

    /// Returns seeds in deterministic key order.
    pub fn seeds(&self) -> Vec<(ValueKey, Vec<TypeId>)> {
        let mut seeds: Vec<_> = self
            .seeds
            .iter()
            .map(|(key, types)| (*key, types.clone()))
            .collect();
        seeds.sort_by_key(|(key, _)| *key);
        seeds
    }

    /// Returns the number of scalar relations.
    pub fn value_relation_count(&self) -> usize {
        self.value_relations.values().map(Vec::len).sum()
    }

    /// Returns the number of pack relations.
    pub fn pack_relation_count(&self) -> usize {
        self.pack_relations.values().map(Vec::len).sum()
    }
}
