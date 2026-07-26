//! Mutable inference facts owned by solver domains.

use std::collections::{HashMap, HashSet};

use id_arena::{Arena, Id};
use smol_str::SmolStr;

use crate::{
    hil::ty2::{builtins::BuiltinPath, canonical::TypeId},
    il::ProtoId,
};

use super::keys::{ObjectKey, PackKey, ValueKey};

/// Stable handle for one value state.
pub type ValueId = Id<ValueState>;

/// Stable handle for one pack state.
pub type PackId = Id<PackState>;

/// Stable handle for one object state.
pub type ObjectId = Id<ObjectState>;

/// Runtime identities carried by a value.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ValueIdentities {
    /// Concrete lifted closures carried by the value.
    pub closures: HashSet<ProtoId>,
    /// Concrete mutable table allocations carried by the value.
    pub objects: HashSet<ObjectId>,
    /// Concrete builtin schemes carried by the value.
    pub builtins: HashSet<BuiltinPath>,
}

/// Bounds and identities known for one scalar value.
#[derive(Debug, Clone)]
pub struct ValueState {
    /// Union of producer evidence.
    pub lower: TypeId,
    /// Intersection of consumer evidence.
    pub upper: TypeId,
    /// Concrete runtime identities.
    pub identities: ValueIdentities,
}

/// One sequence alternative carried by a pack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackAlternative {
    /// Values guaranteed at the start of this alternative.
    pub head: Vec<ValueId>,
    /// Remaining sequence, or `None` when this alternative ends.
    pub tail: Option<PackId>,
}

/// Mutable facts and requested views for one multivalue pack.
#[derive(Debug, Default)]
pub struct PackState {
    /// Sequence alternatives discovered for the pack.
    pub alternatives: Vec<PackAlternative>,
    /// Stable positional projections requested by consumers.
    pub projections: HashMap<usize, ValueId>,
    /// Aggregate of values the pack can produce.
    pub values: Option<ValueId>,
}

/// One named object field.
#[derive(Debug, Clone, Copy)]
pub struct ObjectField {
    /// Value accumulating writes to the field.
    pub value: ValueId,
    /// Whether construction definitely initialized the field.
    pub definite: bool,
}

/// Mutable facts for one table allocation.
#[derive(Debug)]
pub struct ObjectState {
    /// Values observed as dynamic keys.
    pub keys: ValueId,
    /// Values observed through dynamic writes.
    pub values: ValueId,
    /// Named field storage.
    pub fields: HashMap<SmolStr, ObjectField>,
    /// Table allocations installed as metatables.
    pub metatables: HashSet<ObjectId>,
}

/// All mutable inference facts, split by semantic domain.
#[derive(Debug)]
pub struct World {
    /// Scalar value states.
    pub values: Arena<ValueState>,
    /// Pack states.
    pub packs: Arena<PackState>,
    /// Object states.
    pub objects: Arena<ObjectState>,
    value_by_key: HashMap<ValueKey, ValueId>,
    pack_by_key: HashMap<PackKey, PackId>,
    object_by_key: HashMap<ObjectKey, ObjectId>,
    never: TypeId,
    unknown: TypeId,
}

impl World {
    /// Creates an empty world using canonical bottom and top values.
    pub fn new(never: TypeId, unknown: TypeId) -> Self {
        Self {
            values: Arena::new(),
            packs: Arena::new(),
            objects: Arena::new(),
            value_by_key: HashMap::new(),
            pack_by_key: HashMap::new(),
            object_by_key: HashMap::new(),
            never,
            unknown,
        }
    }

    /// Returns or creates the value for a stable key.
    pub fn value_for_key(&mut self, key: ValueKey) -> ValueId {
        if let Some(value) = self.value_by_key.get(&key) {
            return *value;
        }
        let value = self.fresh_value();
        self.value_by_key.insert(key, value);
        value
    }

    /// Returns or creates the pack for a stable key.
    pub fn pack_for_key(&mut self, key: PackKey) -> PackId {
        if let Some(pack) = self.pack_by_key.get(&key) {
            return *pack;
        }
        let pack = self.packs.alloc(PackState::default());
        self.pack_by_key.insert(key, pack);
        pack
    }

    /// Returns or creates the object for a stable key.
    pub fn object_for_key(&mut self, key: ObjectKey) -> ObjectId {
        if let Some(object) = self.object_by_key.get(&key) {
            return *object;
        }
        let keys = self.fresh_value();
        let values = self.fresh_value();
        let object = self.objects.alloc(ObjectState {
            keys,
            values,
            fields: HashMap::new(),
            metatables: HashSet::new(),
        });
        self.object_by_key.insert(key, object);
        object
    }

    /// Allocates an anonymous scalar value.
    pub fn fresh_value(&mut self) -> ValueId {
        self.values.alloc(ValueState {
            lower: self.never,
            upper: self.unknown,
            identities: ValueIdentities::default(),
        })
    }

    /// Allocates an anonymous pack.
    pub fn fresh_pack(&mut self) -> PackId {
        self.packs.alloc(PackState::default())
    }

    /// Returns a stable positional projection variable.
    pub fn projection(&mut self, pack: PackId, index: usize) -> (ValueId, bool) {
        if let Some(value) = self.packs[pack].projections.get(&index) {
            return (*value, false);
        }
        let value = self.fresh_value();
        self.packs[pack].projections.insert(index, value);
        (value, true)
    }

    /// Returns a stable aggregate variable for values a pack can produce.
    pub fn pack_values(&mut self, pack: PackId) -> (ValueId, bool) {
        if let Some(value) = self.packs[pack].values {
            return (value, false);
        }
        let value = self.fresh_value();
        self.packs[pack].values = Some(value);
        (value, true)
    }

    /// Adds one sequence alternative to a pack.
    pub fn add_pack_alternative(&mut self, pack: PackId, alternative: PackAlternative) -> bool {
        if self.packs[pack].alternatives.contains(&alternative) {
            return false;
        }
        self.packs[pack].alternatives.push(alternative);
        true
    }

    /// Returns or creates a field value in an object.
    pub fn object_field(
        &mut self,
        object: ObjectId,
        field: SmolStr,
        definite: bool,
    ) -> (ValueId, bool) {
        if let Some(existing) = self.objects[object].fields.get_mut(&field) {
            let changed = definite && !existing.definite;
            existing.definite |= definite;
            return (existing.value, changed);
        }
        let value = self.fresh_value();
        self.objects[object]
            .fields
            .insert(field, ObjectField { value, definite });
        (value, true)
    }

    /// Returns all stable value keys currently allocated.
    pub fn value_keys(&self) -> Vec<(ValueKey, ValueId)> {
        let mut keys: Vec<_> = self
            .value_by_key
            .iter()
            .map(|(key, id)| (*key, *id))
            .collect();
        keys.sort_by_key(|(key, _)| *key);
        keys
    }

    /// Returns the value for a key if it has been allocated.
    pub fn get_value_key(&self, key: ValueKey) -> Option<ValueId> {
        self.value_by_key.get(&key).copied()
    }

    /// Returns the pack for a key if it has been allocated.
    pub fn get_pack_key(&self, key: PackKey) -> Option<PackId> {
        self.pack_by_key.get(&key).copied()
    }
}
