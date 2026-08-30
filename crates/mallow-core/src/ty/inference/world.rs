//! Mutable inference facts owned by solver domains.

use std::collections::{HashMap, HashSet};

use id_arena::{Arena, Id};
use smol_str::SmolStr;

use super::keys::{ObjectKey, PackKey, ValueKey};
use crate::hil::ty::builtins::BuiltinPath;
use crate::hil::ty::canonical::TypeId;
use crate::il::ProtoId;

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
    /// Concrete builtin identities carried by the value.
    pub builtins: HashSet<BuiltinPath>,
}

/// Types and identities known for one scalar value.
#[derive(Debug, Clone)]
pub struct ValueState {
    /// Types known to come from this value.
    pub lower: TypeId,
    /// Types this value must be able to support.
    pub upper: TypeId,
    /// Concrete runtime identities carried by this value.
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
    /// Types used as dynamic keys.
    pub keys: ValueId,
    /// Types written through dynamic indexes.
    pub values: ValueId,
    /// Named field storage.
    pub fields: HashMap<SmolStr, ObjectField>,
    /// Table allocations installed as metatables.
    pub metatables: HashSet<ObjectId>,
}

/// Result of an operation that may change the inference world.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorldChange<T> {
    /// The world already contained the returned value.
    Unchanged(T),
    /// The operation changed the world and returned this value.
    Changed(T),
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
    #[inline]
    pub fn value_for_key(&mut self, key: ValueKey) -> ValueId {
        match self.value_by_key.get(&key) {
            Some(value) => *value,
            None => {
                let value = self.fresh_value();
                self.value_by_key.insert(key, value);
                value
            }
        }
    }

    /// Returns or creates the pack for a stable key.
    #[inline]
    pub fn pack_for_key(&mut self, key: PackKey) -> PackId {
        match self.pack_by_key.get(&key) {
            Some(pack) => *pack,
            None => {
                let pack = self.packs.alloc(PackState::default());
                self.pack_by_key.insert(key, pack);
                pack
            }
        }
    }

    /// Returns or creates the object for a stable key.
    #[inline]
    pub fn object_for_key(&mut self, key: ObjectKey) -> ObjectId {
        match self.object_by_key.get(&key) {
            Some(object) => *object,
            None => {
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
        }
    }

    /// Allocates an anonymous scalar value.
    #[inline]
    pub fn fresh_value(&mut self) -> ValueId {
        self.values.alloc(ValueState {
            lower: self.never,
            upper: self.unknown,
            identities: ValueIdentities::default(),
        })
    }

    /// Allocates an anonymous pack.
    #[inline]
    pub fn fresh_pack(&mut self) -> PackId {
        self.packs.alloc(PackState::default())
    }

    /// Returns a stable positional projection variable.
    #[inline]
    pub fn projection(&mut self, pack: PackId, index: usize) -> WorldChange<ValueId> {
        match self.packs[pack].projections.get(&index) {
            Some(value) => WorldChange::Unchanged(*value),
            None => {
                let value = self.fresh_value();
                self.packs[pack].projections.insert(index, value);
                WorldChange::Changed(value)
            }
        }
    }

    /// Returns a stable aggregate variable for values a pack can produce.
    #[inline]
    pub fn pack_values(&mut self, pack: PackId) -> WorldChange<ValueId> {
        match self.packs[pack].values {
            Some(value) => WorldChange::Unchanged(value),
            None => {
                let value = self.fresh_value();
                self.packs[pack].values = Some(value);
                WorldChange::Changed(value)
            }
        }
    }

    /// Adds one sequence alternative to a pack.
    #[inline]
    pub fn add_pack_alternative(
        &mut self,
        pack: PackId,
        alternative: PackAlternative,
    ) -> WorldChange<()> {
        if self.packs[pack].alternatives.contains(&alternative) {
            return WorldChange::Unchanged(());
        }

        self.packs[pack].alternatives.push(alternative);
        WorldChange::Changed(())
    }

    /// Returns or creates a field value in an object.
    #[inline]
    pub fn object_field(
        &mut self,
        object: ObjectId,
        field: SmolStr,
        definite: bool,
    ) -> WorldChange<ValueId> {
        match self.objects[object].fields.get_mut(&field) {
            Some(existing) => {
                if definite && !existing.definite {
                    existing.definite = true;
                    WorldChange::Changed(existing.value)
                } else {
                    WorldChange::Unchanged(existing.value)
                }
            }
            None => {
                let value = self.fresh_value();
                self.objects[object]
                    .fields
                    .insert(field, ObjectField { value, definite });
                WorldChange::Changed(value)
            }
        }
    }

    /// Returns all stable value keys currently allocated.
    #[inline]
    pub fn value_keys(&self) -> impl Iterator<Item = (ValueKey, ValueId)> {
        self.value_by_key.iter().map(|(key, id)| (*key, *id))
    }

    /// Returns the value for a key if it has been allocated.
    #[inline]
    pub fn get_value_key(&self, key: ValueKey) -> Option<ValueId> {
        self.value_by_key.get(&key).copied()
    }

    /// Returns the pack for a key if it has been allocated.
    #[inline]
    pub fn get_pack_key(&self, key: PackKey) -> Option<PackId> {
        self.pack_by_key.get(&key).copied()
    }
}
