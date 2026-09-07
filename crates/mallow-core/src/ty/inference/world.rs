//! Mutable inference facts owned by solver domains.

use std::collections::{HashMap, HashSet};

use id_arena::{Arena, Id};
use smol_str::SmolStr;

use super::keys::{ObjectKey, PackKey, ValueKey};
use crate::il::ProtoId;
use crate::ty::canonical::TypeId;

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
}

/// Whether a table slot is guaranteed to exist.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum TableValuePresence {
    /// No write guarantees the slot.
    #[default]
    Unknown,
    /// A constructor write guarantees the slot.
    Required,
    /// A later write may add or remove the slot.
    Optional,
}

impl TableValuePresence {
    /// Records a constructor write.
    pub fn record_initial(&mut self) {
        if *self != Self::Optional {
            *self = Self::Required;
        }
    }

    /// Records a write after construction.
    pub fn record_later(&mut self) {
        *self = Self::Optional;
    }

    /// Returns whether the slot is guaranteed to exist.
    pub fn is_required(self) -> bool {
        self == Self::Required
    }
}

/// Mutable facts for one exact table field.
#[derive(Debug)]
pub struct ObjectFieldState {
    /// Values stored in the field.
    pub value: ValueId,
    /// Whether the field is guaranteed to exist.
    pub presence: TableValuePresence,
}

/// Mutable facts for one table allocation.
#[derive(Debug)]
pub struct ObjectState {
    /// Values and presence facts under exact string keys.
    pub fields: HashMap<SmolStr, ObjectFieldState>,
    /// Types used as dynamic keys.
    pub keys: ValueId,
    /// Types written through dynamic indexes.
    pub values: ValueId,
    /// Whether the dynamic index is guaranteed to contain a value.
    pub indexer_presence: TableValuePresence,
}

/// Result of an operation that may change the inference world.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorldChange<T> {
    /// The world already contained the returned value.
    Unchanged(T),
    /// The operation changed the world and returned this value.
    Changed(T),
}

impl<T> WorldChange<T> {
    /// Returns the operation result regardless of whether the world changed.
    pub fn value(self) -> T {
        match self {
            Self::Unchanged(value) | Self::Changed(value) => value,
        }
    }
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
    #[must_use]
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
    #[must_use]
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
    #[must_use]
    pub fn object_for_key(&mut self, key: ObjectKey) -> ObjectId {
        match self.object_by_key.get(&key) {
            Some(object) => *object,
            None => {
                let keys = self.fresh_value();
                let values = self.fresh_value();
                let object = self.objects.alloc(ObjectState {
                    fields: HashMap::new(),
                    keys,
                    values,
                    indexer_presence: TableValuePresence::Unknown,
                });
                self.object_by_key.insert(key, object);
                object
            }
        }
    }

    /// Returns or creates storage for one exact object field.
    #[must_use]
    pub fn object_field(&mut self, object: ObjectId, name: SmolStr) -> WorldChange<ValueId> {
        match self.objects[object].fields.get(&name) {
            Some(field) => WorldChange::Unchanged(field.value),
            None => {
                let value = self.fresh_value();
                self.objects[object].fields.insert(
                    name,
                    ObjectFieldState {
                        value,
                        presence: TableValuePresence::Unknown,
                    },
                );
                WorldChange::Changed(value)
            }
        }
    }

    /// Allocates an anonymous scalar value.
    #[must_use]
    pub fn fresh_value(&mut self) -> ValueId {
        self.values.alloc(ValueState {
            lower: self.never,
            upper: self.unknown,
            identities: ValueIdentities::default(),
        })
    }

    /// Returns a stable positional projection variable.
    #[must_use]
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

    /// Adds one sequence alternative to a pack.
    #[must_use]
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

    /// Returns all stable value keys currently allocated.
    pub fn value_keys(&self) -> impl Iterator<Item = (ValueKey, ValueId)> {
        self.value_by_key.iter().map(|(key, id)| (key.clone(), *id))
    }
}

#[cfg(test)]
mod tests {
    use super::TableValuePresence;

    /// A later write keeps a slot optional regardless of rule order.
    #[test]
    fn later_write_dominates_initial_presence() {
        let mut initial_then_later = TableValuePresence::Unknown;
        initial_then_later.record_initial();
        initial_then_later.record_later();

        let mut later_then_initial = TableValuePresence::Unknown;
        later_then_initial.record_later();
        later_then_initial.record_initial();

        assert_eq!(initial_then_later, TableValuePresence::Optional);
        assert_eq!(later_then_initial, TableValuePresence::Optional);
    }
}
