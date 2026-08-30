//! Immutable inference relations produced from lifted SSA.

use std::collections::HashMap;

use smol_str::SmolStr;

use super::keys::{BranchPredicate, ObjectKey, PackKey, ValueKey};
use crate::hil::ty::builtins::BuiltinPath;
use crate::hil::ty::canonical::TypeId;
use crate::il::ProtoId;
use crate::operator::{BinOp, UnOp};

/// One relation attached to one scalar value.
///
/// The lowerer writes these relations while it reads the SSA program. They
/// are descriptions, not actions. The engine later turns them into rules.
///
/// The key passed to `InferenceProgram::push_value` is the value receiving
/// the relation. For example, a `ReadField` relation is attached to the
/// object being read, while a `Binary` relation is attached to its left
/// operand.
#[derive(Debug, Clone, PartialEq)]
pub enum ValueRelation {
    /// Says that this value can produce `ty`.
    ///
    /// ```lua
    /// local value = 123
    /// ```
    ///
    /// The temporary for `123` produces `number`.
    Produce(TypeId),
    /// Says that this value must be usable as `ty`.
    ///
    /// ```lua
    /// local result = value + 1
    /// ```
    ///
    /// The addition needs `value` to be a number. The current lowerer usually
    /// records this need inside `Binary` or `Unary` instead.
    Require(TypeId),
    /// Connects this value to another value so type and identity facts can
    /// flow from the other value. Requirements can also flow back.
    ///
    /// ```lua
    /// local result = calculate()
    /// ```
    ///
    /// The result variable receives facts from the temporary holding the call
    /// result.
    FlowFrom(ValueKey),
    /// Says that two SSA values name the same runtime value.
    ///
    /// ```lua
    /// local other = value
    /// ```
    SameAs(ValueKey),
    /// Says that two values are possible contents of one mutable storage cell.
    ///
    /// This relation is used for different SSA versions of an upvalue and for
    /// captures that share storage with their parent.
    SameStorage(ValueKey),
    /// Reads one value from a pack at a given position.
    ///
    /// ```lua
    /// local first, second = get_values()
    /// ```
    ///
    /// This creates one relation for `first` and one for `second`.
    FromPack {
        /// Pack being read.
        pack: PackKey,
        /// Zero-based position to read.
        index: usize,
    },
    /// Collects all values that a pack can produce.
    ///
    /// ```lua
    /// local values = { get_values() }
    /// ```
    FromPackValues {
        /// Pack being collected.
        pack: PackKey,
    },
    /// Makes a branch-specific value from another value.
    ///
    /// ```lua
    /// if value then
    ///     -- the truthy value is used here
    /// end
    /// ```
    ///
    /// The current lowerer does not emit this relation yet.
    Filter {
        /// Value before branch filtering.
        source: ValueKey,
        /// Test used by the branch.
        predicate: BranchPredicate,
    },
    /// Gives a value one concrete table identity.
    ///
    /// ```lua
    /// local object = {}
    /// ```
    NewObject(ObjectKey),
    /// Gives a value one concrete closure identity.
    ///
    /// ```lua
    /// local function_value = function(value)
    ///     return value
    /// end
    /// ```
    Closure(ProtoId),
    /// Gives a value one known builtin identity.
    ///
    /// ```lua
    /// local write = print
    /// ```
    Builtin(BuiltinPath),
    /// Writes a named field on every table carried by this value.
    ///
    /// ```lua
    /// object.name = value
    /// ```
    WriteField {
        /// Name of the field being written.
        field: SmolStr,
        /// Value written to the field.
        value: ValueKey,
        /// Whether table construction definitely created this field.
        definite: bool,
    },
    /// Reads a named field from every table carried by this value.
    ///
    /// ```lua
    /// local value = object.name
    /// ```
    ReadField {
        /// Name of the field being read.
        field: SmolStr,
        /// Value receiving the field contents.
        output: ValueKey,
    },
    /// Writes through a dynamic index on every table carried by this value.
    ///
    /// ```lua
    /// object[index] = value
    /// ```
    WriteIndex {
        /// Value used as the index.
        index: ValueKey,
        /// Value written at the index.
        value: ValueKey,
    },
    /// Reads through a dynamic index from every table carried by this value.
    ///
    /// ```lua
    /// local value = object[index]
    /// ```
    ///
    /// The current engine combines all dynamic table values instead of
    /// tracking each key separately.
    ReadIndex {
        /// Value used as the index.
        index: ValueKey,
        /// Value receiving the table contents.
        output: ValueKey,
    },
    /// Calls this value with an argument pack and a result pack.
    ///
    /// ```lua
    /// local result = function_value(argument)
    /// ```
    Call {
        /// Arguments supplied at the call site.
        args: PackKey,
        /// Results received at the call site.
        returns: PackKey,
    },
    /// Evaluates a binary operation and stores its result.
    ///
    /// ```lua
    /// local result = left + right
    /// ```
    Binary {
        /// Operation being evaluated.
        op: BinOp,
        /// Right-hand value.
        rhs: ValueKey,
        /// Value receiving the result.
        output: ValueKey,
    },
    /// Evaluates a unary operation and stores its result.
    ///
    /// ```lua
    /// local result = -value
    /// ```
    Unary {
        /// Operation being evaluated.
        op: UnOp,
        /// Value receiving the result.
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

    /// Adds a type already known from bytecode for one scalar value.
    pub fn seed(&mut self, key: ValueKey, ty: TypeId) {
        self.seeds.entry(key).or_default().push(ty);
    }

    /// Returns an iterator over scalar relations.
    pub fn value_relations(&self) -> impl Iterator<Item = (ValueKey, &[ValueRelation])> + '_ {
        self.value_relations
            .iter()
            .map(|(key, relations)| (*key, relations.as_slice()))
    }

    /// Returns an iterator over pack relations.
    pub fn pack_relations(&self) -> impl Iterator<Item = (PackKey, &[PackRelation])> + '_ {
        self.pack_relations
            .iter()
            .map(|(key, relations)| (*key, relations.as_slice()))
    }

    /// Returns an iterator over seeded types.
    pub fn seeds(&self) -> impl Iterator<Item = (ValueKey, &[TypeId])> + '_ {
        self.seeds
            .iter()
            .map(|(key, types)| (*key, types.as_slice()))
    }
}
