//! Collected inference program and source-level generic evidence.

use std::collections::HashMap;

use smol_str::SmolStr;

use crate::{
    hil::{lifted::LiftedFunction, lifter::ssa::SymbolId, ty2::canonical::TypeId},
    il::ProtoId,
    operator::{BinOp, UnOp},
};

use crate::hil::ty2::builtins::BuiltinPath;

/// Durable key for an inference variable discovered while collecting HIL.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeSlot {
    /// One SSA symbol in one proto.
    Symbol(ProtoId, SymbolId),
    /// One expression result without a durable HIL symbol.
    Synthetic(ProtoId, u32),
    /// One block-local occurrence narrowed by an incoming branch edge.
    Refined(ProtoId, usize, SymbolId),
}

/// Durable identity for one inference-time value pack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum PackSlot {
    /// Values supplied through one function's vararg parameter.
    VarArgs(ProtoId),
    /// Values returned by one function.
    Returns(ProtoId),
    /// One expression-list or call result without a durable HIL identity.
    Synthetic(ProtoId, u32),
}

/// Identity assigned to a table allocation during collection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct TableKey {
    /// Proto containing the allocation.
    pub(super) proto: ProtoId,
    /// Allocation sequence number within the proto.
    pub(super) index: u32,
}

/// Truthiness restriction carried by a CFG edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Truthiness {
    /// Values reaching the edge exclude `nil` and `false`.
    Truthy,
    /// Values reaching the edge are restricted to `nil | false`.
    Falsy,
}

impl std::ops::Not for Truthiness {
    type Output = Self;

    /// Returns the complementary branch restriction.
    fn not(self) -> Self::Output {
        match self {
            Self::Truthy => Self::Falsy,
            Self::Falsy => Self::Truthy,
        }
    }
}

/// One collected relation between HIL values.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum CollectedConstraint {
    /// The value has this exact type.
    Concrete(TypeId),
    /// The value comes from another slot.
    From(TypeSlot),
    /// Two slots hold the same value.
    Equal(TypeSlot),
    /// The value is one positional projection from a value pack.
    FromPack {
        /// Pack being projected.
        pack: PackSlot,
        /// Zero-based value position.
        index: usize,
    },
    /// The value is `source`, narrowed by a truthiness check.
    Narrowed {
        /// Slot before narrowing.
        source: TypeSlot,
        /// Which branch narrowed it (truthy or falsy).
        truthiness: Truthiness,
    },
    /// The constrained expression allocates one mutable table object.
    NewTable(TableKey),
    /// A table-like value receives an indexed write.
    SetIndex {
        /// Slot containing the index.
        index: TypeSlot,
        /// Slot containing the written value.
        value: TypeSlot,
    },
    /// A table-like value receives every concrete value produced by a pack.
    SetIndexPack {
        /// Pack whose produced elements are written at numeric indices.
        values: PackSlot,
    },
    /// A table-like value performs an indexed read.
    GetIndex {
        /// Slot containing the index.
        index: TypeSlot,
        /// Slot receiving the read value.
        value: TypeSlot,
    },
    /// A table-like value receives a named-field write.
    SetField {
        /// Field selected by the write.
        field: SmolStr,
        /// Slot containing the written value.
        value: TypeSlot,
        /// Whether the field is initialized by the table constructor itself.
        definite: bool,
    },
    /// A table-like value performs a named-field read.
    GetField {
        /// Field selected by the read.
        field: SmolStr,
        /// Slot receiving the read value.
        value: TypeSlot,
    },
    /// A binary operation relates two operands and one result.
    Binary {
        /// Operation performed by the expression.
        op: BinOp,
        /// Right operand slot.
        rhs: TypeSlot,
        /// Result slot.
        result: TypeSlot,
    },
    /// A unary operation relates one operand and one result.
    Unary {
        /// Operation performed by the expression.
        op: UnOp,
        /// Result slot.
        result: TypeSlot,
    },
    /// A callable value is invoked with argument and result packs.
    Call {
        /// Pack containing every supplied argument.
        args: PackSlot,
        /// Pack receiving every produced result.
        returns: PackSlot,
    },
    /// Calls a field while preserving same-table field correlations.
    FieldCall {
        /// Field containing the callable value.
        callee: SmolStr,
        /// Fixed argument prefix, including same-table field provenance.
        head: Vec<CollectedCallArgument>,
        /// Optional remaining argument pack.
        tail: Option<PackSlot>,
        /// Pack receiving every produced result.
        returns: PackSlot,
    },
    /// The constrained value is a closure for this proto.
    Closure(ProtoId),
    /// The constrained value denotes one builtin type scheme.
    Builtin(BuiltinPath),
}

/// One argument to a table-field call before solver lowering.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum CollectedCallArgument {
    /// An independently collected expression value.
    Value(TypeSlot),
    /// A named field read from the same object as the callee field.
    Field(SmolStr),
}

/// One producer relation for an inference-time value pack.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum CollectedPackConstraint {
    /// A fixed prefix followed by an optional remaining pack.
    Sequence {
        /// Values guaranteed at the start of this alternative.
        head: Vec<TypeSlot>,
        /// Remaining values, or `None` when this alternative ends after `head`.
        tail: Option<PackSlot>,
    },
}

/// Mutable constraint output for one lifted function.
///
/// This value owns proto-local identity allocation while collection is in
/// progress. Inserting it into [`CollectedProgram`] retains only solver-visible
/// constraints and metadata.
#[derive(Debug)]
pub(super) struct CollectedFunction {
    /// Proto whose HIL is being collected.
    proto: ProtoId,
    /// Constraints grouped by their primary slot.
    constraints: HashMap<TypeSlot, Vec<CollectedConstraint>>,
    /// Pack constraints grouped by their produced pack.
    pack_constraints: HashMap<PackSlot, Vec<CollectedPackConstraint>>,
    /// Relational field calls suitable for generic signature recovery.
    generic_field_calls: Vec<GenericFieldCall>,
    /// Next proto-local synthetic slot number.
    next_synthetic_slot: u32,
    /// Next proto-local synthetic pack number.
    next_synthetic_pack: u32,
    /// Next proto-local table allocation number.
    next_table_key: u32,
}

/// Constraints and return-pack metadata collected across all protos.
#[derive(Debug, Default)]
pub(super) struct CollectedProgram {
    /// Constraints grouped by their primary slot.
    pub(super) constraints: HashMap<TypeSlot, Vec<CollectedConstraint>>,
    /// Pack constraints grouped by their durable identity.
    pub(super) pack_constraints: HashMap<PackSlot, Vec<CollectedPackConstraint>>,
    /// Relational field calls that can be expressed as source-level generics.
    pub(super) generic_field_calls: HashMap<ProtoId, Vec<GenericFieldCall>>,
}

/// A same-table field relationship suitable for generic signature recovery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GenericFieldCall {
    /// Function parameter containing the related fields.
    pub(super) parameter: SymbolId,
    /// Field invoked as the callback.
    pub(super) callee: SmolStr,
    /// Callback argument positions sourced from fields of the same table.
    pub(super) field_arguments: Vec<(usize, SmolStr)>,
    /// Fixed callback results consumed, or `None` for an open result context.
    pub(super) return_count: Option<usize>,
}

impl CollectedFunction {
    /// Creates output with the storage constraints for one lifted function.
    pub(super) fn from_function(function: &LiftedFunction) -> Self {
        let mut output = Self::new(function.proto);
        output.return_pack();
        if function.is_vararg {
            output.vararg_pack();
        }
        for versions in function.symbols.storage_version_groups() {
            let Some((&first, rest)) = versions.split_first() else {
                continue;
            };
            let first = output.symbol_slot(first);
            for &version in rest {
                let version = output.symbol_slot(version);
                output.push(first, CollectedConstraint::Equal(version));
            }
        }
        output
    }

    /// Creates empty output for one proto.
    pub(super) fn new(proto: ProtoId) -> Self {
        Self {
            proto,
            constraints: HashMap::new(),
            pack_constraints: HashMap::new(),
            generic_field_calls: Vec::new(),
            next_synthetic_slot: 0,
            next_synthetic_pack: 0,
            next_table_key: 0,
        }
    }

    /// Allocates and registers one proto-local synthetic value slot.
    pub(super) fn synthetic_slot(&mut self) -> TypeSlot {
        let slot = TypeSlot::Synthetic(self.proto, self.next_synthetic_slot);
        self.next_synthetic_slot = self
            .next_synthetic_slot
            .checked_add(1)
            .expect("one proto exhausted synthetic type-slot IDs");
        self.ensure_slot(slot);
        slot
    }

    /// Allocates and registers one proto-local synthetic value pack.
    pub(super) fn synthetic_pack(&mut self) -> PackSlot {
        let slot = PackSlot::Synthetic(self.proto, self.next_synthetic_pack);
        self.next_synthetic_pack = self
            .next_synthetic_pack
            .checked_add(1)
            .expect("one proto exhausted synthetic pack IDs");
        self.ensure_pack(slot);
        slot
    }

    /// Returns and registers this function's incoming vararg pack.
    pub(super) fn vararg_pack(&mut self) -> PackSlot {
        let slot = PackSlot::VarArgs(self.proto);
        self.ensure_pack(slot);
        slot
    }

    /// Returns and registers this function's result pack.
    pub(super) fn return_pack(&mut self) -> PackSlot {
        let slot = PackSlot::Returns(self.proto);
        self.ensure_pack(slot);
        slot
    }

    /// Allocates one proto-local table identity.
    pub(super) fn table_key(&mut self) -> TableKey {
        let key = TableKey {
            proto: self.proto,
            index: self.next_table_key,
        };
        self.next_table_key = self
            .next_table_key
            .checked_add(1)
            .expect("one proto exhausted inferred table IDs");
        key
    }

    /// Returns and registers the definition slot for one local symbol.
    pub(super) fn symbol_slot(&mut self, symbol: SymbolId) -> TypeSlot {
        let slot = TypeSlot::Symbol(self.proto, symbol);
        self.ensure_slot(slot);
        slot
    }

    /// Returns a refined occurrence slot and records its source relation.
    pub(super) fn refined_symbol_slot(
        &mut self,
        block_index: usize,
        symbol: SymbolId,
        truthiness: Truthiness,
    ) -> TypeSlot {
        let source = self.symbol_slot(symbol);
        let occurrence = TypeSlot::Refined(self.proto, block_index, symbol);
        self.push(
            occurrence,
            CollectedConstraint::Narrowed { source, truthiness },
        );
        occurrence
    }

    /// Records one generic field-call shape unless it was already observed.
    pub(super) fn record_generic_field_call(&mut self, call: GenericFieldCall) {
        if !self.generic_field_calls.contains(&call) {
            self.generic_field_calls.push(call);
        }
    }

    /// Ensures that `slot` participates in solver construction.
    fn ensure_slot(&mut self, slot: TypeSlot) {
        self.constraints.entry(slot).or_default();
    }

    /// Ensures that `slot` participates in pack solver construction.
    fn ensure_pack(&mut self, slot: PackSlot) {
        self.pack_constraints.entry(slot).or_default();
    }

    /// Adds one pack producer unless the same relation was already collected.
    pub(super) fn push_pack(&mut self, slot: PackSlot, constraint: CollectedPackConstraint) {
        let constraints = self.pack_constraints.entry(slot).or_default();
        if !constraints.contains(&constraint) {
            constraints.push(constraint);
        }
    }

    /// Adds a constraint unless the same relation was already collected.
    pub(super) fn push(&mut self, slot: TypeSlot, constraint: CollectedConstraint) {
        let constraints = self.constraints.entry(slot).or_default();
        if !constraints.contains(&constraint) {
            constraints.push(constraint);
        }
    }
}

impl CollectedProgram {
    /// Inserts one fully collected function into the whole-program graph.
    pub(super) fn insert_function(&mut self, function: CollectedFunction) {
        let CollectedFunction {
            proto,
            constraints,
            pack_constraints,
            generic_field_calls,
            ..
        } = function;

        assert!(
            !self
                .pack_constraints
                .contains_key(&PackSlot::Returns(proto)),
            "each proto must be collected exactly once"
        );
        for (slot, constraints) in constraints {
            let previous = self.constraints.insert(slot, constraints);
            assert!(
                previous.is_none(),
                "proto-local constraint slots must not overlap"
            );
        }
        for (slot, constraints) in pack_constraints {
            let previous = self.pack_constraints.insert(slot, constraints);
            assert!(
                previous.is_none(),
                "proto-local pack slots must not overlap"
            );
        }
        if !generic_field_calls.is_empty() {
            self.generic_field_calls.insert(proto, generic_field_calls);
        }
    }
}
