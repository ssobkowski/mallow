//! Stable constraints produced directly from FIR.

use std::collections::HashSet;

use super::keys::{BranchPredicate, ObjectKey, PackKey, ValueKey};
use crate::il::ProtoId;
use crate::operator::{BinOp, UnOp};
use crate::ty::canonical::TypeId;

/// An inference constraint.
#[derive(Debug, Clone, PartialEq)]
pub enum Constraint<V, P, O> {
    /// The value produces a type.
    Produce {
        /// Value producing the type.
        value: V,
        /// Produced type.
        ty: TypeId,
    },
    /// The value requires a type.
    Require {
        /// Value that must support the type.
        value: V,
        /// Required type.
        ty: TypeId,
    },
    /// Sends type and identity facts from a value to another.
    Flow {
        /// Value providing facts.
        source: V,
        /// Value receiving facts.
        target: V,
    },
    /// Sends produced facts except `nil` from a value to another.
    NonNilFlow {
        /// Value providing facts.
        source: V,
        /// Value receiving facts.
        target: V,
    },
    /// Sends a branch-specific part of a value to an occurrence.
    Filter {
        /// Value tested by the branch.
        source: V,
        /// Value used inside the branch.
        target: V,
        /// Branch test to apply.
        predicate: BranchPredicate,
    },
    /// Adds a table allocation to a value.
    IncludeObject {
        /// Value carrying the table.
        value: V,
        /// Table allocation identity.
        object: O,
    },
    /// Adds a closure to a value.
    IncludeClosure {
        /// Value carrying the closure.
        value: V,
        /// Lifted closure proto.
        proto: ProtoId,
    },
    /// Keeps a value equal to a pack position.
    ProjectPack {
        /// Pack being read.
        pack: P,
        /// Zero-based position being read.
        index: usize,
        /// Value receiving the position.
        output: V,
    },
    /// Adds a sequence alternative to a pack.
    Sequence {
        /// Pack receiving the alternative.
        pack: P,
        /// Values guaranteed at the start of the alternative.
        head: Vec<V>,
        /// Remaining sequence, or `None` when the alternative ends.
        tail: Option<P>,
    },
    /// Sends every source alternative after an offset to a target pack.
    SlicePack {
        /// Pack providing alternatives.
        source: P,
        /// Number of leading positions to skip.
        offset: usize,
        /// Pack receiving the suffix alternatives.
        target: P,
    },
    /// Writes through a key on every table carried by a value.
    SetTable {
        /// Value carrying the tables.
        table: V,
        /// Value used as the key.
        key: V,
        /// Value written at the key.
        value: V,
    },
    /// Writes a pack into the array part of every table carried by a value.
    WriteList {
        /// Value carrying the tables.
        table: V,
        /// Pack carrying the values.
        values: P,
    },
    /// Reads through a key from every table carried by a value.
    GetTable {
        /// Value carrying the tables.
        table: V,
        /// Value used as the key.
        key: V,
        /// Value receiving the table contents.
        output: V,
    },
    /// Calls a value with an argument and result pack.
    Call {
        /// Value being called.
        callee: V,
        /// Arguments supplied at the call site.
        args: P,
        /// Results received at the call site.
        returns: P,
    },
    /// Applies a binary operation.
    Binary {
        /// Left-hand value.
        lhs: V,
        /// Operation being evaluated.
        op: BinOp,
        /// Right-hand value.
        rhs: V,
        /// Value receiving the result.
        output: V,
    },
    /// Applies a unary operation.
    Unary {
        /// Value being operated on.
        operand: V,
        /// Operation being evaluated.
        op: UnOp,
        /// Value receiving the result.
        output: V,
    },
}

pub type ProgramConstraint = Constraint<ValueKey, PackKey, ObjectKey>;

#[derive(Debug, Default)]
pub struct InferenceProgram {
    values: HashSet<ValueKey>,
    packs: HashSet<PackKey>,
    constraints: Vec<ProgramConstraint>,
}

impl InferenceProgram {
    /// Ensures a scalar value exists even when it has no constraint yet.
    pub fn touch_value(&mut self, key: ValueKey) {
        self.values.insert(key);
    }

    /// Ensures a pack exists even when it has no constraint yet.
    pub fn touch_pack(&mut self, key: PackKey) {
        self.packs.insert(key);
    }

    /// Adds a inference constraint.
    pub fn push(&mut self, constraint: ProgramConstraint) {
        self.constraints.push(constraint);
    }

    /// Adds an exact type supplied by bytecode metadata.
    pub fn seed(&mut self, value: ValueKey, ty: TypeId) {
        self.push(Constraint::Produce {
            value: value.clone(),
            ty,
        });
        self.push(Constraint::Require { value, ty });
    }

    /// Returns all scalar identities owned by the program.
    pub fn values(&self) -> impl Iterator<Item = &ValueKey> {
        self.values.iter()
    }

    /// Returns all pack identities owned by the program.
    pub fn packs(&self) -> impl Iterator<Item = PackKey> + '_ {
        self.packs.iter().copied()
    }

    /// Consumes the program and returns its constraints.
    pub fn into_constraints(self) -> impl Iterator<Item = ProgramConstraint> {
        self.constraints.into_iter()
    }
}
