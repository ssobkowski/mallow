//! Stable identities used by FIR inference.

use std::cmp::Ordering;

use smol_str::SmolStr;

use crate::il::ProtoId;
use crate::ir::fir::{CellId, PackId, ValueId};

/// Stable identity for one scalar value in the inference program.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueKey {
    /// One immutable FIR value in one proto.
    Value(ProtoId, ValueId),
    /// One mutable FIR cell in one proto.
    Cell(ProtoId, CellId),
    /// One mutable global binding shared by all protos.
    Global(SmolStr),
    /// One scalar needed to describe a fused FIR operation.
    Synthetic(ProtoId, u32),
    /// One block-local use of an immutable value refined by a branch.
    Occurrence(ProtoId, usize, ValueId),
}

impl Ord for ValueKey {
    fn cmp(&self, other: &Self) -> Ordering {
        let kind = value_kind(self).cmp(&value_kind(other));
        if kind != Ordering::Equal {
            return kind;
        }

        match (self, other) {
            (Self::Value(lhs_proto, lhs), Self::Value(rhs_proto, rhs)) => {
                (lhs_proto.0, lhs.index()).cmp(&(rhs_proto.0, rhs.index()))
            }
            (Self::Cell(lhs_proto, lhs), Self::Cell(rhs_proto, rhs)) => {
                (lhs_proto.0, lhs.index()).cmp(&(rhs_proto.0, rhs.index()))
            }
            (Self::Global(lhs), Self::Global(rhs)) => lhs.cmp(rhs),
            (Self::Synthetic(lhs_proto, lhs), Self::Synthetic(rhs_proto, rhs)) => {
                (lhs_proto.0, lhs).cmp(&(rhs_proto.0, rhs))
            }
            (
                Self::Occurrence(lhs_proto, lhs_block, lhs),
                Self::Occurrence(rhs_proto, rhs_block, rhs),
            ) => (lhs_proto.0, lhs_block, lhs.index()).cmp(&(rhs_proto.0, rhs_block, rhs.index())),
            _ => unreachable!("equal value-key kinds must use the same variant"),
        }
    }
}

impl PartialOrd for ValueKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Stable identity for one multivalue pack in the inference program.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PackKey {
    /// One FIR pack in one proto.
    Pack(ProtoId, PackId),
    /// Values supplied through one function's variadic parameter.
    VarArgs(ProtoId),
    /// Values returned by one function.
    Returns(ProtoId),
    /// One pack needed to describe a fused FIR operation.
    Synthetic(ProtoId, u32),
}

impl Ord for PackKey {
    fn cmp(&self, other: &Self) -> Ordering {
        let kind = pack_kind(*self).cmp(&pack_kind(*other));
        if kind != Ordering::Equal {
            return kind;
        }

        match (*self, *other) {
            (Self::Pack(lhs_proto, lhs), Self::Pack(rhs_proto, rhs)) => {
                (lhs_proto.0, lhs.index()).cmp(&(rhs_proto.0, rhs.index()))
            }
            (Self::VarArgs(lhs), Self::VarArgs(rhs)) | (Self::Returns(lhs), Self::Returns(rhs)) => {
                lhs.0.cmp(&rhs.0)
            }
            (Self::Synthetic(lhs_proto, lhs), Self::Synthetic(rhs_proto, rhs)) => {
                (lhs_proto.0, lhs).cmp(&(rhs_proto.0, rhs))
            }
            _ => unreachable!("equal pack-key kinds must use the same variant"),
        }
    }
}

impl PartialOrd for PackKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Stable identity for one mutable table allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectKey {
    /// Proto containing the allocation.
    pub proto: ProtoId,
    /// FIR value produced by the allocation.
    pub value: ValueId,
}

impl Ord for ObjectKey {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.proto.0, self.value.index()).cmp(&(other.proto.0, other.value.index()))
    }
}

impl PartialOrd for ObjectKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Branch predicate used by occurrence-sensitive lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BranchPredicate {
    /// Values on this edge exclude `nil` and `false`.
    Truthy,
    /// Values on this edge are restricted to `nil | false`.
    Falsy,
}

impl std::ops::Not for BranchPredicate {
    type Output = Self;

    /// Returns the opposite predicate for the other branch.
    fn not(self) -> Self::Output {
        match self {
            Self::Truthy => Self::Falsy,
            Self::Falsy => Self::Truthy,
        }
    }
}

/// Returns the ordering rank for a value-key variant.
const fn value_kind(key: &ValueKey) -> u8 {
    match key {
        ValueKey::Value(_, _) => 0,
        ValueKey::Cell(_, _) => 1,
        ValueKey::Global(_) => 2,
        ValueKey::Synthetic(_, _) => 3,
        ValueKey::Occurrence(_, _, _) => 4,
    }
}

/// Returns the ordering rank for a pack-key variant.
const fn pack_kind(key: PackKey) -> u8 {
    match key {
        PackKey::Pack(_, _) => 0,
        PackKey::VarArgs(_) => 1,
        PackKey::Returns(_) => 2,
        PackKey::Synthetic(_, _) => 3,
    }
}
