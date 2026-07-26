//! Stable identities used by SSA inference.

use std::cmp::Ordering;

use crate::{hil::lifter::ssa::SymbolId, il::ProtoId};

/// Stable identity for one scalar value in the inference program.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValueKey {
    /// One SSA symbol in one proto.
    Symbol(ProtoId, SymbolId),
    /// One expression result created while lowering a proto.
    Temp(ProtoId, u32),
    /// One block-local symbol occurrence refined by a branch.
    Occurrence(ProtoId, usize, SymbolId),
}

impl Ord for ValueKey {
    /// Orders value keys by proto, kind, and local identity.
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Symbol(lhs_proto, lhs), Self::Symbol(rhs_proto, rhs)) => {
                (lhs_proto.0, 0u8, lhs.index(), 0usize).cmp(&(rhs_proto.0, 0, rhs.index(), 0))
            }
            (Self::Temp(lhs_proto, lhs), Self::Temp(rhs_proto, rhs)) => {
                (lhs_proto.0, 1u8, *lhs, 0usize).cmp(&(rhs_proto.0, 1, *rhs, 0))
            }
            (
                Self::Occurrence(lhs_proto, lhs_block, lhs),
                Self::Occurrence(rhs_proto, rhs_block, rhs),
            ) => (lhs_proto.0, 2u8, lhs.index(), *lhs_block).cmp(&(
                rhs_proto.0,
                2,
                rhs.index(),
                *rhs_block,
            )),
            (lhs, rhs) => value_kind(lhs).cmp(&value_kind(rhs)),
        }
    }
}

impl PartialOrd for ValueKey {
    /// Delegates partial ordering to the total ordering.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Stable identity for one multivalue pack in the inference program.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PackKey {
    /// Values supplied through one function's vararg parameter.
    VarArgs(ProtoId),
    /// Values returned by one function.
    Returns(ProtoId),
    /// One expression-list or call result created while lowering a proto.
    Temp(ProtoId, u32),
}

impl Ord for PackKey {
    /// Orders pack keys by proto, kind, and local identity.
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::VarArgs(lhs), Self::VarArgs(rhs)) => (lhs.0, 0u8, 0u32).cmp(&(rhs.0, 0, 0)),
            (Self::Returns(lhs), Self::Returns(rhs)) => (lhs.0, 1u8, 0u32).cmp(&(rhs.0, 1, 0)),
            (Self::Temp(lhs_proto, lhs), Self::Temp(rhs_proto, rhs)) => {
                (lhs_proto.0, 2u8, *lhs).cmp(&(rhs_proto.0, 2, *rhs))
            }
            (lhs, rhs) => pack_kind(lhs).cmp(&pack_kind(rhs)),
        }
    }
}

impl PartialOrd for PackKey {
    /// Delegates partial ordering to the total ordering.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Stable identity for one mutable table allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectKey {
    /// Proto containing the allocation.
    pub proto: ProtoId,
    /// Allocation sequence inside the proto.
    pub index: u32,
}

impl Ord for ObjectKey {
    /// Orders object keys by proto and allocation index.
    fn cmp(&self, other: &Self) -> Ordering {
        (self.proto.0, self.index).cmp(&(other.proto.0, other.index))
    }
}

impl PartialOrd for ObjectKey {
    /// Delegates partial ordering to the total ordering.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Branch predicate used by optional occurrence-sensitive lowering.
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

/// Returns the ordering prefix for a value-key variant.
fn value_kind(key: &ValueKey) -> (u16, u8) {
    match key {
        ValueKey::Symbol(proto, _) => (proto.0, 0),
        ValueKey::Temp(proto, _) => (proto.0, 1),
        ValueKey::Occurrence(proto, _, _) => (proto.0, 2),
    }
}

/// Returns the ordering prefix for a pack-key variant.
fn pack_kind(key: &PackKey) -> (u16, u8) {
    match key {
        PackKey::VarArgs(proto) => (proto.0, 0),
        PackKey::Returns(proto) => (proto.0, 1),
        PackKey::Temp(proto, _) => (proto.0, 2),
    }
}
