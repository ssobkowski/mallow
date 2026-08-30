use std::collections::HashSet;

use smol_str::{SmolStr, format_smolstr};

use crate::ast::Identifier;
use crate::common::is_valid_luau_identifier;
use crate::hil::ir::CellId;
use crate::ir::nir::{Expr, LocalId, PackLocalId};

/// The source role of one emitter binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LocalRole {
    /// A formal function parameter.
    Parameter,
    /// A value produced by a NIR expression.
    Value,
    /// A mutable captured cell.
    Cell,
    /// A value pack that needs source storage.
    Pack,
    /// A numeric or generic loop variable.
    LoopVariable,
}

/// Returns the precedence used when several syntax roles share one identity.
impl LocalRole {
    #[inline]
    pub const fn priority(&self) -> usize {
        match self {
            Self::Parameter => 4,
            Self::LoopVariable => 3,
            Self::Cell => 2,
            Self::Pack => 1,
            Self::Value => 0,
        }
    }
}

/// The NIR identity represented by one source binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LocalSource {
    /// A source-representable NIR local.
    Local(LocalId),
    /// A mutable NIR cell.
    Cell(CellId),
    /// A materialized NIR pack.
    Pack(PackLocalId),
}

/// Read-only information available while suggesting a local name.
#[derive(Clone, Copy)]
pub(crate) struct LocalNameCtx<'a> {
    /// Identity represented by the source binding.
    pub(crate) source: LocalSource,
    /// Source role of the binding.
    pub(crate) role: LocalRole,
    /// Expression that defines the binding, when one exists.
    pub(crate) value: Option<&'a Expr>,
}

/// Suggests readable names for source bindings.
pub(crate) trait Namer {
    /// Suggests one identifier. The allocator makes the result valid and unique.
    fn name(&mut self, ctx: LocalNameCtx<'_>) -> Identifier;
}

/// Provides plain sequential names when no smarter naming policy is installed.
#[derive(Default)]
pub(crate) struct PlainNamer {
    next_parameter: usize,
    next_value: usize,
}

impl Namer for PlainNamer {
    /// Uses separate sequential names for parameters and other values.
    fn name(&mut self, ctx: LocalNameCtx<'_>) -> Identifier {
        let name = if ctx.role == LocalRole::Parameter {
            let index = self.next_parameter;
            self.next_parameter += 1;
            format_smolstr!("p{index}")
        } else {
            let index = self.next_value;
            self.next_value += 1;
            format_smolstr!("v{index}")
        };
        Identifier::new(name)
    }
}

/// Provides names whose suffixes preserve NIR arena identities.
#[derive(Default)]
#[allow(dead_code, reason = "not implemented yet")]
pub(crate) struct ArenaNamer;

impl Namer for ArenaNamer {
    /// Uses the NIR identity and role to build one detailed name.
    fn name(&mut self, ctx: LocalNameCtx<'_>) -> Identifier {
        let name = match (ctx.role, ctx.source) {
            (LocalRole::Parameter, LocalSource::Local(local)) => {
                format_smolstr!("p{}", local.index())
            }
            (LocalRole::Cell, LocalSource::Cell(cell)) => format_smolstr!("c{}", cell.index()),
            (LocalRole::Pack, LocalSource::Pack(pack)) => format_smolstr!("q{}", pack.index()),
            (_, LocalSource::Local(local)) => format_smolstr!("v{}", local.index()),
            (_, LocalSource::Cell(cell)) => format_smolstr!("c{}", cell.index()),
            (_, LocalSource::Pack(pack)) => format_smolstr!("q{}", pack.index()),
        };
        Identifier::new(name)
    }
}

/// Owns the identifier namespace for one emitted function.
pub(crate) struct Names {
    used: HashSet<SmolStr>,
    next_internal: usize,
}

impl Names {
    /// Creates a namespace with names that generated locals must not shadow.
    pub(crate) fn new(reserved: impl IntoIterator<Item = SmolStr>) -> Self {
        Self {
            used: reserved.into_iter().collect(),
            next_internal: 0,
        }
    }

    /// Claims a namer suggestion after validating and uniquifying it.
    pub(crate) fn claim(&mut self, suggested: Identifier) -> Identifier {
        let preferred = if is_valid_luau_identifier(suggested.as_str()) {
            suggested.0
        } else {
            SmolStr::new_static("v")
        };
        self.claim_text(preferred)
    }

    /// Claims an internal name that cannot collide with source-visible names.
    pub(crate) fn internal(&mut self, purpose: &str) -> Identifier {
        loop {
            let candidate = format_smolstr!("__mallow_{purpose}_{}", self.next_internal);
            self.next_internal += 1;
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
        }
    }

    /// Claims one preferred text value.
    fn claim_text(&mut self, preferred: SmolStr) -> Identifier {
        if self.used.insert(preferred.clone()) {
            return Identifier::new(preferred);
        }

        for suffix in 1usize.. {
            let candidate = format_smolstr!("{preferred}_{suffix}");
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
        }

        unreachable!("usize overflowed")
    }
}
