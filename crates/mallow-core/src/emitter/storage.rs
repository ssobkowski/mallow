use crate::ast::{Expr, Identifier, Literal};

/// Source location used for one NIR binding.
#[derive(Debug, Clone)]
pub(crate) enum Storage {
    /// A regular Luau local.
    Named(Identifier),
    /// One entry in a scope-owned spill table.
    Spilled {
        /// Name of the spill table.
        table: Identifier,
        /// One-based table index.
        index: usize,
    },
}

impl Storage {
    /// Builds an expression that reads or writes this location.
    #[inline]
    #[must_use]
    pub(crate) fn expr(&self) -> Expr {
        match self {
            Self::Named(name) => Expr::Named(name.clone()),
            Self::Spilled { table, index } => Expr::Index {
                base: Box::new(Expr::Named(table.clone())),
                index: Box::new(Expr::Literal(Literal::Float(*index as f64))),
            },
        }
    }

    /// Returns the identifier that must remain visible for this location.
    #[inline]
    pub(crate) fn base_name(&self) -> &Identifier {
        match self {
            Self::Named(name) => name,
            Self::Spilled { table, .. } => table,
        }
    }

    /// Returns the local name when this location is not spilled.
    #[inline]
    pub(crate) fn name(&self) -> Option<&Identifier> {
        match self {
            Self::Named(name) => Some(name),
            Self::Spilled { .. } => None,
        }
    }
}
