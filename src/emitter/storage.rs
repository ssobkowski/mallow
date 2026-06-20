use crate::ast::{Expr, Identifier, Literal};

#[derive(Clone)]
pub struct SpillSlot {
    /// Name of the per-function spill table.
    pub table: Identifier,
    /// Numeric index inside the spill table.
    pub slot: usize,
}

pub enum SymbolStorage {
    Named(Identifier),
    Spilled(SpillSlot),
}

impl SymbolStorage {
    pub fn into_expr(self) -> Expr {
        match self {
            SymbolStorage::Named(name) => Expr::Named(name),
            SymbolStorage::Spilled(SpillSlot { table, slot }) => Expr::Index {
                base: Box::new(Expr::Named(table)),
                index: Box::new(Expr::Literal(Literal::Float(slot as f64))),
            },
        }
    }
}
