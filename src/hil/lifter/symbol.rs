use id_arena::Id;

pub type SymbolId = Id<Symbol>;

#[derive(Debug, Clone)]
pub struct Symbol {
    /// The original register this symbol represents.
    pub reg: u8,
    /// The program counter at the time this symbol was created.
    pub pc: usize,
    /// The mutability type of this symbol.
    pub mutability: Mutability,
}

impl Symbol {
    pub fn new(reg: u8, pc: usize) -> Self {
        Self {
            reg,
            pc,
            mutability: Mutability::Immutable,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mutability {
    /// Never reassigned
    Immutable,
    /// Reassigned at some point
    Mutable,
}
