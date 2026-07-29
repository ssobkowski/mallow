use crate::{hil::lifter::ssa::SymbolId, scopes::Scopes};

#[derive(Default)]
pub struct DeclarationState {
    /// HIL symbols visible in the current lexical scope stack and their planned
    /// emitted local slots.
    symbols: Scopes<SymbolId, usize>,
    /// Planned slots that already have a Luau declaration in the current scope
    /// stack. Several symbols may share one slot, so this is not redundant with
    /// `symbols`.
    slots: Scopes<usize, ()>,
}

impl DeclarationState {
    pub fn new() -> Self {
        Self {
            symbols: Scopes::new(),
            slots: Scopes::new(),
        }
    }

    pub fn push_scope(&mut self) {
        self.symbols.push_scope();
        self.slots.push_scope();
    }

    pub fn pop_scope(&mut self) {
        self.symbols.pop_scope();
        self.slots.pop_scope();
    }

    pub fn contains_symbol(&self, sym: &SymbolId) -> bool {
        self.symbols.contains(sym)
    }

    pub fn declare_symbol(&mut self, sym: SymbolId, slot: usize) {
        self.symbols.declare(sym, slot);
    }

    pub fn symbol_slot(&self, sym: &SymbolId) -> Option<usize> {
        self.symbols.get(sym).copied()
    }

    pub fn contains_slot(&self, slot: usize) -> bool {
        self.slots.contains(&slot)
    }

    pub fn declare_slot(&mut self, slot: usize) {
        self.slots.declare(slot, ());
    }
}
