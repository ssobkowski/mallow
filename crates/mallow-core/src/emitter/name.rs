use std::collections::{HashMap, HashSet};

use smol_str::{SmolStr, format_smolstr};

use crate::{ast::Identifier, hil::lifter::ssa::SymbolId};

#[derive(Default)]
pub struct NameAllocator {
    used: HashSet<SmolStr>,
    next_param: usize,
    next_local: usize,
}

impl NameAllocator {
    pub fn reserve_exact(&mut self, preferred: SmolStr) -> Identifier {
        if self.used.insert(preferred.clone()) {
            return Identifier::new(preferred);
        }

        let mut counter = 0usize;
        loop {
            let candidate = format_smolstr!("{preferred}__{counter}");
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
            counter += 1;
        }
    }

    pub fn fresh_param(&mut self) -> Identifier {
        loop {
            let candidate = format_smolstr!("p{}", self.next_param);
            self.next_param += 1;
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
        }
    }

    pub fn fresh_local(&mut self) -> Identifier {
        loop {
            let candidate = format_smolstr!("v{}", self.next_local);
            self.next_local += 1;
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
        }
    }
}

pub struct NamePlan {
    /// Single allocator for every emitted identifier in this function.
    allocator: NameAllocator,
    /// Stable reservations for symbols that need a specific name, such as
    /// params, debug-named closures, and inherited upvalues.
    symbol_names: HashMap<SymbolId, Identifier>,
    /// Names for planned source-local slots. Most ordinary symbol reads go
    /// through this table rather than receiving one name per SSA symbol.
    slot_names: HashMap<usize, Identifier>,
    /// Reserved `_ms` table name when spill-local mode needs table storage.
    spill_table: Option<Identifier>,
}

impl NamePlan {
    pub fn new() -> Self {
        Self {
            allocator: NameAllocator::default(),
            symbol_names: HashMap::new(),
            slot_names: HashMap::new(),
            spill_table: None,
        }
    }

    pub fn reserve_symbol_name_exact(&mut self, sym: SymbolId, preferred: SmolStr) -> Identifier {
        if let Some(name) = self.symbol_names.get(&sym) {
            return name.clone();
        }

        let name = self.allocator.reserve_exact(preferred);
        self.symbol_names.insert(sym, name.clone());
        name
    }

    pub fn get_symbol_name(&mut self, sym: SymbolId, is_param: bool) -> Identifier {
        if let Some(name) = self.symbol_names.get(&sym) {
            return name.clone();
        }

        let name = if is_param {
            self.allocator.fresh_param()
        } else {
            self.allocator.fresh_local()
        };
        self.symbol_names.insert(sym, name.clone());
        name
    }

    pub fn bind_slot_to_symbol_name(&mut self, slot: usize, sym: SymbolId, is_param: bool) {
        if self.slot_names.contains_key(&slot) {
            return;
        }

        let name = self.get_symbol_name(sym, is_param);
        self.slot_names.insert(slot, name);
    }

    pub fn get_slot_name(&mut self, slot: usize) -> Identifier {
        if let Some(name) = self.slot_names.get(&slot) {
            return name.clone();
        }

        let name = self.allocator.fresh_local();
        self.slot_names.insert(slot, name.clone());
        name
    }

    pub fn fresh_temp_local(&mut self) -> Identifier {
        self.allocator.fresh_local()
    }

    pub fn reserve_exact_name(&mut self, name: &Identifier) {
        self.allocator.reserve_exact(name.0.clone());
    }

    pub fn reserve_spill_table(&mut self) -> Identifier {
        if let Some(name) = self.spill_table.clone() {
            return name;
        }

        let name = self.allocator.reserve_exact("_ms".into());
        self.spill_table = Some(name.clone());
        name
    }

    pub fn spill_table(&self) -> Option<Identifier> {
        self.spill_table.clone()
    }

    /// Returns the emitted name currently assigned to a symbol or its slot.
    pub fn emitted_name_for(&self, sym: SymbolId, slot: usize) -> Option<Identifier> {
        self.symbol_names
            .get(&sym)
            .or_else(|| self.slot_names.get(&slot))
            .cloned()
    }

    /// Returns every symbol with a directly reserved emitted name.
    pub fn symbol_names(&self) -> Vec<(SymbolId, Identifier)> {
        let mut names: Vec<_> = self
            .symbol_names
            .iter()
            .map(|(&sym, name)| (sym, name.clone()))
            .collect();
        names.sort_by_key(|(sym, _)| sym.index());
        names
    }
}
