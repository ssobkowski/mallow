use std::collections::{HashMap, HashSet};

use smol_str::SmolStr;

use crate::{
    ast::Identifier,
    emitter::{
        locals::LocalPlan,
        name::NamePlan,
        storage::{SpillSlot, SymbolStorage},
    },
    hil::{StructuredFunction, lifter::ssa::SymbolId},
};

pub struct FunctionPlan {
    /// Owns all emitted identifiers for this function.
    names: NamePlan,
    /// Maps HIL symbols to emitted source-local slots.
    locals: LocalPlan,
    /// Slots for symbols that were not mentioned by the local planner but are
    /// discovered during lowering, usually from defensive anomaly paths.
    next_fallback_slot: usize,
    /// Symbols that must remain named source locals even if their slot would
    /// otherwise be spillable, such as loop variables.
    forced_named_symbols: HashSet<SymbolId>,
    /// Child upvalues whose parent storage is a spill table access.
    inherited_spills: HashMap<SymbolId, SpillSlot>,
}

impl FunctionPlan {
    pub fn new(fun: &StructuredFunction) -> Self {
        let locals = LocalPlan::build(fun);
        let next_fallback_slot = locals.slot_count();
        let forced_named_symbols = identity_named_symbols(&fun.params, &fun.upvalues);
        Self {
            names: NamePlan::new(),
            locals,
            next_fallback_slot,
            forced_named_symbols,
            inherited_spills: HashMap::new(),
        }
    }

    pub fn reserve_symbol_name_exact(&mut self, sym: SymbolId, preferred: SmolStr) -> Identifier {
        self.names.reserve_symbol_name_exact(sym, preferred)
    }

    pub fn get_symbol_name(&mut self, sym: SymbolId, is_param: bool) -> Identifier {
        self.names.get_symbol_name(sym, is_param)
    }

    pub fn bind_slot_to_symbol_name(&mut self, slot: usize, sym: SymbolId, is_param: bool) {
        self.names.bind_slot_to_symbol_name(slot, sym, is_param);
    }

    pub fn get_slot_name(&mut self, slot: usize) -> Identifier {
        self.names.get_slot_name(slot)
    }

    pub fn fresh_temp_local(&mut self) -> Identifier {
        self.names.fresh_temp_local()
    }

    pub fn symbol_slot(&mut self, sym: SymbolId) -> usize {
        if let Some(slot) = self.locals.slot(sym) {
            return slot;
        }

        let slot = self.next_fallback_slot;
        self.next_fallback_slot += 1;
        slot
    }

    pub fn force_named_symbol(&mut self, sym: SymbolId) {
        self.forced_named_symbols.insert(sym);
    }

    pub fn inherited_storage(&self, sym: SymbolId) -> Option<SymbolStorage> {
        self.inherited_spills
            .get(&sym)
            .cloned()
            .map(SymbolStorage::Spilled)
    }

    pub fn inherit_named_upvalue(&mut self, child_upvalue_sym: SymbolId, name: Identifier) {
        self.reserve_symbol_name_exact(child_upvalue_sym, name.0);
    }

    pub fn inherit_spilled_upvalue(&mut self, child_upvalue_sym: SymbolId, spill: SpillSlot) {
        self.names.reserve_exact_name(&spill.table);
        self.inherited_spills.insert(child_upvalue_sym, spill);
    }

    pub fn storage_for(
        &mut self,
        sym: SymbolId,
        slot: usize,
        spill_locals: bool,
        max_local_count: usize,
    ) -> SymbolStorage {
        if spill_locals && slot >= max_local_count && !self.forced_named_symbols.contains(&sym) {
            return SymbolStorage::Spilled(SpillSlot {
                table: self.reserve_spill_table(),
                slot,
            });
        }

        SymbolStorage::Named(self.get_slot_name(slot))
    }

    pub fn spill_table(&self) -> Option<Identifier> {
        self.names.spill_table()
    }

    fn reserve_spill_table(&mut self) -> Identifier {
        self.names.reserve_spill_table()
    }
}

fn identity_named_symbols(params: &[SymbolId], upvalues: &[SymbolId]) -> HashSet<SymbolId> {
    params.iter().chain(upvalues).copied().collect()
}

#[cfg(test)]
mod tests {
    use id_arena::Arena;

    use super::*;
    use crate::hil::lifter::ssa::Symbol;

    fn symbols(count: usize) -> Vec<SymbolId> {
        let mut arena: Arena<Symbol> = Arena::new();
        let mut symbols = Vec::new();
        for _ in 0..count {
            symbols.push(arena.alloc(Symbol::reg(0)));
        }
        symbols
    }

    #[test]
    fn params_and_upvalues_do_not_spill() {
        let symbols = symbols(3);
        let param = symbols[0];
        let upvalue = symbols[1];
        let ordinary = symbols[2];
        let mut plan = FunctionPlan {
            names: NamePlan::new(),
            locals: LocalPlan::default(),
            next_fallback_slot: 0,
            forced_named_symbols: identity_named_symbols(&[param], &[upvalue]),
            inherited_spills: HashMap::new(),
        };

        let param_storage = plan.storage_for(param, 250, true, 199);
        let upvalue_storage = plan.storage_for(upvalue, 251, true, 199);
        let ordinary_storage = plan.storage_for(ordinary, 252, true, 199);

        assert!(matches!(param_storage, SymbolStorage::Named(_)));
        assert!(matches!(upvalue_storage, SymbolStorage::Named(_)));
        assert!(matches!(ordinary_storage, SymbolStorage::Spilled(_)));
        assert!(plan.spill_table().is_some());
    }
}
