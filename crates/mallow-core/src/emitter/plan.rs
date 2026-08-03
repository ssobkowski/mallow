use std::collections::{HashMap, HashSet};

use smol_str::SmolStr;

use crate::EmitMode;
use crate::ast::Identifier;
use crate::emitter::locals::LocalPlan;
use crate::emitter::name::NamePlan;
use crate::emitter::storage::{SpillSlot, SymbolStorage};
use crate::hil::StructuredFunction;
use crate::hil::lifter::ssa::{FunctionSymbols, SymbolId};

pub struct FunctionPlan {
    /// Selects source naming or identity-preserving SSA naming.
    emit: EmitMode,
    /// Proto namespace used for identity-preserving SSA names.
    proto_idx: u16,
    /// Owns all emitted identifiers for this function.
    names: NamePlan,
    /// Maps HIL symbols to emitted source-local slots.
    locals: LocalPlan,
    /// Fallback source-local slots allocated for symbols absent from the local
    /// planner, usually from defensive anomaly paths.
    fallback_slots: HashMap<SymbolId, usize>,
    /// Next fallback source-local slot.
    next_fallback_slot: usize,
    /// Symbols that must remain named source locals even if their slot would
    /// otherwise be spillable, such as loop variables.
    forced_named_symbols: HashSet<SymbolId>,
    /// Child upvalues whose parent storage is a spill table access.
    inherited_spills: HashMap<SymbolId, SpillSlot>,
    /// Upvalue slot used by each SSA version of declared upvalue storage.
    ssa_upvalue_slots: HashMap<SymbolId, usize>,
}

impl FunctionPlan {
    /// Builds the storage and name plan for one function.
    pub fn new(fun: &StructuredFunction, emit: EmitMode) -> Self {
        let locals = LocalPlan::build(fun, emit == EmitMode::Source);
        let next_fallback_slot = locals.slot_count();
        let forced_named_symbols =
            identity_named_symbols(fun.symbols.params(), fun.symbols.upvalues());
        let ssa_upvalue_slots = if emit == EmitMode::Ssa {
            collect_ssa_upvalue_slots(&fun.symbols)
        } else {
            HashMap::new()
        };
        let mut plan = Self {
            emit,
            proto_idx: fun.proto.0,
            names: NamePlan::new(),
            locals,
            fallback_slots: HashMap::new(),
            next_fallback_slot,
            forced_named_symbols,
            inherited_spills: HashMap::new(),
            ssa_upvalue_slots,
        };

        if emit == EmitMode::Ssa {
            let mut symbols: Vec<_> = plan
                .locals
                .symbol_slots()
                .into_iter()
                .map(|(symbol, _)| symbol)
                .chain(fun.symbols.params().iter().copied())
                .chain(fun.symbols.upvalues().iter().copied())
                .collect();
            symbols.sort_by_key(|symbol| symbol.index());
            symbols.dedup();
            for symbol in symbols {
                plan.reserve_ssa_symbol_name(symbol);
            }
        }

        plan
    }

    pub fn reserve_symbol_name_exact(&mut self, sym: SymbolId, preferred: SmolStr) -> Identifier {
        match self.emit {
            EmitMode::Ssa => self.reserve_ssa_symbol_name(sym),
            EmitMode::Source => self.names.reserve_symbol_name_exact(sym, preferred),
        }
    }

    pub fn get_symbol_name(&mut self, sym: SymbolId, is_param: bool) -> Identifier {
        match self.emit {
            EmitMode::Ssa => self.reserve_ssa_symbol_name(sym),
            EmitMode::Source => self.names.get_symbol_name(sym, is_param),
        }
    }

    pub fn bind_slot_to_symbol_name(&mut self, slot: usize, sym: SymbolId, is_param: bool) {
        match self.emit {
            EmitMode::Ssa => {
                self.reserve_ssa_symbol_name(sym);
            }
            EmitMode::Source => self.names.bind_slot_to_symbol_name(slot, sym, is_param),
        }
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

        if let Some(&slot) = self.fallback_slots.get(&sym) {
            return slot;
        }

        let slot = self.next_fallback_slot;
        self.next_fallback_slot += 1;
        self.fallback_slots.insert(sym, slot);
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

    /// Returns the declared upvalue slot written by one SSA symbol version.
    pub fn ssa_upvalue_slot(&self, sym: SymbolId) -> Option<usize> {
        self.ssa_upvalue_slots.get(&sym).copied()
    }

    pub fn inherit_named_upvalue(&mut self, child_upvalue_sym: SymbolId, name: Identifier) {
        if self.emit == EmitMode::Ssa {
            self.reserve_ssa_symbol_name(child_upvalue_sym);
            return;
        }
        self.reserve_symbol_name_exact(child_upvalue_sym, name.0);
    }

    pub fn inherit_spilled_upvalue(&mut self, child_upvalue_sym: SymbolId, spill: SpillSlot) {
        if self.emit == EmitMode::Ssa {
            self.reserve_ssa_symbol_name(child_upvalue_sym);
            return;
        }
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
        if self.emit == EmitMode::Ssa {
            return SymbolStorage::Named(self.reserve_ssa_symbol_name(sym));
        }

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

    /// Reserves the identifier derived from one underlying SSA symbol ID.
    fn reserve_ssa_symbol_name(&mut self, sym: SymbolId) -> Identifier {
        self.names
            .reserve_symbol_name_exact(sym, format_ssa_symbol_name(self.proto_idx, sym))
    }

    /// Returns every symbol that currently has an emitted source name.
    pub fn emitted_name_map(&self) -> Vec<(SymbolId, Identifier)> {
        let mut names = Vec::new();
        for (sym, slot) in self
            .locals
            .symbol_slots()
            .into_iter()
            .chain(self.fallback_slots.iter().map(|(&sym, &slot)| (sym, slot)))
        {
            if let Some(name) = self.names.emitted_name_for(sym, slot) {
                names.push((sym, name));
            }
        }

        for (sym, name) in self.names.symbol_names() {
            if !names.iter().any(|(mapped_sym, _)| *mapped_sym == sym) {
                names.push((sym, name));
            }
        }

        names.sort_by_key(|(sym, _)| sym.index());
        names
    }
}

fn identity_named_symbols(params: &[SymbolId], upvalues: &[SymbolId]) -> HashSet<SymbolId> {
    params.iter().chain(upvalues).copied().collect()
}

/// Maps every surviving upvalue symbol back to its declared upvalue slot.
fn collect_ssa_upvalue_slots(symbols: &FunctionSymbols) -> HashMap<SymbolId, usize> {
    let mut slots: HashMap<_, _> = symbols
        .upvalues()
        .iter()
        .copied()
        .enumerate()
        .map(|(slot, symbol)| (symbol, slot))
        .collect();

    for slot in 0..symbols.upvalues().len() {
        for symbol in symbols.for_upvalue(slot) {
            slots.insert(symbol, slot);
        }
    }

    slots
}

/// Formats one SSA symbol with the proto namespace that owns its arena.
pub(crate) fn format_ssa_symbol_name(proto_idx: u16, sym: SymbolId) -> SmolStr {
    format!("p{}_v{}", proto_idx, sym.index()).into()
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

    fn empty_plan() -> FunctionPlan {
        FunctionPlan {
            emit: EmitMode::Source,
            proto_idx: 0,
            names: NamePlan::new(),
            locals: LocalPlan::default(),
            fallback_slots: HashMap::new(),
            next_fallback_slot: 0,
            forced_named_symbols: HashSet::new(),
            inherited_spills: HashMap::new(),
            ssa_upvalue_slots: HashMap::new(),
        }
    }

    /// SSA storage names expose the underlying symbol arena index.
    #[test]
    fn ssa_storage_uses_symbol_id_name() {
        let symbols = symbols(3);
        let symbol = symbols[2];
        let mut plan = FunctionPlan {
            emit: EmitMode::Ssa,
            proto_idx: 7,
            names: NamePlan::new(),
            locals: LocalPlan::default(),
            fallback_slots: HashMap::new(),
            next_fallback_slot: 0,
            forced_named_symbols: HashSet::new(),
            inherited_spills: HashMap::new(),
            ssa_upvalue_slots: HashMap::new(),
        };

        let SymbolStorage::Named(name) = plan.storage_for(symbol, 0, true, 0) else {
            panic!("SSA symbols must remain named")
        };
        assert_eq!(name.as_str(), "p7_v2");
    }

    /// SSA upvalue versions retain their declared slot when earlier slots have no writes.
    #[test]
    fn ssa_upvalue_versions_keep_declared_slot() {
        let mut arena: Arena<Symbol> = Arena::new();
        let first_entry = arena.alloc(Symbol::upval(0));
        let second_entry = arena.alloc(Symbol::upval(1));
        let second_write = arena.alloc(Symbol::upval(1));
        let symbols = FunctionSymbols::new(
            Vec::new(),
            vec![first_entry, second_entry],
            Vec::new(),
            vec![vec![second_entry, second_write]],
            Vec::new(),
            Vec::new(),
        );

        let slots = collect_ssa_upvalue_slots(&symbols);

        assert_eq!(slots.get(&first_entry), Some(&0));
        assert_eq!(slots.get(&second_entry), Some(&1));
        assert_eq!(slots.get(&second_write), Some(&1));
    }

    #[test]
    fn fallback_symbol_reuses_slot_and_slot_name() {
        let symbols = symbols(2);
        let fallback = symbols[0];
        let other_fallback = symbols[1];
        let mut plan = empty_plan();

        let slot = plan.symbol_slot(fallback);
        let name = plan.get_slot_name(slot);

        let repeated_slot = plan.symbol_slot(fallback);
        assert_eq!(repeated_slot, slot);
        assert_eq!(plan.get_slot_name(repeated_slot), name);
        assert_ne!(plan.symbol_slot(other_fallback), slot);
    }

    #[test]
    fn emitted_name_map_reports_slot_name_for_fallback_symbol() {
        let symbols = symbols(1);
        let fallback = symbols[0];
        let mut plan = empty_plan();

        let slot = plan.symbol_slot(fallback);
        let name = plan.get_slot_name(slot);

        assert_eq!(plan.emitted_name_map(), vec![(fallback, name)]);
    }

    #[test]
    fn params_and_upvalues_do_not_spill() {
        let symbols = symbols(3);
        let param = symbols[0];
        let upvalue = symbols[1];
        let ordinary = symbols[2];
        let mut plan = FunctionPlan {
            emit: EmitMode::Source,
            proto_idx: 0,
            names: NamePlan::new(),
            locals: LocalPlan::default(),
            fallback_slots: HashMap::new(),
            next_fallback_slot: 0,
            forced_named_symbols: identity_named_symbols(&[param], &[upvalue]),
            inherited_spills: HashMap::new(),
            ssa_upvalue_slots: HashMap::new(),
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
