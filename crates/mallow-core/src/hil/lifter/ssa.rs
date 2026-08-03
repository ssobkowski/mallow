use std::collections::{BTreeSet, HashMap};

use id_arena::{Arena, Id};

use crate::hil::cflow::cfg::Block;
use crate::hil::cflow::graph::GraphView;
use crate::hil::ir::{PhiNode, Stmt};
use crate::hil::ty::canonical::TypeId;

pub type SymbolId = Id<Symbol>;

#[derive(Debug, Clone)]
pub struct Symbol {
    /// The original storage role this symbol represents.
    pub kind: SymbolKind,
    /// Bytecode-provided type fact for this symbol, if one was available.
    pub ty: Option<TypeId>,
    /// Index of the active debug-local record, if debug information was present.
    pub local_index: Option<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Register(u8),
    CapturedRegister { reg: u8, generation: u16 },
    Upvalue(u8),
    Param(u8),
}

/// One named local and its SSA symbols.
#[derive(Debug, Clone)]
pub(crate) struct NamedLocal {
    /// Name stored in Luau debug information.
    pub(crate) name: String,
    /// First bytecode PC covered by the local.
    pub(crate) start_pc: u32,
    /// First bytecode PC after the local's lifetime.
    pub(crate) end_pc: u32,
    /// SSA symbols associated with this local.
    pub(crate) symbols: Vec<SymbolId>,
}

/// Stores the symbols and storage links found while building SSA.
#[derive(Debug, Clone)]
pub(crate) struct FunctionSymbols {
    /// Entry symbol for each formal parameter, in parameter order.
    params: Vec<SymbolId>,
    /// Entry symbol for each declared upvalue slot, in slot order.
    upvalues: Vec<SymbolId>,
    /// Named locals recovered from Luau debug information.
    debug_locals: Vec<NamedLocal>,
    /// Symbols that share one declared upvalue storage location.
    upvalue_storage: Vec<Vec<SymbolId>>,
    /// Symbols that share one captured register storage location.
    captured_storage: Vec<Vec<SymbolId>>,
    /// Pairs of symbols that represent one loop-carried local.
    loop_carried_links: Vec<(SymbolId, SymbolId)>,
}

impl FunctionSymbols {
    /// Creates the symbol metadata for one lifted function.
    pub(crate) fn new(
        params: Vec<SymbolId>,
        upvalues: Vec<SymbolId>,
        debug_locals: Vec<NamedLocal>,
        upvalue_storage: Vec<Vec<SymbolId>>,
        captured_storage: Vec<Vec<SymbolId>>,
        loop_carried_links: Vec<(SymbolId, SymbolId)>,
    ) -> Self {
        Self {
            params,
            upvalues,
            debug_locals,
            upvalue_storage,
            captured_storage,
            loop_carried_links,
        }
    }

    /// Returns the entry symbol for each formal parameter, in parameter order.
    pub(crate) fn params(&self) -> &[SymbolId] {
        &self.params
    }

    /// Returns mutable parameter symbols for SSA canonicalization.
    pub(crate) fn params_mut(&mut self) -> &mut [SymbolId] {
        &mut self.params
    }

    /// Returns the entry symbol for each declared upvalue slot, in slot order.
    pub(crate) fn upvalues(&self) -> &[SymbolId] {
        &self.upvalues
    }

    /// Returns mutable upvalue symbols for SSA canonicalization.
    pub(crate) fn upvalues_mut(&mut self) -> &mut [SymbolId] {
        &mut self.upvalues
    }

    /// Returns named locals recovered from Luau debug information.
    pub(crate) fn debug_locals(&self) -> &[NamedLocal] {
        &self.debug_locals
    }

    /// Returns mutable debug locals for SSA canonicalization.
    pub(crate) fn debug_locals_mut(&mut self) -> &mut [NamedLocal] {
        &mut self.debug_locals
    }

    /// Returns the declared upvalue slot containing `symbol`.
    pub(crate) fn slot_for_upvalue(&self, symbol: SymbolId) -> Option<usize> {
        self.upvalues
            .iter()
            .position(|&entry| entry == symbol)
            .or_else(|| {
                self.upvalue_storage
                    .iter()
                    .find(|symbols| symbols.contains(&symbol))
                    .and_then(|symbols| {
                        self.upvalues
                            .iter()
                            .position(|entry| symbols.contains(entry))
                    })
            })
    }

    /// Returns every symbol that uses one declared upvalue's storage.
    pub(crate) fn for_upvalue(&self, slot: usize) -> impl Iterator<Item = SymbolId> + '_ {
        let entry = *self
            .upvalues
            .get(slot)
            .expect("upvalue slot must index a declared upvalue");
        let storage = self
            .upvalue_storage
            .iter()
            .find(|symbols| symbols.contains(&entry));
        let members = storage
            .into_iter()
            .flat_map(|symbols| symbols.iter().copied());
        let fallback = storage.is_none().then_some(entry);
        members.chain(fallback)
    }

    /// Returns every symbol in captured storage with multiple surviving symbols.
    pub(crate) fn captured_storage_symbols(&self) -> impl Iterator<Item = SymbolId> + '_ {
        self.captured_storage.iter().flatten().copied()
    }

    /// Returns pairs of symbols that must use the same storage.
    pub(crate) fn same_storage_links(&self) -> impl Iterator<Item = (SymbolId, SymbolId)> + '_ {
        self.upvalue_storage
            .iter()
            .chain(&self.captured_storage)
            .flat_map(|symbols| {
                let mut symbols = symbols.iter().copied();
                let first = symbols.next();
                symbols.filter_map(move |symbol| first.map(|first| (first, symbol)))
            })
    }

    /// Takes the symbol lists for shared storage locations.
    pub(crate) fn take_storage_members(&mut self) -> impl Iterator<Item = Vec<SymbolId>> {
        std::mem::take(&mut self.upvalue_storage)
            .into_iter()
            .chain(std::mem::take(&mut self.captured_storage))
    }

    /// Takes the pairs of symbols that represent loop-carried locals.
    pub(crate) fn take_loop_carried_links(&mut self) -> impl Iterator<Item = (SymbolId, SymbolId)> {
        std::mem::take(&mut self.loop_carried_links).into_iter()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SsaVar {
    Reg(u8),
    Upval(u8),
}

impl From<SsaVar> for Symbol {
    fn from(var: SsaVar) -> Self {
        match var {
            SsaVar::Reg(r) => Symbol::reg(r),
            SsaVar::Upval(u) => Symbol::upval(u),
        }
    }
}

impl Symbol {
    pub const fn reg(reg: u8) -> Self {
        Self {
            kind: SymbolKind::Register(reg),
            ty: None,
            local_index: None,
        }
    }

    pub const fn upval(index: u8) -> Self {
        Self {
            kind: SymbolKind::Upvalue(index),
            ty: None,
            local_index: None,
        }
    }

    pub const fn captured_reg(reg: u8, generation: u16) -> Self {
        Self {
            kind: SymbolKind::CapturedRegister { reg, generation },
            ty: None,
            local_index: None,
        }
    }

    pub const fn param(index: u8) -> Self {
        Self {
            kind: SymbolKind::Param(index),
            ty: None,
            local_index: None,
        }
    }

    pub fn with_type(mut self, ty: Option<TypeId>) -> Self {
        self.ty = ty;
        self
    }

    /// Associates this version with one debug-local record.
    pub fn with_local_index(mut self, local_index: Option<usize>) -> Self {
        self.local_index = local_index;
        self
    }
}

/// Builds SSA versions for the registers and upvalues in one function.
pub struct Ssa<'a, G: GraphView> {
    /// Register versions stored as contiguous block rows.
    registers: Vec<Option<SymbolId>>,
    /// Number of register slots in each block row.
    register_count: usize,
    /// Upvalue versions stored as contiguous block rows.
    upvalues: Vec<Option<SymbolId>>,
    /// Number of upvalue slots in each block row.
    upvalue_count: usize,
    /// Control-flow graph that owns the block indices.
    graph: &'a G,
    /// Symbols allocated while constructing SSA.
    arena: Arena<Symbol>,
    /// Trivial Phi symbols mapped to their surviving symbols.
    aliases: HashMap<SymbolId, SymbolId>,
    /// Phi symbols that read each symbol.
    phi_uses: HashMap<SymbolId, BTreeSet<SymbolId>>,
    /// Block containing each Phi symbol.
    phi_to_block: HashMap<SymbolId, usize>,
    /// Predecessor operands read by each Phi symbol.
    phi_to_operands: HashMap<SymbolId, Vec<(usize, SymbolId)>>,
    /// Whether each block has received all local writes.
    filled_blocks: Vec<bool>,
    /// Phi symbols waiting for predecessor blocks to be filled.
    incomplete_phis: HashMap<usize, Vec<(SsaVar, SymbolId)>>,
}

impl<'a, G: GraphView> Ssa<'a, G> {
    /// Creates empty SSA state sized to the function's declared storage.
    pub fn new(graph: &'a G, register_count: u8, upvalue_count: u8) -> Self {
        let blocks_count = graph.len();
        let register_count = usize::from(register_count);
        let upvalue_count = usize::from(upvalue_count);
        let register_slots = blocks_count
            .checked_mul(register_count)
            .expect("SSA register state size overflow");
        let upvalue_slots = blocks_count
            .checked_mul(upvalue_count)
            .expect("SSA upvalue state size overflow");

        Self {
            registers: vec![None; register_slots],
            register_count,
            upvalues: vec![None; upvalue_slots],
            upvalue_count,
            graph,
            arena: Arena::new(),
            aliases: HashMap::new(),
            phi_uses: HashMap::new(),
            phi_to_block: HashMap::new(),
            phi_to_operands: HashMap::new(),
            filled_blocks: vec![false; blocks_count],
            incomplete_phis: HashMap::new(),
        }
    }

    /// Returns the flat state index for one register in one block.
    fn register_index(&self, block: usize, reg: u8) -> usize {
        assert!(block < self.graph.len(), "SSA block index out of range");
        let reg = usize::from(reg);
        assert!(
            reg < self.register_count,
            "register R{reg} exceeds max stack size {}",
            self.register_count
        );
        block * self.register_count + reg
    }

    /// Returns the flat state index for one upvalue in one block.
    fn upvalue_index(&self, block: usize, upvalue: u8) -> usize {
        assert!(block < self.graph.len(), "SSA block index out of range");
        let upvalue = usize::from(upvalue);
        assert!(
            upvalue < self.upvalue_count,
            "upvalue U{upvalue} exceeds declared count {}",
            self.upvalue_count
        );
        block * self.upvalue_count + upvalue
    }

    fn write_var(&mut self, block: usize, var: SsaVar, symbol: SymbolId) {
        match var {
            SsaVar::Reg(reg) => {
                let index = self.register_index(block, reg);
                self.registers[index] = Some(symbol);
            }
            SsaVar::Upval(upvalue) => {
                let index = self.upvalue_index(block, upvalue);
                self.upvalues[index] = Some(symbol);
            }
        }
    }

    pub fn promote_to_captured_reg(&mut self, symbol: SymbolId, reg: u8, generation: u16) {
        self.arena[symbol].kind = SymbolKind::CapturedRegister { reg, generation };
    }

    /// Updates the debug-local record after a multi-instruction write is complete.
    pub fn set_local_index(&mut self, symbol: SymbolId, local_index: Option<usize>) {
        self.arena[symbol].local_index = local_index;
    }

    pub fn alloc_symbol(&mut self, sym: Symbol) -> SymbolId {
        self.arena.alloc(sym)
    }

    pub fn arena(&self) -> &Arena<Symbol> {
        &self.arena
    }

    pub fn write_reg(&mut self, block: usize, reg: u8, symbol: SymbolId) {
        self.write_var(block, SsaVar::Reg(reg), symbol);
    }

    #[must_use]
    pub fn read_var(&mut self, block: usize, var: SsaVar) -> SymbolId {
        match var {
            SsaVar::Reg(reg) => self.read_reg(block, reg),
            SsaVar::Upval(index) => self.read_upval(block, index),
        }
    }

    #[must_use]
    pub fn read_reg(&mut self, block: usize, reg: u8) -> SymbolId {
        let index = self.register_index(block, reg);
        if let Some(sym) = self.registers[index] {
            sym
        } else {
            self.read_var_recursive(block, SsaVar::Reg(reg))
        }
    }

    pub fn write_upval(&mut self, block: usize, index: u8, symbol: SymbolId) {
        self.write_var(block, SsaVar::Upval(index), symbol);
    }

    #[must_use]
    pub fn read_upval(&mut self, block: usize, upvalue: u8) -> SymbolId {
        let index = self.upvalue_index(block, upvalue);
        if let Some(sym) = self.upvalues[index] {
            sym
        } else {
            self.read_var_recursive(block, SsaVar::Upval(upvalue))
        }
    }

    #[must_use]
    pub fn resolve(&self, mut sym: SymbolId) -> SymbolId {
        while let Some(&alias) = self.aliases.get(&sym) {
            sym = alias;
        }
        sym
    }

    #[must_use]
    fn read_operands_from(&mut self, preds: &[usize], var: SsaVar) -> Vec<(usize, SymbolId)> {
        preds
            .iter()
            .map(|&p| {
                let sym = self.read_var(p, var);
                (p, sym)
            })
            .collect()
    }

    fn read_var_recursive(&mut self, block: usize, var: SsaVar) -> SymbolId {
        let preds = self.graph.predecessors(block);
        if preds.is_empty() {
            return self.arena.alloc(Symbol::from(var));
        }

        let is_incomplete = preds.iter().any(|&p| !self.filled_blocks[p]);
        if is_incomplete {
            let phi_sym = self.arena.alloc(Symbol::from(var));
            self.write_var(block, var, phi_sym);

            self.phi_to_block.insert(phi_sym, block);

            self.incomplete_phis
                .entry(block)
                .or_default()
                .push((var, phi_sym));
            return phi_sym;
        }

        if preds.len() == 1 {
            let sym = self.read_var(preds[0], var);
            self.write_var(block, var, sym);
            return sym;
        }

        let phi_sym = self.arena.alloc(Symbol::from(var));
        self.write_var(block, var, phi_sym);
        self.phi_to_block.insert(phi_sym, block);

        let operands = self.read_operands_from(preds, var);
        for (_, op_sym) in &operands {
            self.phi_uses.entry(*op_sym).or_default().insert(phi_sym);
        }
        self.phi_to_operands.insert(phi_sym, operands);

        self.try_remove_trivial_phis(phi_sym)
    }

    fn try_remove_trivial_phis(&mut self, phi_sym: SymbolId) -> SymbolId {
        let Some(operands) = self.phi_to_operands.get(&phi_sym) else {
            return self.resolve(phi_sym);
        };

        let mut same = None;
        for (_, op_sym) in operands {
            let op = self.resolve(*op_sym);

            if Some(op) == same || op == phi_sym {
                continue;
            }
            if same.is_some() {
                return phi_sym;
            }

            same = Some(op);
        }

        let replacement = same.unwrap_or_else(|| {
            let kind = self.arena[phi_sym].kind;
            let ty = self.arena[phi_sym].ty;
            let local_index = self.arena[phi_sym].local_index;
            self.arena.alloc(Symbol {
                kind,
                ty,
                local_index,
            })
        });

        self.phi_to_operands.remove(&phi_sym);
        self.phi_to_block.remove(&phi_sym);
        self.aliases.insert(phi_sym, replacement);

        if let Some(uses) = self.phi_uses.remove(&phi_sym) {
            for used_by in uses {
                if !self.aliases.contains_key(&used_by) {
                    self.try_remove_trivial_phis(used_by);
                }
            }
        }

        replacement
    }

    pub fn mark_filled(&mut self, block: usize) {
        self.filled_blocks[block] = true;
    }

    pub fn seal_blocks(&mut self) {
        let incomplete = std::mem::take(&mut self.incomplete_phis);

        for (block, phis) in incomplete {
            for (var, phi_sym) in phis {
                let preds = self.graph.predecessors(block);
                let operands = self.read_operands_from(preds, var);
                for (_, op_sym) in &operands {
                    self.phi_uses.entry(*op_sym).or_default().insert(phi_sym);
                }

                self.phi_to_operands.insert(phi_sym, operands);
                self.try_remove_trivial_phis(phi_sym);
            }
        }
    }

    /// Materializes surviving Phi nodes in deterministic block and symbol order.
    pub fn finish(&mut self, blocks: &mut [Block]) {
        let mut phis: Vec<_> = std::mem::take(&mut self.phi_to_operands)
            .into_iter()
            .collect();
        phis.sort_by_key(|(symbol, _)| (self.phi_to_block[symbol], *symbol));

        // Inserting at the front reverses each block's local order, so consume
        // the globally sorted list backward to leave ascending symbol IDs.
        for (phi_symbol, operands) in phis.into_iter().rev() {
            let block_index = self.phi_to_block[&phi_symbol];
            let operands = operands
                .into_iter()
                .map(|(predecessor, symbol)| (predecessor, self.resolve(symbol)))
                .collect();
            let phi = PhiNode {
                target: phi_symbol,
                operands,
            };

            blocks[block_index].stmts_mut().insert(0, Stmt::Phi(phi));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Ssa, Symbol};
    use crate::hil::cflow::graph::AdjGraph;

    /// SSA state uses the declared row widths and keeps block rows separate.
    #[test]
    fn state_uses_declared_storage_sizes() {
        let successors = vec![Vec::new(), Vec::new(), Vec::new()];
        let predecessors = vec![Vec::new(), Vec::new(), Vec::new()];
        let graph = AdjGraph::new(0, &successors, &predecessors);
        let mut ssa = Ssa::new(&graph, 4, 2);

        assert_eq!(ssa.registers.len(), 12);
        assert_eq!(ssa.upvalues.len(), 6);

        let register = ssa.alloc_symbol(Symbol::reg(3));
        let upvalue = ssa.alloc_symbol(Symbol::upval(1));
        ssa.write_reg(2, 3, register);
        ssa.write_upval(2, 1, upvalue);

        assert_eq!(ssa.read_reg(2, 3), register);
        assert_eq!(ssa.read_upval(2, 1), upvalue);
    }
}
