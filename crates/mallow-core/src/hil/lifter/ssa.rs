use std::collections::{BTreeSet, HashMap};

use id_arena::{Arena, Id};

use crate::hil::cflow::cfg::Block;
use crate::hil::cflow::graph::GraphView;
use crate::hil::ir::{Cell, CellId, PhiNode, Stmt};
use crate::hil::ty::canonical::TypeId;

/// Stable identity for one immutable SSA symbol.
pub type SymbolId = Id<Symbol>;

/// Metadata for one immutable SSA symbol.
#[derive(Debug, Clone)]
pub struct Symbol {
    /// The register role that introduced this symbol.
    pub kind: SymbolKind,
    /// Bytecode-provided type fact for this symbol, if one was available.
    pub ty: Option<TypeId>,
    /// Index of the active debug-local record, if debug information was present.
    pub local_index: Option<usize>,
}

/// The bytecode role that introduced one immutable SSA symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    /// A normal register value.
    Register(u8),
    /// A function parameter value.
    Param(u8),
    /// Transitional source-emitter name for one upvalue cell.
    UpvalueName(u8),
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

/// Stores immutable symbols and mutable cells found while lifting one function.
#[derive(Debug, Clone)]
pub(crate) struct FunctionSymbols {
    /// Entry symbol for each formal parameter, in parameter order.
    params: Vec<SymbolId>,
    /// Transitional source-emitter symbol for each upvalue slot.
    upvalues: Vec<SymbolId>,
    /// Mutable cell for each declared upvalue slot, in slot order.
    upvalue_cells: Vec<CellId>,
    /// All mutable cells owned by the function.
    cells: Arena<Cell>,
    /// Transitional source-emitter symbol for each mutable cell.
    cell_names: HashMap<CellId, SymbolId>,
    /// Named locals recovered from Luau debug information.
    debug_locals: Vec<NamedLocal>,
    /// Pairs of symbols that represent one loop-carried local.
    loop_carried_links: Vec<(SymbolId, SymbolId)>,
}

impl FunctionSymbols {
    /// Creates the symbol and cell metadata for one lifted function.
    pub(crate) fn new(
        params: Vec<SymbolId>,
        upvalues: Vec<SymbolId>,
        upvalue_cells: Vec<CellId>,
        cells: Arena<Cell>,
        cell_names: HashMap<CellId, SymbolId>,
        debug_locals: Vec<NamedLocal>,
        loop_carried_links: Vec<(SymbolId, SymbolId)>,
    ) -> Self {
        Self {
            params,
            upvalues,
            upvalue_cells,
            cells,
            cell_names,
            debug_locals,
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

    /// Returns the transitional emitter symbol for each declared upvalue slot.
    pub(crate) fn upvalues(&self) -> &[SymbolId] {
        &self.upvalues
    }

    /// Returns the mutable cell for each declared upvalue slot.
    pub(crate) fn upvalue_cells(&self) -> &[CellId] {
        &self.upvalue_cells
    }

    /// Returns the transitional source-emitter symbol for one cell.
    pub(crate) fn name_for_cell(&self, cell: CellId) -> SymbolId {
        self.cell_names[&cell]
    }

    /// Returns the transitional source-emitter names for all cells.
    pub(crate) fn cell_names(&self) -> impl Iterator<Item = (CellId, SymbolId)> + '_ {
        self.cell_names
            .iter()
            .map(|(cell, symbol)| (*cell, *symbol))
    }

    /// Returns the transitional name for one declared upvalue slot.
    pub(crate) fn for_upvalue(&self, slot: usize) -> impl Iterator<Item = SymbolId> + '_ {
        std::iter::once(self.upvalues[slot])
    }

    /// Returns all mutable cells owned by this function.
    pub(crate) fn cells(&self) -> &Arena<Cell> {
        &self.cells
    }

    /// Returns named locals recovered from Luau debug information.
    pub(crate) fn debug_locals(&self) -> &[NamedLocal] {
        &self.debug_locals
    }

    /// Returns mutable debug locals for SSA canonicalization.
    pub(crate) fn debug_locals_mut(&mut self) -> &mut [NamedLocal] {
        &mut self.debug_locals
    }

    /// Takes the pairs of symbols that represent loop-carried locals.
    pub(crate) fn take_loop_carried_links(&mut self) -> impl Iterator<Item = (SymbolId, SymbolId)> {
        std::mem::take(&mut self.loop_carried_links).into_iter()
    }
}

impl Symbol {
    /// Creates one normal register symbol.
    pub const fn reg(reg: u8) -> Self {
        Self {
            kind: SymbolKind::Register(reg),
            ty: None,
            local_index: None,
        }
    }

    /// Creates one transitional source-emitter name for an upvalue cell.
    pub const fn upvalue_name(index: u8) -> Self {
        Self {
            kind: SymbolKind::UpvalueName(index),
            ty: None,
            local_index: None,
        }
    }

    /// Creates one parameter symbol.
    pub const fn param(index: u8) -> Self {
        Self {
            kind: SymbolKind::Param(index),
            ty: None,
            local_index: None,
        }
    }

    /// Adds a bytecode-provided type fact.
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

/// Builds SSA versions for registers in one function.
pub struct Ssa<'a, G: GraphView> {
    /// Register versions stored as contiguous block rows.
    registers: Vec<Option<SymbolId>>,
    /// Number of register slots in each block row.
    register_count: usize,
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
    incomplete_phis: HashMap<usize, Vec<(u8, SymbolId)>>,
}

impl<'a, G: GraphView> Ssa<'a, G> {
    /// Creates empty SSA state sized to the function's declared registers.
    pub fn new(graph: &'a G, register_count: u8) -> Self {
        let blocks_count = graph.len();
        let register_count = usize::from(register_count);
        let register_slots = blocks_count
            .checked_mul(register_count)
            .expect("SSA register state size overflow");

        Self {
            registers: vec![None; register_slots],
            register_count,
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

    /// Updates the debug-local record after a multi-instruction write is complete.
    pub fn set_local_index(&mut self, symbol: SymbolId, local_index: Option<usize>) {
        self.arena[symbol].local_index = local_index;
    }

    /// Allocates one immutable SSA symbol.
    pub fn alloc_symbol(&mut self, sym: Symbol) -> SymbolId {
        self.arena.alloc(sym)
    }

    /// Returns all allocated symbols.
    pub fn arena(&self) -> &Arena<Symbol> {
        &self.arena
    }

    /// Writes one register version in one block.
    pub fn write_reg(&mut self, block: usize, reg: u8, symbol: SymbolId) {
        let index = self.register_index(block, reg);
        self.registers[index] = Some(symbol);
    }

    /// Reads one register version in one block.
    #[must_use]
    pub fn read_reg(&mut self, block: usize, reg: u8) -> SymbolId {
        let index = self.register_index(block, reg);
        if let Some(sym) = self.registers[index] {
            sym
        } else {
            self.read_reg_recursive(block, reg)
        }
    }

    /// Resolves one symbol through trivial Phi aliases.
    #[must_use]
    pub fn resolve(&self, mut sym: SymbolId) -> SymbolId {
        while let Some(&alias) = self.aliases.get(&sym) {
            sym = alias;
        }
        sym
    }

    /// Reads one register from every predecessor.
    fn read_operands_from(&mut self, preds: &[usize], reg: u8) -> Vec<(usize, SymbolId)> {
        preds
            .iter()
            .map(|&predecessor| (predecessor, self.read_reg(predecessor, reg)))
            .collect()
    }

    /// Recursively reads one register and creates a Phi when needed.
    fn read_reg_recursive(&mut self, block: usize, reg: u8) -> SymbolId {
        let preds = self.graph.predecessors(block);
        if preds.is_empty() {
            return self.arena.alloc(Symbol::reg(reg));
        }

        let is_incomplete = preds
            .iter()
            .any(|&predecessor| !self.filled_blocks[predecessor]);
        if is_incomplete {
            let phi_sym = self.arena.alloc(Symbol::reg(reg));
            self.write_reg(block, reg, phi_sym);
            self.phi_to_block.insert(phi_sym, block);
            self.incomplete_phis
                .entry(block)
                .or_default()
                .push((reg, phi_sym));
            return phi_sym;
        }

        if preds.len() == 1 {
            let sym = self.read_reg(preds[0], reg);
            self.write_reg(block, reg, sym);
            return sym;
        }

        let phi_sym = self.arena.alloc(Symbol::reg(reg));
        self.write_reg(block, reg, phi_sym);
        self.phi_to_block.insert(phi_sym, block);

        let operands = self.read_operands_from(preds, reg);
        for (_, op_sym) in &operands {
            self.phi_uses.entry(*op_sym).or_default().insert(phi_sym);
        }
        self.phi_to_operands.insert(phi_sym, operands);

        self.try_remove_trivial_phis(phi_sym)
    }

    /// Removes one trivial Phi and revisits dependent Phi nodes.
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

    /// Marks one block complete for sealed SSA construction.
    pub fn mark_filled(&mut self, block: usize) {
        self.filled_blocks[block] = true;
    }

    /// Completes Phi nodes that were created before every predecessor was filled.
    pub fn seal_blocks(&mut self) {
        let incomplete = std::mem::take(&mut self.incomplete_phis);

        for (block, phis) in incomplete {
            for (reg, phi_sym) in phis {
                let preds = self.graph.predecessors(block);
                let operands = self.read_operands_from(preds, reg);
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

    /// SSA state uses the declared row width and keeps block rows separate.
    #[test]
    fn state_uses_declared_register_size() {
        let successors = vec![Vec::new(), Vec::new(), Vec::new()];
        let predecessors = vec![Vec::new(), Vec::new(), Vec::new()];
        let graph = AdjGraph::new(0, &successors, &predecessors);
        let mut ssa = Ssa::new(&graph, 4);

        assert_eq!(ssa.registers.len(), 12);

        let register = ssa.alloc_symbol(Symbol::reg(3));
        ssa.write_reg(2, 3, register);

        assert_eq!(ssa.read_reg(2, 3), register);
    }
}
