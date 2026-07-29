use std::collections::{BTreeSet, HashMap};

use id_arena::{Arena, Id};

use crate::hil::{
    cflow::{cfg::Block, graph::GraphView},
    ir::{PhiNode, Stmt},
    ty2::canonical::TypeId,
};

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

/// One named local and its SSA versions.
#[derive(Debug, Clone)]
pub struct NamedLocal {
    /// Name stored in Luau debug information.
    pub name: String,
    /// First bytecode PC covered by the local.
    pub start_pc: u32,
    /// First bytecode PC after the local's lifetime.
    pub end_pc: u32,
    /// SSA versions associated with this local.
    pub symbols: Vec<SymbolId>,
}

/// Stores the symbols and storage links found while building SSA.
#[derive(Debug, Clone)]
pub struct FunctionSymbols {
    /// Entry versions for the function parameters.
    pub params: Vec<SymbolId>,
    /// Entry versions for the declared upvalues.
    pub upvalues: Vec<SymbolId>,
    /// Named locals recovered from Luau debug information.
    pub named_locals: Vec<NamedLocal>,
    /// Version groups for declared upvalue storage.
    pub(crate) upvalue_version_groups: Vec<Vec<SymbolId>>,
    /// Version groups for captured register storage.
    pub(crate) captured_version_groups: Vec<Vec<SymbolId>>,
    /// Version pairs that must use one source local after inference.
    pub(crate) loop_carried_versions: Vec<(SymbolId, SymbolId)>,
}

impl FunctionSymbols {
    /// Creates the symbol metadata for one lifted function.
    pub(crate) fn new(
        params: Vec<SymbolId>,
        upvalues: Vec<SymbolId>,
        named_locals: Vec<NamedLocal>,
        upvalue_version_groups: Vec<Vec<SymbolId>>,
        captured_version_groups: Vec<Vec<SymbolId>>,
        loop_carried_versions: Vec<(SymbolId, SymbolId)>,
    ) -> Self {
        Self {
            params,
            upvalues,
            named_locals,
            upvalue_version_groups,
            captured_version_groups,
            loop_carried_versions,
        }
    }

    /// Returns all versions of declared upvalue storage.
    pub(crate) fn upvalue_version_groups(&self) -> impl Iterator<Item = &[SymbolId]> {
        self.upvalue_version_groups.iter().map(Vec::as_slice)
    }

    /// Returns all version groups for mutable storage.
    pub(crate) fn storage_version_groups(&self) -> impl Iterator<Item = &[SymbolId]> {
        self.upvalue_version_groups
            .iter()
            .chain(&self.captured_version_groups)
            .map(Vec::as_slice)
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

pub struct Ssa<'a, G: GraphView> {
    registers: Vec<[Option<SymbolId>; 256]>,
    upvalues: Vec<[Option<SymbolId>; 256]>,

    graph: &'a G,
    arena: Arena<Symbol>,

    aliases: HashMap<SymbolId, SymbolId>,
    phi_uses: HashMap<SymbolId, BTreeSet<SymbolId>>,
    phi_to_block: HashMap<SymbolId, usize>,
    phi_to_operands: HashMap<SymbolId, Vec<(usize, SymbolId)>>,

    filled_blocks: Vec<bool>,
    incomplete_phis: HashMap<usize, Vec<(SsaVar, SymbolId)>>,
}

impl<'a, G: GraphView> Ssa<'a, G> {
    pub fn new(graph: &'a G) -> Self {
        let blocks_count = graph.len();
        Self {
            registers: vec![[None; 256]; blocks_count],
            upvalues: vec![[None; 256]; blocks_count],
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

    fn write_var(&mut self, block: usize, var: SsaVar, symbol: SymbolId) {
        match var {
            SsaVar::Reg(reg) => self.registers[block][reg as usize] = Some(symbol),
            SsaVar::Upval(index) => self.upvalues[block][index as usize] = Some(symbol),
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
        if let Some(sym) = self.registers[block][reg as usize] {
            sym
        } else {
            self.read_var_recursive(block, SsaVar::Reg(reg))
        }
    }

    pub fn write_upval(&mut self, block: usize, index: u8, symbol: SymbolId) {
        self.write_var(block, SsaVar::Upval(index), symbol);
    }

    #[must_use]
    pub fn read_upval(&mut self, block: usize, index: u8) -> SymbolId {
        if let Some(sym) = self.upvalues[block][index as usize] {
            sym
        } else {
            self.read_var_recursive(block, SsaVar::Upval(index))
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
