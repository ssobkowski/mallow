use std::collections::{BTreeSet, HashMap};

use id_arena::{Arena, Id};

use crate::{
    common::ToSpanned as _,
    hil::{
        cflow::cfg::Block,
        ir::{HilStmt, PhiNode},
    },
};

pub type SymbolId = Id<Symbol>;

#[derive(Debug, Clone)]
pub struct Symbol {
    /// The original storage role this symbol represents.
    pub kind: SymbolKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Register(u8),
    CapturedRegister { reg: u8, generation: u16 },
    Upvalue(u8),
    Param(u8),
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
        }
    }

    pub const fn upval(index: u8) -> Self {
        Self {
            kind: SymbolKind::Upvalue(index),
        }
    }

    pub const fn captured_reg(reg: u8, generation: u16) -> Self {
        Self {
            kind: SymbolKind::CapturedRegister { reg, generation },
        }
    }

    pub const fn param(index: u8) -> Self {
        Self {
            kind: SymbolKind::Param(index),
        }
    }
}

pub struct Ssa<'a> {
    registers: Vec<[Option<SymbolId>; 256]>,
    upvalues: Vec<[Option<SymbolId>; 256]>,

    predecessors: &'a [Vec<usize>], // TODO: hold a GraphView instead?
    arena: Arena<Symbol>,

    aliases: HashMap<SymbolId, SymbolId>,
    phi_uses: HashMap<SymbolId, BTreeSet<SymbolId>>,
    phi_to_block: HashMap<SymbolId, usize>,
    phi_to_operands: HashMap<SymbolId, Vec<(usize, SymbolId)>>,

    filled_blocks: Vec<bool>,
    incomplete_phis: HashMap<usize, Vec<(SsaVar, SymbolId)>>,
}

impl<'a> Ssa<'a> {
    pub fn new(predecessors: &'a [Vec<usize>]) -> Self {
        let blocks_count = predecessors.len();
        Self {
            registers: vec![[None; 256]; blocks_count],
            upvalues: vec![[None; 256]; blocks_count],
            predecessors,
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
        let preds = &self.predecessors[block];
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
            self.arena.alloc(Symbol { kind })
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
                let preds = &self.predecessors[block];
                let operands = self.read_operands_from(preds, var);
                for (_, op_sym) in &operands {
                    self.phi_uses.entry(*op_sym).or_default().insert(phi_sym);
                }

                self.phi_to_operands.insert(phi_sym, operands);
                self.try_remove_trivial_phis(phi_sym);
            }
        }
    }

    pub fn finish(&mut self, blocks: &mut [Block]) {
        let map = std::mem::take(&mut self.phi_to_operands);
        for (phi_sym, operands) in map {
            let block_idx = self.phi_to_block[&phi_sym];

            let resolved_operands: Vec<_> = operands
                .into_iter()
                .map(|(p, sym)| (p, self.resolve(sym)))
                .collect();

            let phi_node = PhiNode {
                target: phi_sym,
                operands: resolved_operands,
            };

            blocks[block_idx]
                .stmts
                .insert(0, HilStmt::Phi(phi_node).to_spanned(0));
        }
    }
}
