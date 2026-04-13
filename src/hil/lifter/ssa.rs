use std::collections::{BTreeSet, HashMap};

use id_arena::{Arena, Id};

use crate::hil::{
    cflow::graph::Block,
    ir::{HilStmt, PhiNode, ToSpanned as _},
};

pub type SymbolId = Id<Symbol>;

#[derive(Debug, Clone)]
pub struct Symbol {
    /// The original storage role this symbol represents.
    pub kind: SymbolKind,
    /// The mutability type of this symbol.
    pub mutability: Mutability,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Register(u8),
    Upvalue(u8),
    Param(u8),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SsaVar {
    Reg(u8),
    Upval(u8),
}

impl SsaVar {
    const fn to_index(self) -> usize {
        match self {
            SsaVar::Reg(r) => r as usize,
            SsaVar::Upval(u) => 256 + u as usize,
        }
    }
}

impl Symbol {
    pub fn reg(reg: u8) -> Self {
        Self {
            kind: SymbolKind::Register(reg),
            mutability: Mutability::Immutable,
        }
    }

    pub fn upval(index: u8) -> Self {
        Self {
            kind: SymbolKind::Upvalue(index),
            mutability: Mutability::Immutable,
        }
    }

    pub fn param(index: u8) -> Self {
        Self {
            kind: SymbolKind::Param(index),
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

pub struct Ssa<'a> {
    defs: Vec<[Option<SymbolId>; 512]>,
    predecessors: &'a [Vec<usize>],
    arena: &'a mut Arena<Symbol>,
    aliases: HashMap<SymbolId, SymbolId>,
    phi_uses: HashMap<SymbolId, BTreeSet<SymbolId>>,
    phi_to_block: HashMap<SymbolId, usize>,
    phi_to_operands: HashMap<SymbolId, Vec<(usize, SymbolId)>>,

    filled_blocks: Vec<bool>,
    incomplete_phis: HashMap<usize, Vec<(SsaVar, SymbolId)>>,
}

impl<'a> Ssa<'a> {
    pub fn new(predecessors: &'a [Vec<usize>], arena: &'a mut Arena<Symbol>) -> Self {
        let blocks_count = predecessors.len();
        Self {
            defs: vec![[None; 512]; blocks_count],
            predecessors,
            arena,
            aliases: HashMap::new(),
            phi_uses: HashMap::new(),
            phi_to_block: HashMap::new(),
            phi_to_operands: HashMap::new(),
            filled_blocks: vec![false; blocks_count],
            incomplete_phis: HashMap::new(),
        }
    }

    pub fn alloc_symbol(&mut self, symbol: Symbol) -> SymbolId {
        self.arena.alloc(symbol)
    }

    pub fn arena_iter(&self) -> impl Iterator<Item = (SymbolId, &Symbol)> {
        self.arena.iter()
    }

    pub fn write_reg(&mut self, block: usize, reg: u8, symbol: SymbolId) {
        self.defs[block][SsaVar::Reg(reg).to_index()] = Some(symbol);
    }

    pub fn read_reg(&mut self, block: usize, reg: u8) -> SymbolId {
        if let Some(sym) = self.defs[block][SsaVar::Reg(reg).to_index()] {
            sym
        } else {
            self.read_var_recursive(block, SsaVar::Reg(reg))
        }
    }

    pub fn write_upval(&mut self, block: usize, index: u8, symbol: SymbolId) {
        self.defs[block][SsaVar::Upval(index).to_index()] = Some(symbol);
    }

    pub fn read_upval(&mut self, block: usize, index: u8) -> SymbolId {
        if let Some(sym) = self.defs[block][SsaVar::Upval(index).to_index()] {
            sym
        } else {
            self.read_var_recursive(block, SsaVar::Upval(index))
        }
    }

    pub fn resolve(&self, mut sym: SymbolId) -> SymbolId {
        while let Some(&alias) = self.aliases.get(&sym) {
            sym = alias;
        }
        sym
    }

    fn read_var_recursive(&mut self, block: usize, var: SsaVar) -> SymbolId {
        let preds = &self.predecessors[block];
        if preds.is_empty() {
            let symbol = match var {
                SsaVar::Reg(r) => Symbol::reg(r),
                SsaVar::Upval(u) => Symbol::upval(u),
            };
            return self.arena.alloc(symbol);
        }

        let is_incomplete = preds.iter().any(|&p| !self.filled_blocks[p]);
        if is_incomplete {
            let symbol = match var {
                SsaVar::Reg(r) => Symbol::reg(r),
                SsaVar::Upval(u) => Symbol::upval(u),
            };
            let phi_sym = self.arena.alloc(symbol);
            self.defs[block][var.to_index()] = Some(phi_sym);
            self.phi_to_block.insert(phi_sym, block);

            self.incomplete_phis
                .entry(block)
                .or_default()
                .push((var, phi_sym));
            return phi_sym;
        }

        if preds.len() == 1 {
            let sym = match var {
                SsaVar::Reg(r) => self.read_reg(preds[0], r),
                SsaVar::Upval(u) => self.read_upval(preds[0], u),
            };
            self.defs[block][var.to_index()] = Some(sym);
            return sym;
        }

        let symbol = match var {
            SsaVar::Reg(r) => Symbol::reg(r),
            SsaVar::Upval(u) => Symbol::upval(u),
        };
        let phi_sym = self.arena.alloc(symbol);
        self.defs[block][var.to_index()] = Some(phi_sym);
        self.phi_to_block.insert(phi_sym, block);

        let operands: Vec<_> = preds
            .iter()
            .map(|&p| {
                let sym = match var {
                    SsaVar::Reg(r) => self.read_reg(p, r),
                    SsaVar::Upval(u) => self.read_upval(p, u),
                };
                (p, sym)
            })
            .collect();
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
            self.arena.alloc(Symbol {
                kind,
                mutability: Mutability::Immutable,
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
                let preds = &self.predecessors[block];
                let operands: Vec<_> = preds
                    .iter()
                    .map(|&p| {
                        let sym = match var {
                            SsaVar::Reg(r) => self.read_reg(p, r),
                            SsaVar::Upval(u) => self.read_upval(p, u),
                        };
                        (p, sym)
                    })
                    .collect();
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
