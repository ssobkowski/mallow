use std::collections::{BTreeSet, HashMap};

use id_arena::Arena;

use super::{Block, Instr, Value, ValueId};
use crate::hil::cflow::graph::GraphView;

/// Builds immutable value versions for physical registers.
pub(super) struct Ssa<'a, G: GraphView> {
    /// Register versions stored as contiguous block rows.
    registers: Vec<Option<ValueId>>,
    /// Number of register slots in each block row.
    register_count: usize,
    /// Control-flow graph that owns the block indices.
    graph: &'a G,
    /// Values allocated while constructing SSA.
    values: Arena<Value>,
    /// Trivial Phi values mapped to their surviving values.
    aliases: HashMap<ValueId, ValueId>,
    /// Phi values that read each value.
    phi_uses: HashMap<ValueId, BTreeSet<ValueId>>,
    /// Block containing each Phi value.
    phi_to_block: HashMap<ValueId, usize>,
    /// Predecessor inputs read by each Phi value.
    phi_to_inputs: HashMap<ValueId, Vec<(usize, ValueId)>>,
    /// Whether each block has received all local writes.
    filled_blocks: Vec<bool>,
    /// Phi values waiting for predecessor blocks to be filled.
    incomplete_phis: HashMap<usize, Vec<(u8, ValueId)>>,
}

impl<'a, G: GraphView> Ssa<'a, G> {
    /// Creates empty SSA state sized to the function's declared registers.
    pub(super) fn new(graph: &'a G, register_count: u8) -> Self {
        let block_count = graph.len();
        let register_count = register_count as usize;
        let register_slots = block_count
            .checked_mul(register_count)
            .expect("SSA register state size overflow");

        Self {
            registers: vec![None; register_slots],
            register_count,
            graph,
            values: Arena::new(),
            aliases: HashMap::new(),
            phi_uses: HashMap::new(),
            phi_to_block: HashMap::new(),
            phi_to_inputs: HashMap::new(),
            filled_blocks: vec![false; block_count],
            incomplete_phis: HashMap::new(),
        }
    }

    /// Allocates one immutable value identity.
    pub(super) fn alloc(&mut self) -> ValueId {
        self.values.alloc(Value)
    }

    /// Writes one register version in one block.
    pub(super) fn write_reg(&mut self, block: usize, reg: u8, value: ValueId) {
        let index = self.register_index(block, reg);
        self.registers[index] = Some(value);
    }

    /// Reads one register version in one block.
    pub(super) fn read_reg(&mut self, block: usize, reg: u8) -> ValueId {
        let index = self.register_index(block, reg);
        if let Some(value) = self.registers[index] {
            value
        } else {
            self.read_reg_recursive(block, reg)
        }
    }

    /// Marks one block complete for sealed SSA construction.
    pub(super) fn mark_filled(&mut self, block: usize) {
        self.filled_blocks[block] = true;
    }

    /// Completes SSA, inserts surviving Phi instructions, and returns its values.
    pub(super) fn finish(
        mut self,
        blocks: &mut [Block],
    ) -> (Arena<Value>, HashMap<ValueId, ValueId>) {
        self.seal_blocks();
        let mut phis: Vec<_> = std::mem::take(&mut self.phi_to_inputs)
            .into_iter()
            .collect();
        phis.sort_by_key(|(value, _)| (self.phi_to_block[value], *value));

        for (out, inputs) in phis.into_iter().rev() {
            let block = self.phi_to_block[&out];
            let inputs = inputs
                .into_iter()
                .map(|(predecessor, value)| (predecessor, self.resolve(value)))
                .collect();
            blocks[block].instrs.insert(0, Instr::Phi { out, inputs });
        }

        (self.values, self.aliases)
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

    /// Resolves one value through trivial Phi aliases.
    fn resolve(&self, mut value: ValueId) -> ValueId {
        while let Some(&alias) = self.aliases.get(&value) {
            value = alias;
        }
        value
    }

    /// Recursively reads one register and creates a Phi when needed.
    fn read_reg_recursive(&mut self, block: usize, reg: u8) -> ValueId {
        let predecessors = self.graph.predecessors(block);
        if predecessors.is_empty() {
            return self.alloc();
        }

        if predecessors
            .iter()
            .any(|&predecessor| !self.filled_blocks[predecessor])
        {
            let phi = self.alloc();
            self.write_reg(block, reg, phi);
            self.phi_to_block.insert(phi, block);
            self.incomplete_phis
                .entry(block)
                .or_default()
                .push((reg, phi));
            return phi;
        }

        if predecessors.len() == 1 {
            let value = self.read_reg(predecessors[0], reg);
            self.write_reg(block, reg, value);
            return value;
        }

        let phi = self.alloc();
        self.write_reg(block, reg, phi);
        self.phi_to_block.insert(phi, block);
        let inputs = self.read_inputs(predecessors, reg);
        self.record_inputs(phi, inputs);
        self.remove_trivial_phi(phi)
    }

    /// Reads one register from every predecessor.
    fn read_inputs(&mut self, predecessors: &[usize], reg: u8) -> Vec<(usize, ValueId)> {
        predecessors
            .iter()
            .map(|&predecessor| (predecessor, self.read_reg(predecessor, reg)))
            .collect()
    }

    /// Records the inputs and reverse uses of one Phi.
    fn record_inputs(&mut self, phi: ValueId, inputs: Vec<(usize, ValueId)>) {
        for (_, value) in &inputs {
            self.phi_uses.entry(*value).or_default().insert(phi);
        }
        self.phi_to_inputs.insert(phi, inputs);
    }

    /// Removes one trivial Phi and revisits dependent Phi values.
    fn remove_trivial_phi(&mut self, phi: ValueId) -> ValueId {
        let Some(inputs) = self.phi_to_inputs.get(&phi) else {
            return self.resolve(phi);
        };

        let mut same = None;
        for (_, input) in inputs {
            let input = self.resolve(*input);
            if input == phi || Some(input) == same {
                continue;
            }
            if same.is_some() {
                return phi;
            }
            same = Some(input);
        }

        let replacement = same.unwrap_or_else(|| self.alloc());
        self.phi_to_inputs.remove(&phi);
        self.phi_to_block.remove(&phi);
        self.aliases.insert(phi, replacement);

        if let Some(uses) = self.phi_uses.remove(&phi) {
            for use_value in uses {
                if !self.aliases.contains_key(&use_value) {
                    self.remove_trivial_phi(use_value);
                }
            }
        }
        replacement
    }

    /// Completes Phi values created before all predecessors were filled.
    fn seal_blocks(&mut self) {
        for (block, phis) in std::mem::take(&mut self.incomplete_phis) {
            for (reg, phi) in phis {
                let inputs = self.read_inputs(self.graph.predecessors(block), reg);
                self.record_inputs(phi, inputs);
                self.remove_trivial_phi(phi);
            }
        }
    }
}
