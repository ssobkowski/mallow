use std::collections::{BTreeSet, HashMap};

use id_arena::Arena;

use super::{Block, Value, ValueId};
use crate::ir::fir::{ControlFlowGraph, Edge};
use crate::ir::graph::GraphView;

enum Input {
    /// This value comes from the entry block (e.g. from a function param).
    Entry(ValueId),
    /// This value comes from a predecessor block.
    Predecessor(usize, ValueId),
}

impl Input {
    #[inline]
    fn value(&self) -> ValueId {
        match self {
            Input::Entry(value) => *value,
            Input::Predecessor(_, value) => *value,
        }
    }
}

/// Builds immutable value versions for physical registers.
pub struct Ssa<'g, G> {
    /// Register versions stored as contiguous block rows.
    registers: Box<[Option<ValueId>]>,
    /// Registers allocated at the entry.
    entry_registers: Box<[Option<ValueId>]>,
    /// Number of register slots in each block row.
    register_count: usize,
    /// Control-flow graph that owns the block indices.
    graph: &'g G,
    /// Values allocated while constructing SSA.
    values: Arena<Value>,
    /// Trivial Phi values mapped to their surviving values.
    aliases: HashMap<ValueId, ValueId>,
    /// Phi values that read each value.
    phi_uses: HashMap<ValueId, BTreeSet<ValueId>>,
    /// Block containing each Phi value.
    phi_to_block: HashMap<ValueId, usize>,
    /// Predecessor inputs read by each Phi value.
    phi_to_inputs: HashMap<ValueId, Vec<Input>>,
    /// Whether each block has received all local writes.
    filled_blocks: Box<[bool]>,
    /// Phi values waiting for predecessor blocks to be filled.
    incomplete_phis: HashMap<usize, Vec<(u8, ValueId)>>,
}

impl<'g, G: GraphView<Node = usize>> Ssa<'g, G> {
    /// Creates empty SSA state sized to the function's declared registers.
    pub fn new(graph: &'g G, register_count: u8) -> Self {
        let block_count = graph.len();
        let register_count = register_count as usize;
        let register_slots = block_count
            .checked_mul(register_count)
            .expect("SSA register state size overflow");

        Self {
            registers: vec![None; register_slots].into_boxed_slice(),
            entry_registers: vec![None; register_count].into_boxed_slice(),
            register_count,
            graph,
            values: Arena::new(),
            aliases: HashMap::new(),
            phi_uses: HashMap::new(),
            phi_to_block: HashMap::new(),
            phi_to_inputs: HashMap::new(),
            filled_blocks: vec![false; block_count].into_boxed_slice(),
            incomplete_phis: HashMap::new(),
        }
    }

    /// Allocates an immutable value identity.
    #[inline]
    #[must_use]
    pub fn alloc(&mut self) -> ValueId {
        self.values.alloc(Value)
    }

    /// Stores a register value at the entry block, without creating
    /// a "SSA Identity" for it yet.
    #[inline]
    pub fn write_entry(&mut self, reg: u8, value: ValueId) {
        self.entry_registers[reg as usize] = Some(value);
    }

    /// Writes one register version in one block.
    #[inline]
    pub fn write_reg(&mut self, block: usize, reg: u8, value: ValueId) {
        let index = self.register_index(block, reg);
        self.registers[index] = Some(value);
    }

    /// Reads one register version in one block.
    #[must_use]
    pub fn read_reg(&mut self, block: usize, reg: u8) -> ValueId {
        let index = self.register_index(block, reg);
        if let Some(value) = self.registers[index] {
            value
        } else {
            self.read_reg_recursive(block, reg)
        }
    }

    /// Marks one block complete for sealed SSA construction.
    #[inline]
    pub fn mark_filled(&mut self, block: usize) {
        self.filled_blocks[block] = true;
    }

    /// Completes SSA, updating the block edges.
    ///
    /// # Returns
    ///
    /// Returns a tuple of:
    /// - The values allocated during SSA construction.
    /// - The Phi value aliases.
    /// - The function's entry edge.
    #[must_use]
    pub fn finish(
        mut self,
        cfg: &mut ControlFlowGraph<Block>,
    ) -> (Arena<Value>, HashMap<ValueId, ValueId>, Edge) {
        self.seal_blocks();
        self.remove_remaining_trivial_phis();
        let mut phis: Vec<_> = std::mem::take(&mut self.phi_to_inputs)
            .into_iter()
            .collect();
        phis.sort_by_key(|(value, _)| (self.phi_to_block[value], *value));

        let mut entry = Edge {
            target: cfg.entry(),
            params: Vec::new(),
        };
        for (out, inputs) in phis.into_iter() {
            let block = self.phi_to_block[&out];
            cfg[block].params.push(out);

            for input in inputs {
                match input {
                    Input::Predecessor(predecessor, input) => {
                        for edge in cfg[predecessor].exit.edges_mut() {
                            if edge.target == block {
                                edge.params.push(self.resolve(input));
                            }
                        }
                    }
                    Input::Entry(input) => {
                        entry.params.push(self.resolve(input));
                    }
                }
            }
        }

        (self.values, self.aliases, entry)
    }

    /// Returns the flat state index for one register in one block.
    #[inline]
    fn register_index(&self, block: usize, reg: u8) -> usize {
        assert!(block < self.graph.len(), "SSA block index out of range");
        let reg = reg as usize;
        assert!(
            reg < self.register_count,
            "register R{reg} exceeds max stack size {}",
            self.register_count
        );
        block * self.register_count + reg
    }

    /// Resolves one value through trivial Phi aliases.
    #[inline]
    fn resolve(&self, mut value: ValueId) -> ValueId {
        while let Some(&alias) = self.aliases.get(&value) {
            value = alias;
        }
        value
    }

    /// Recursively reads one register and creates a Phi when needed.
    #[must_use]
    fn read_reg_recursive(&mut self, block: usize, reg: u8) -> ValueId {
        let predecessors: Vec<_> = self.graph.predecessors(block).collect();
        if predecessors.is_empty() {
            // No predecessors = MIGHT be the entry block.
            if let Some(value) = self.entry_registers[reg as usize] {
                return value;
            }
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
        let inputs = self.read_inputs(block, reg);
        self.record_inputs(phi, inputs);
        self.remove_trivial_phi(phi)
    }

    /// Reads one register from every predecessor.
    fn read_inputs(&mut self, block: usize, reg: u8) -> Vec<Input> {
        let mut inputs = Vec::new();

        if block == self.graph.entry()
            && let Some(value) = self.entry_registers[reg as usize]
        {
            inputs.push(Input::Entry(value));
        }
        inputs.extend(
            self.graph.predecessors(block).map(|predecessor| {
                Input::Predecessor(predecessor, self.read_reg(predecessor, reg))
            }),
        );

        inputs
    }

    /// Records the inputs and reverse uses of one Phi.
    fn record_inputs(&mut self, phi: ValueId, inputs: Vec<Input>) {
        for input in &inputs {
            self.phi_uses
                .entry(self.resolve(input.value()))
                .or_default()
                .insert(phi);
        }
        self.phi_to_inputs.insert(phi, inputs);
    }

    /// Removes one trivial Phi and revisits dependent Phi values.
    fn remove_trivial_phi(&mut self, phi: ValueId) -> ValueId {
        let Some(inputs) = self.phi_to_inputs.get(&phi) else {
            return self.resolve(phi);
        };

        let mut same = None;
        for input in inputs {
            let input = self.resolve(input.value());
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
            let active_uses: Vec<_> = uses
                .into_iter()
                .filter(|use_value| !self.aliases.contains_key(use_value))
                .collect();
            self.phi_uses
                .entry(replacement)
                .or_default()
                .extend(active_uses.iter().copied());
            for use_value in active_uses {
                self.remove_trivial_phi(use_value);
            }
        }
        replacement
    }

    /// Revisits every surviving Phi after incomplete Phi values are sealed.
    fn remove_remaining_trivial_phis(&mut self) {
        let mut phis: Vec<_> = self.phi_to_inputs.keys().copied().collect();
        phis.sort_unstable();
        for phi in phis {
            if !self.aliases.contains_key(&phi) {
                self.remove_trivial_phi(phi);
            }
        }
    }

    /// Completes Phi values created before all predecessors were filled.
    fn seal_blocks(&mut self) {
        for (block, phis) in std::mem::take(&mut self.incomplete_phis) {
            for (reg, phi) in phis {
                let inputs = self.read_inputs(block, reg);
                self.record_inputs(phi, inputs);
                self.remove_trivial_phi(phi);
            }
        }
    }
}
