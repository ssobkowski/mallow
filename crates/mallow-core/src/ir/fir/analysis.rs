//! Analyses over flat intermediate representation.

use std::collections::HashSet;

use super::{Function, Instr};
use crate::ir::graph::GraphView as _;

/// The location of an instruction inside a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct InstructionLocation {
    /// Block containing the instruction.
    block: usize,
    /// Zero-based position inside the block.
    instruction: usize,
}

/// Table writes that happen while their allocation is still private.
#[derive(Debug, Default)]
pub(crate) struct TableConstructorWrites {
    /// Writes that initialize a fresh table before it can be observed.
    initial_writes: HashSet<InstructionLocation>,
}

impl TableConstructorWrites {
    /// Finds table writes that initialize fresh allocations.
    pub(crate) fn analyze(function: &Function) -> Self {
        let mut analysis = Self::default();

        for block_index in function.cfg.nodes() {
            analysis.analyze_block(block_index, &function.cfg[block_index].instrs);
        }

        analysis
    }

    /// Finds initial writes in one linear instruction sequence.
    fn analyze_block(&mut self, block: usize, instructions: &[Instr]) {
        let mut fresh_tables = HashSet::new();
        for (instruction_index, instruction) in instructions.iter().enumerate() {
            let preserved_table = match instruction {
                Instr::SetTable { table, key, value }
                    if fresh_tables.contains(table) && key != table && value != table =>
                {
                    Some(*table)
                }
                _ => None,
            };
            if preserved_table.is_some() {
                self.initial_writes.insert(InstructionLocation {
                    block,
                    instruction: instruction_index,
                });
            }

            for used in instruction.used_values() {
                if Some(used) != preserved_table {
                    fresh_tables.remove(&used);
                }
            }

            if let Instr::NewTable { out } = instruction {
                fresh_tables.insert(*out);
            }
        }
    }

    /// Returns whether an instruction initializes a fresh table.
    pub(crate) fn contains(&self, block: usize, instruction: usize) -> bool {
        self.initial_writes
            .contains(&InstructionLocation { block, instruction })
    }
}

#[cfg(test)]
mod tests {
    use id_arena::Arena;

    use super::TableConstructorWrites;
    use crate::ir::fir::{Instr, Value};
    use crate::operator::BinOp;

    /// An arbitrary key computation can remain inside table construction.
    #[test]
    fn computed_key_keeps_table_fresh() {
        let mut values = Arena::<Value>::new();
        let table = values.alloc(Value);
        let key = values.alloc(Value);
        let lhs = values.alloc(Value);
        let rhs = values.alloc(Value);
        let value = values.alloc(Value);
        let instructions = [
            Instr::NewTable { out: table },
            Instr::Binary {
                out: key,
                lhs,
                op: BinOp::Add,
                rhs,
            },
            Instr::SetTable { table, key, value },
        ];

        let mut analysis = TableConstructorWrites::default();
        analysis.analyze_block(0, &instructions);

        assert!(analysis.contains(0, 2));
    }

    /// Using a fresh table ends its construction region.
    #[test]
    fn table_use_ends_construction() {
        let mut values = Arena::<Value>::new();
        let table = values.alloc(Value);
        let alias = values.alloc(Value);
        let key = values.alloc(Value);
        let value = values.alloc(Value);
        let instructions = [
            Instr::NewTable { out: table },
            Instr::Copy {
                out: alias,
                value: table,
            },
            Instr::SetTable { table, key, value },
        ];

        let mut analysis = TableConstructorWrites::default();
        analysis.analyze_block(0, &instructions);

        assert!(!analysis.contains(0, 2));
    }

    /// A table cannot initialize itself recursively.
    #[test]
    fn recursive_write_ends_construction() {
        let mut values = Arena::<Value>::new();
        let table = values.alloc(Value);
        let key = values.alloc(Value);
        let instructions = [
            Instr::NewTable { out: table },
            Instr::SetTable {
                table,
                key,
                value: table,
            },
        ];

        let mut analysis = TableConstructorWrites::default();
        analysis.analyze_block(0, &instructions);

        assert!(!analysis.contains(0, 1));
    }
}
