//! Storage shared by FIR values once block parameters are coalesced.
//!
//! An edge argument and the block parameter it binds are emitted as one source
//! local, so every value in such a group reads and writes the same storage.
//! The only exception is the argument which seeds a loop variable, since the
//! loop header itself assigns the variable.

use crate::collections::{HashMap, HashSet, IndexMap, IndexSet};

use super::{BlockExit, Function, Instr, ValueId};
use crate::ir::graph::GraphView;
use crate::ir::union_find::UnionFind;

/// Canonical storage for every value of one function.
#[derive(Debug)]
pub(crate) struct Storage {
    /// Canonical storage for every value.
    storage: IndexMap<ValueId, ValueId>,
    /// Storage assigned by a loop header on every iteration.
    loop_storage: IndexSet<ValueId>,
    /// Storage which is only ever assigned once.
    single_assignment: IndexSet<ValueId>,
}

impl Storage {
    /// Groups the values of one function which will use the same storage.
    pub(crate) fn build(function: &Function) -> Self {
        let cfg = &function.cfg;
        let mut groups = UnionFind::new();
        let mut loop_values = Vec::new();

        // Share the identities between the params from the function signature
        // and the actual identities used in the entry block.
        let entry_block = &cfg[function.entry.target];
        for (argument, parameter) in function.entry.params.iter().zip(&entry_block.params) {
            groups.union(*argument, *parameter);
        }

        for block_index in cfg.post_order() {
            let block = &cfg[block_index];
            for (i, out) in block.params.iter().enumerate() {
                for p in cfg.predecessors(block_index) {
                    let pred_exit = &cfg[p].exit;
                    for edge in pred_exit.edges() {
                        if edge.target == block_index
                            && !initializes_loop_variable(pred_exit, block_index, *out)
                        {
                            groups.union(*out, edge.params[i]);
                        }
                    }
                }
            }

            loop_values.extend(block.exit.defined_values());
            if let BlockExit::GenericFor {
                loop_block,
                variables: init_variables,
                ..
            } = &block.exit
            {
                let BlockExit::GenericForLoop {
                    variables: body_variables,
                    ..
                } = &cfg[*loop_block].exit
                else {
                    unreachable!("raw CFG validation guarantees the generic loop target")
                };

                for (entry, body) in init_variables.iter().zip(body_variables) {
                    groups.union(*entry, *body);
                }
            }
        }

        let storage: IndexMap<_, _> = function
            .values
            .iter()
            .map(|(value, _)| (value, groups.find(value)))
            .collect();
        let loop_storage = loop_values.iter().map(|value| storage[value]).collect();
        let single_assignment = single_assignment_storage(function, &storage);

        Self {
            storage,
            loop_storage,
            single_assignment,
        }
    }

    /// Returns the canonical storage for one value.
    #[inline]
    pub(crate) fn of(&self, value: ValueId) -> ValueId {
        self.storage[&value]
    }

    /// Returns whether a loop header assigns the storage on every iteration.
    #[inline]
    pub(crate) fn is_loop_storage(&self, storage: ValueId) -> bool {
        self.loop_storage.contains(storage)
    }

    /// Returns whether the storage of a value is only ever assigned once.
    #[inline]
    pub(crate) fn is_single_assignment(&self, value: ValueId) -> bool {
        self.single_assignment.contains(self.of(value))
    }
}

/// Returns storage which is only ever assigned once.
///
/// Storage is assigned once when exactly one of its values is defined on entry
/// or by an instruction, and no block exit assigns it.
fn single_assignment_storage(
    function: &Function,
    storage: &IndexMap<ValueId, ValueId>,
) -> IndexSet<ValueId> {
    let instr_defined = function
        .cfg
        .items()
        .flat_map(|block| block.instrs.iter())
        .filter_map(Instr::defined_value);

    // Values live at entry are defined there, whether or not they are parameters.
    let mut definitions = HashMap::default();
    for value in function
        .params
        .iter()
        .chain(&function.entry.params)
        .copied()
        .collect::<HashSet<_>>()
        .into_iter()
        .chain(instr_defined)
    {
        *definitions.entry(storage[&value]).or_insert(0usize) += 1;
    }

    let exit_assigned: IndexSet<_> = function
        .cfg
        .items()
        .flat_map(|block| {
            block
                .outputs
                .iter()
                .copied()
                .chain(block.exit.defined_values())
        })
        .map(|value| storage[&value])
        .collect();

    definitions
        .into_iter()
        .filter(|(storage, count)| *count == 1 && !exit_assigned.contains(storage))
        .map(|(storage, _)| storage)
        .collect()
}

/// Returns whether a loop entry edge argument only seeds the loop variable.
///
/// Such arguments are materialized as the loop header itself rather than as
/// an assignment to shared storage.
pub(crate) fn initializes_loop_variable(
    exit: &BlockExit,
    target: usize,
    parameter: ValueId,
) -> bool {
    match exit {
        BlockExit::NumericFor {
            body_edge,
            variable,
            ..
        } => body_edge.target == target && *variable == parameter,
        BlockExit::GenericFor {
            body_edge,
            variables,
            ..
        } => body_edge.target == target && variables.contains(&parameter),
        _ => false,
    }
}
