//! Conservative whole-program type inference over lifted SSA HIL.
//!
//! Collection produces a source-level constraint program, the solver reaches a
//! fixed point over the canonical graph and heap identities, and output writes
//! graph-backed schemes back to HIL. Semantic solver domains communicate by
//! enqueuing constraints instead of invoking one another directly.

mod collect;
mod program;
mod queue;
mod solver;

use std::collections::HashMap;

use crate::hil::{
    lifted::LiftedFunction,
    ty2::{builtins::BuiltinEnvironment, canonical::TypeId, store::TypeStore},
};

use collect::collect as collect_function;
use program::CollectedProgram;
pub use program::TypeSlot;
use solver::TypeSolver;

/// Runs whole-program inference and writes conservative symbol annotations back.
pub fn run(functions: &mut [LiftedFunction]) {
    let mut type_store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut type_store);
    let primitives = *type_store.primitives();
    let mut program = CollectedProgram::default();
    for function in functions.iter() {
        program.insert_function(collect_function(function, functions, &builtins, primitives));
    }

    let mut seeds: HashMap<TypeSlot, Vec<TypeId>> = HashMap::new();
    for function in functions.iter() {
        for (symbol, type_id) in function.types.monomorphic_symbol_types() {
            let type_id = type_store.import(function.types.type_store(), type_id);
            seeds
                .entry(TypeSlot::Symbol(function.proto, symbol))
                .or_default()
                .push(type_id);
        }
    }

    let mut solver = TypeSolver::new(program, functions, &builtins, &mut type_store, seeds);
    solver.solve();
    solver.prepare_output();
    let symbol_slots = solver.symbol_slots();
    let inferred: Vec<_> = symbol_slots
        .into_iter()
        .filter_map(|(proto, symbol, slot)| {
            solver
                .resolved_symbol_type(slot)
                .map(|ty| (proto, symbol, ty))
        })
        .collect();
    drop(solver);

    for (proto, symbol, ty) in inferred {
        if let Some(function) = functions.get_mut(proto.0 as usize) {
            function
                .types
                .import_inferred_symbol_type(symbol, &type_store, &ty);
        }
    }
}
