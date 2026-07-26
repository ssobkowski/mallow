//! SSA-first whole-program type inference.
//!
//! Lowering reads lifted SSA, the engine solves immutable relations over a
//! small mutable world, and output imports solved schemes back into functions.

mod engine;
mod keys;
mod lower;
mod output;
mod program;
mod world;

use crate::hil::{
    lifted::LiftedFunction,
    ty2::{builtins::BuiltinEnvironment, store::TypeStore},
};

use engine::Engine;
use keys::ValueKey;
use lower::lower_functions;

/// Runs ty3 inference over lifted SSA and writes inferred symbol schemes.
pub fn run(functions: &mut [LiftedFunction]) {
    let mut type_store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut type_store);
    let primitives = *type_store.primitives();
    let mut program = lower_functions(functions, &builtins, primitives);

    for function in functions.iter() {
        for (symbol, type_id) in function.types.monomorphic_symbol_types() {
            let imported = type_store.import(function.types.type_store(), type_id);
            program.seed(ValueKey::Symbol(function.proto, symbol), imported);
        }
    }

    let mut engine = Engine::new(program, functions, &builtins, &mut type_store);
    engine.solve();
    engine.prepare_output();
    let inferred: Vec<_> = engine
        .symbol_keys()
        .into_iter()
        .filter_map(|(proto, symbol, key)| {
            engine
                .resolved_value_scheme(key)
                .map(|scheme| (proto, symbol, scheme))
        })
        .collect();
    drop(engine);

    for (proto, symbol, scheme) in inferred {
        if let Some(function) = functions.get_mut(proto.0 as usize) {
            function
                .types
                .import_inferred_symbol_type(symbol, &type_store, &scheme);
        }
    }
}
