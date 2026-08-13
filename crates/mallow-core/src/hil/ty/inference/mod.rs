//! SSA-first whole-program type inference.
//!
//! Lowering reads lifted SSA, the engine solves immutable relations over a
//! small mutable world, and output imports solved types back into functions.

// mod captures;
// mod engine;
// mod keys;
// mod lower;
// mod output;
// mod program;
// mod world;

// use engine::Engine;
// use keys::ValueKey;
// use lower::lower_functions;

use crate::hil::lifted::LiftedFunction;
// use crate::hil::ty::builtins::BuiltinEnvironment;
// use crate::hil::ty::store::TypeStore;

/// Runs whole-program type inference over lifted SSA and writes inferred types.
pub fn run(_functions: &mut [LiftedFunction]) {
    // let mut type_store = TypeStore::new();
    // let builtins = BuiltinEnvironment::new(&mut type_store);
    // let primitives = type_store.primitives();
    // let mut program = lower_functions(functions, &builtins, &primitives);

    // for function in functions.iter() {
    //     for (symbol, type_id) in function.types.monomorphic_symbol_types() {
    //         let imported = type_store.import(function.types.type_store(), type_id);
    //         program.seed(ValueKey::Symbol(function.proto, symbol), imported);
    //     }
    // }

    // let mut engine = Engine::new(program, functions, &builtins, &mut type_store);
    // engine.solve();

    // // TODO: Calls below should be one function like `engine.finalize()` that consume
    // //       the engine returning the inferred types. Perhaps include `engine.solve()`
    // //       too, which further allows for a single public function like `solve_types(...)`.
    // engine.prepare_output();

    // let inferred: Vec<_> = engine
    //     .symbol_keys()
    //     .into_iter()
    //     .filter_map(|(proto, symbol, key)| {
    //         engine
    //             .resolved_value_type(key)
    //             .map(|type_id| (proto, symbol, type_id))
    //     })
    //     .collect();
    // drop(engine);

    // for (proto, symbol, type_id) in inferred {
    //     if let Some(function) = functions.get_mut(proto.0 as usize) {
    //         function
    //             .types
    //             .import_inferred_symbol_type(symbol, &type_store, type_id);
    //     }
    // }
}
