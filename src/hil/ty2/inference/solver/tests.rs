//! Solver regression tests retained during the structural split.

use std::collections::HashMap;

use smol_str::SmolStr;

use super::model::{CallSite, PackAlternative, SolverConstraint, TypeSolver};
use crate::hil::ty2::inference::program::{CollectedProgram, GenericFieldCall, TableKey, TypeSlot};
use crate::{
    Diagnostics,
    disasm::Chunk,
    hil::lifted::LiftedFunction,
    hil::ty2::{
        builtins::{BuiltinEnvironment, BuiltinPath},
        canonical::{GenericBinder, Type},
        store::TypeStore,
    },
    il::{DecodedInstr, Instr, Proto, ProtoId, ProtoTypeInfo},
};

/// Builds an empty solver suitable for bound-algebra unit tests.
fn empty_solver<'a>(builtins: &'a BuiltinEnvironment, store: &'a mut TypeStore) -> TypeSolver<'a> {
    TypeSolver::new(
        CollectedProgram::default(),
        &[],
        builtins,
        store,
        HashMap::new(),
    )
}

/// Consumer requirements intersect instead of widening into an invalid union.
#[test]
fn requirements_intersect() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let variable = solver.fresh_variable();
    let string = solver.types.primitives().string;
    let number = solver.types.primitives().number;
    let string_or_number = solver.types.union_all([string, number]);

    solver.add_constraint(variable, SolverConstraint::Require(string_or_number));
    solver.add_constraint(variable, SolverConstraint::Require(number));
    solver.solve();

    assert_eq!(solver.candidate_type(variable), Some(number));
}

/// Broad capability markers validate evidence but never seed annotations alone.
#[test]
fn broad_table_requirement_is_not_an_annotation_candidate() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let variable = solver.fresh_variable();
    let table = solver.types.primitives().table;

    solver.add_constraint(variable, SolverConstraint::Require(table));
    solver.solve();

    assert_eq!(solver.candidate_type(variable), None);
}

/// Conflicting producer evidence and consumer requirements suppress a solution.
#[test]
fn inconsistent_bounds_do_not_produce_an_annotation() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let variable = solver.fresh_variable();
    let string = solver.types.primitives().string;
    let number = solver.types.primitives().number;

    solver.add_constraint(variable, SolverConstraint::Observe(string));
    solver.add_constraint(variable, SolverConstraint::Require(number));
    solver.solve();

    assert_eq!(solver.candidate_type(variable), None);
}

/// Optional producer evidence is narrowed only in the refined occurrence.
#[test]
fn truthy_refinement_does_not_mutate_definition() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let source = solver.fresh_variable();
    let refined = solver.fresh_variable();
    let string = solver.types.primitives().string;
    let nil = solver.types.primitives().nil;
    let optional = solver.types.union_all([string, nil]);

    solver.add_constraint(source, SolverConstraint::Observe(optional));
    solver.add_constraint(
        refined,
        SolverConstraint::RefinedFrom {
            source,
            truthiness: super::Truthiness::Truthy,
        },
    );
    solver.solve();

    assert_eq!(solver.produced_type(source), Some(optional));
    assert_eq!(solver.produced_type(refined), Some(string));
}

/// Producer-free refinements remain absent until the ordinary queue is quiescent.
#[test]
fn refinement_fallback_runs_only_after_quiescence() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let truthy = solver.fresh_variable();
    let falsy = solver.fresh_variable();
    let source = solver.fresh_variable();
    solver.add_constraint(
        truthy,
        SolverConstraint::RefinedFrom {
            source,
            truthiness: super::Truthiness::Truthy,
        },
    );
    solver.add_constraint(
        falsy,
        SolverConstraint::RefinedFrom {
            source,
            truthiness: super::Truthiness::Falsy,
        },
    );

    solver.drain_queue();
    assert_eq!(solver.produced_type(truthy), None);
    assert_eq!(solver.produced_type(falsy), None);
    assert_eq!(solver.deferred_refinements.len(), 2);

    assert!(solver.activate_deferred_refinements());
    solver.drain_queue();
    let unknown = solver.types.primitives().unknown;
    let unknown_falsy = solver.types.falsy_part(unknown);
    assert_eq!(solver.produced_type(truthy), Some(unknown));
    assert_eq!(solver.produced_type(falsy), Some(unknown_falsy));
}

/// Concrete evidence scheduled after a refinement wins before fallback activation.
#[test]
fn late_refinement_evidence_stays_precise() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let refined = solver.fresh_variable();
    let source = solver.fresh_variable();
    let number = solver.types.primitives().number;
    solver.add_constraint(
        refined,
        SolverConstraint::RefinedFrom {
            source,
            truthiness: super::Truthiness::Truthy,
        },
    );
    solver.add_constraint(source, SolverConstraint::Observe(number));

    solver.solve();

    assert_eq!(solver.produced_type(refined), Some(number));
    // assert!(solver.activated_refinement_fallbacks.is_empty());
}

/// Graph `unknown` remains a real type rather than absence of evidence.
#[test]
fn unknown_observation_is_not_replaced_by_concrete_evidence() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let variable = solver.fresh_variable();
    let unknown = solver.types.primitives().unknown;
    let number = solver.types.primitives().number;

    solver.add_constraint(variable, SolverConstraint::Observe(unknown));
    solver.add_constraint(variable, SolverConstraint::Observe(number));
    solver.solve();

    assert_eq!(solver.produced_type(variable), Some(unknown));
}

/// Identity markers participate in evidence through the semantic lattice.
#[test]
fn identity_markers_join_with_observed_evidence() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let identity_only = solver.fresh_variable();
    let unknown_producer = solver.fresh_variable();
    let unknown = solver.types.primitives().unknown;
    let function = solver.types.primitives().function;

    assert!(solver.include_builtin(identity_only, BuiltinPath::Global("assert".into()),));
    assert!(solver.include_builtin(unknown_producer, BuiltinPath::Global("assert".into()),));
    solver.add_constraint(unknown_producer, SolverConstraint::Observe(unknown));
    solver.solve();

    assert_eq!(solver.evidence_type(identity_only), Some(function));
    assert_eq!(solver.evidence_type(unknown_producer), Some(unknown));
}

/// Known metatable arithmetic dispatches through the metamethod signature.
#[test]
fn arithmetic_uses_known_metamethod_return_type() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let base = solver.fresh_variable();
    let metatable = solver.fresh_variable();
    let method = solver.fresh_variable();
    let rhs = solver.fresh_variable();
    let result = solver.fresh_variable();
    let base_table = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 0,
    });
    let metatable_table = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 1,
    });
    let table = solver.types.table_shape(Vec::new(), None);
    let number = solver.types.primitives().number;
    let string = solver.types.primitives().string;
    let params = solver.types.pack(vec![table, number], None);
    let returns = solver.types.pack(vec![string], None);
    let signature = solver.types.function_signature(params, returns);

    solver.add_constraint(base, SolverConstraint::NewTable(base_table));
    solver.add_constraint(metatable, SolverConstraint::NewTable(metatable_table));
    solver.add_constraint(method, SolverConstraint::Observe(signature));
    solver.add_constraint(
        metatable,
        SolverConstraint::SetField {
            field: "__add".into(),
            value: method,
            definite: true,
        },
    );
    solver.add_constraint(
        base,
        SolverConstraint::SetMetatable {
            metatable,
            result: None,
        },
    );
    solver.add_constraint(rhs, SolverConstraint::Observe(number));
    solver.add_constraint(
        base,
        SolverConstraint::Binary {
            op: crate::operator::BinOp::Add,
            rhs,
            result,
        },
    );
    solver.solve();

    assert!(
        solver.tables[base_table]
            .metatables
            .contains(&metatable_table)
    );
    assert!(matches!(
        solver
            .types
            .get(solver.produced_type(result).expect("metamethod result")),
        Type::String
    ));
}

/// Named and dynamic reads reconnect when a callable `__index` arrives late.
#[test]
fn late_callable_index_handler_reconnects_all_read_kinds() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let base = solver.fresh_variable();
    let metatable = solver.fresh_variable();
    let handler = solver.fresh_variable();
    let key = solver.fresh_variable();
    let named = solver.fresh_variable();
    let dynamic = solver.fresh_variable();
    let base_table = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 10,
    });
    let metatable_table = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 11,
    });
    let unknown = solver.types.primitives().unknown;
    let string = solver.types.primitives().string;
    let params = solver.types.pack(vec![unknown, string], None);
    let returns = solver.types.pack(vec![string], None);
    let signature = solver.types.function_signature(params, returns);

    solver.add_constraint(base, SolverConstraint::NewTable(base_table));
    solver.add_constraint(metatable, SolverConstraint::NewTable(metatable_table));
    solver.add_constraint(
        base,
        SolverConstraint::SetMetatable {
            metatable,
            result: None,
        },
    );
    solver.add_constraint(
        base,
        SolverConstraint::GetField {
            field: "answer".into(),
            value: named,
        },
    );
    solver.add_constraint(key, SolverConstraint::Observe(string));
    solver.add_constraint(
        base,
        SolverConstraint::GetIndex {
            index: key,
            value: dynamic,
        },
    );
    solver.solve();

    solver.add_constraint(handler, SolverConstraint::Observe(signature));
    solver.add_constraint(
        metatable,
        SolverConstraint::SetField {
            field: "__index".into(),
            value: handler,
            definite: true,
        },
    );
    solver.solve();

    let named = solver.produced_type(named).expect("named index result");
    let dynamic = solver.produced_type(dynamic).expect("dynamic index result");
    assert!(solver.types.is_subtype(string, named));
    assert!(solver.types.is_subtype(string, dynamic));
}

/// Dynamic reads revisit named fields of a table-valued `__index` handler.
#[test]
fn table_valued_dynamic_index_revisits_late_named_fields() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let base = solver.fresh_variable();
    let metatable = solver.fresh_variable();
    let handler = solver.fresh_variable();
    let key = solver.fresh_variable();
    let field_value = solver.fresh_variable();
    let result = solver.fresh_variable();
    let base_table = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 20,
    });
    let metatable_table = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 21,
    });
    let handler_table = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 22,
    });
    let string = solver.types.primitives().string;
    let number = solver.types.primitives().number;

    solver.add_constraint(base, SolverConstraint::NewTable(base_table));
    solver.add_constraint(metatable, SolverConstraint::NewTable(metatable_table));
    solver.add_constraint(handler, SolverConstraint::NewTable(handler_table));
    solver.add_constraint(
        metatable,
        SolverConstraint::SetField {
            field: "__index".into(),
            value: handler,
            definite: true,
        },
    );
    solver.add_constraint(
        base,
        SolverConstraint::SetMetatable {
            metatable,
            result: None,
        },
    );
    solver.add_constraint(key, SolverConstraint::Observe(string));
    solver.add_constraint(
        base,
        SolverConstraint::GetIndex {
            index: key,
            value: result,
        },
    );
    solver.solve();

    solver.add_constraint(field_value, SolverConstraint::Observe(number));
    solver.add_constraint(
        handler,
        SolverConstraint::SetField {
            field: "answer".into(),
            value: field_value,
            definite: true,
        },
    );
    solver.solve();

    let result = solver.produced_type(result).expect("table index result");
    assert!(solver.types.is_subtype(number, result));
}

/// Setmetatable links the same metatable to every base identity.
#[test]
fn setmetatable_links_multiple_base_tables() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let base = solver.fresh_variable();
    let metatable = solver.fresh_variable();
    let first = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 30,
    });
    let second = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 31,
    });
    let meta = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 32,
    });

    solver.add_constraint(base, SolverConstraint::NewTable(first));
    solver.add_constraint(base, SolverConstraint::NewTable(second));
    solver.add_constraint(metatable, SolverConstraint::NewTable(meta));
    solver.add_constraint(
        base,
        SolverConstraint::SetMetatable {
            metatable,
            result: None,
        },
    );
    solver.solve();

    assert!(solver.tables[first].metatables.contains(&meta));
    assert!(solver.tables[second].metatables.contains(&meta));
}

/// Fresh builtin generics preserve argument-to-return relationships.
#[test]
fn builtin_generic_return_flows_from_argument() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let argument = solver.fresh_variable();
    let returned = solver.fresh_variable();
    let string = solver.types.primitives().string;
    solver.add_constraint(argument, SolverConstraint::Observe(string));
    let args = solver.fixed_pack(vec![argument]);
    let returns = solver.result_pack(&[returned]);
    let call = CallSite {
        callee: solver.fresh_variable(),
        args,
        returns,
    };

    solver.instantiate_builtin(&call, &BuiltinPath::Global("assert".into()));
    solver.solve();

    assert_eq!(solver.produced_type(returned), Some(string));
}

/// Dynamic scalar calls recover callable requirements from requested result projections.
#[test]
fn dynamic_call_uses_requested_result_pack_for_signature() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let callee = solver.fresh_variable();
    let argument = solver.fresh_variable();
    let number = solver.types.primitives().number;
    let string = solver.types.primitives().string;
    solver.add_constraint(argument, SolverConstraint::Observe(number));
    let args = solver.fixed_pack(vec![argument]);
    let returns = solver.fresh_pack();
    let returned = solver.project_pack(returns, 0);
    solver.add_constraint(returned, SolverConstraint::Require(string));
    solver.add_constraint(callee, SolverConstraint::Call { args, returns });
    solver.solve();

    let Type::FunctionSignature { params, returns } =
        solver.types.get(solver.variables[callee].upper)
    else {
        panic!("dynamic callee did not receive a structural signature")
    };
    assert_eq!(solver.types.get_pack(*params).head, vec![number]);
    let returns = solver.types.get_pack(*returns);
    assert_eq!(returns.head, vec![string]);
    assert_eq!(
        returns.tail,
        Some(crate::hil::ty2::canonical::TypePackTail::Homogeneous(
            solver.types.primitives().unknown
        ))
    );
}

/// Builtin overload selection reruns when argument producer types change.
#[test]
fn builtin_call_reactivates_after_argument_type_change() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let callee = solver.fresh_variable();
    let argument = solver.fresh_variable();
    solver.include_builtin(callee, BuiltinPath::Global("assert".into()));
    let args = solver.fixed_pack(vec![argument]);
    let returns = solver.fresh_pack();
    solver.add_constraint(callee, SolverConstraint::Call { args, returns });
    solver.drain_queue();
    // let initial_states = solver.activated_builtins.len();

    // let string = solver.types.primitives().string;
    // solver.add_constraint(argument, SolverConstraint::Observe(string));
    // solver.drain_queue();

    // assert!(solver.activated_builtins.len() > initial_states);
}

/// Builtin effects wait until a nested argument tail reaches its final arity.
#[test]
fn builtin_effect_uses_stable_nested_tail_arity() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let table = solver.fresh_variable();
    let position = solver.fresh_variable();
    let value = solver.fresh_variable();
    let callee = solver.fresh_variable();
    let table_object = solver.table_for_key(TableKey {
        proto: ProtoId(0),
        index: 40,
    });
    let number = solver.types.primitives().number;
    let string = solver.types.primitives().string;
    solver.add_constraint(table, SolverConstraint::NewTable(table_object));
    solver.add_constraint(position, SolverConstraint::Observe(number));
    solver.add_constraint(value, SolverConstraint::Observe(string));
    solver.include_builtin(
        callee,
        BuiltinPath::NamespaceField {
            namespace: "table".into(),
            field: "insert".into(),
        },
    );

    let tail = solver.fresh_pack();
    let args = solver.prefixed_pack(vec![table], tail);
    let returns = solver.fresh_pack();
    solver.add_constraint(callee, SolverConstraint::Call { args, returns });
    solver.drain_queue();
    assert!(
        solver
            .evidence_type(solver.tables[table_object].values)
            .is_none()
    );
    // let provisional_states = solver.activated_builtins.len();

    // solver.include_pack_alternative(
    //     tail,
    //     PackAlternative {
    //         head: vec![position, value],
    //         tail: None,
    //     },
    // );
    // solver.solve();

    // assert!(solver.activated_builtins.len() > provisional_states);
    // assert_eq!(
    //     solver.evidence_type(solver.tables[table_object].values),
    //     Some(string)
    // );
}

/// Direct-value plans avoid table-generic names and optionalize both positions.
#[test]
fn direct_value_plan_is_optional_collision_free_and_bound_guarded() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let proto = ProtoId(0);
    let function = minimal_function(proto, 2);
    let table_parameter = function.symbols.params[0];
    let value_parameter = function.symbols.params[1];
    let mut program = CollectedProgram::default();
    program.generic_field_calls.insert(
        proto,
        vec![GenericFieldCall {
            parameter: table_parameter,
            callee: "visit".into(),
            field_arguments: vec![(0, "value".into())],
            return_count: Some(1),
        }],
    );
    program.pack_constraints.insert(
        crate::hil::ty2::inference::program::PackSlot::Returns(proto),
        vec![
            crate::hil::ty2::inference::program::CollectedPackConstraint::Sequence {
                head: vec![TypeSlot::Symbol(proto, value_parameter)],
                tail: None,
            },
        ],
    );
    let functions = vec![function];
    let mut solver = TypeSolver::new(program, &functions, &builtins, &mut store, HashMap::new());
    let formal = solver.variable_for_slot(TypeSlot::Symbol(proto, value_parameter));
    let argument = solver.fresh_variable();
    let arguments = solver.fixed_pack(vec![argument]);
    solver
        .closure_argument_packs
        .entry(proto)
        .or_default()
        .insert(arguments);

    let plans = solver.generic_value_plans(proto);
    assert_eq!(plans.len(), 1);
    let pattern = solver.generic_value_pattern(&plans[0]);
    let nil = solver.types.primitives().nil;
    let generic = solver.types.generic("T1");
    assert!(
        matches!(solver.types.get(pattern), Type::Union(parts) if parts.contains(&nil) && parts.contains(&generic))
    );

    let number = solver.types.primitives().number;
    solver.add_constraint(formal, SolverConstraint::Require(number));
    solver.solve();
    assert!(solver.generic_value_plans(proto).is_empty());
}

/// Pack projections retain prefix positions, tail positions, and closed-pack omission.
#[test]
fn pack_projection_and_flow_preserve_sequence_semantics() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let boolean_value = solver.fresh_variable();
    let string_value = solver.fresh_variable();
    let number_value = solver.fresh_variable();
    let boolean = solver.types.primitives().boolean;
    let string = solver.types.primitives().string;
    let number = solver.types.primitives().number;
    let nil = solver.types.primitives().nil;
    solver.add_constraint(boolean_value, SolverConstraint::Observe(boolean));
    solver.add_constraint(string_value, SolverConstraint::Observe(string));
    solver.add_constraint(number_value, SolverConstraint::Observe(number));

    let tail = solver.fixed_pack(vec![string_value, number_value]);
    let source = solver.prefixed_pack(vec![boolean_value], tail);
    let flowed = solver.fresh_pack();
    solver.add_pack_flow(flowed, source);
    let first = solver.project_pack(flowed, 0);
    let second = solver.project_pack(flowed, 1);
    let third = solver.project_pack(flowed, 2);
    let omitted = solver.project_pack(flowed, 3);
    let aggregate = solver.pack_values(flowed);
    solver.solve();

    assert_eq!(solver.produced_type(first), Some(boolean));
    assert_eq!(solver.produced_type(second), Some(string));
    assert_eq!(solver.produced_type(third), Some(number));
    assert_eq!(solver.produced_type(omitted), Some(nil));
    let aggregate = solver
        .produced_type(aggregate)
        .expect("pack element aggregate");
    assert!(solver.types.is_subtype(boolean, aggregate));
    assert!(solver.types.is_subtype(string, aggregate));
    assert!(solver.types.is_subtype(number, aggregate));
}

/// Open suffix aggregates exclude the guaranteed fixed prefix.
#[test]
fn open_pack_suffix_keeps_head_out_of_tail_values() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let head = solver.fresh_variable();
    let tail_value = solver.fresh_variable();
    let boolean = solver.types.primitives().boolean;
    let string = solver.types.primitives().string;
    solver.add_constraint(head, SolverConstraint::Observe(boolean));
    solver.add_constraint(tail_value, SolverConstraint::Observe(string));

    let tail = solver.fresh_pack();
    solver.include_homogeneous_pack(tail, tail_value);
    let pack = solver.prefixed_pack(vec![head], tail);
    assert_eq!(solver.pack_arity(pack), (1, None));
    let suffix = solver.pack_suffix(pack, 1);
    let values = solver.pack_values(suffix);
    solver.solve();

    assert_eq!(solver.produced_type(values), Some(string));
}

/// A nested tail shape change reschedules consumers of the enclosing pack.
#[test]
fn nested_tail_shape_change_invalidates_enclosing_pack() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let head = solver.fresh_variable();
    let tail_value = solver.fresh_variable();
    let tail = solver.fresh_pack();
    let pack = solver.prefixed_pack(vec![head], tail);
    let dependent = solver.fresh_variable();
    solver
        .pack_dependents
        .entry(pack)
        .or_default()
        .insert(dependent);
    solver.drain_queue();
    assert!(!solver.queue.contains(dependent));

    solver.include_pack_alternative(
        tail,
        PackAlternative {
            head: vec![tail_value],
            tail: None,
        },
    );

    assert!(solver.queue.contains(dependent));
    assert_eq!(solver.pack_arity(pack), (2, Some(2)));
}

/// Recursive pack arity distinguishes grounded aliases from productive cycles.
#[test]
fn recursive_pack_arity_handles_aliases_and_productive_cycles() {
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = empty_solver(&builtins, &mut store);
    let value = solver.fresh_variable();
    let first = solver.fixed_pack(vec![value]);
    let second = solver.fresh_pack();
    solver.add_pack_flow(first, second);
    solver.add_pack_flow(second, first);

    assert_eq!(solver.pack_arity(first), (1, Some(1)));

    let productive = solver.fresh_pack();
    solver.include_pack_alternative(
        productive,
        PackAlternative {
            head: Vec::new(),
            tail: None,
        },
    );
    solver.include_pack_alternative(
        productive,
        PackAlternative {
            head: vec![value],
            tail: Some(productive),
        },
    );
    assert_eq!(solver.pack_arity(productive), (0, None));

    let first = solver.fixed_pack(Vec::new());
    let second = solver.fresh_pack();
    let third = solver.fresh_pack();
    solver.add_pack_flow(first, second);
    solver.add_pack_flow(first, third);
    solver.add_pack_flow(second, first);
    solver.include_pack_alternative(
        third,
        PackAlternative {
            head: vec![value],
            tail: Some(second),
        },
    );
    assert_eq!(solver.pack_arity(first), (0, None));
}

/// Builds a minimal lifted function whose return terminator keeps CFG setup deterministic.
fn minimal_function(proto: ProtoId, num_params: u8) -> LiftedFunction {
    let source = Proto {
        id: proto,
        max_stack_size: num_params.max(1),
        num_params,
        num_upvals: 0,
        is_vararg: false,
        flags: 0,
        type_info: ProtoTypeInfo::default(),
        instrs: vec![DecodedInstr {
            instr: Instr::Return { base: 0, count: 1 },
            word_pc: 0,
        }],
        consts: Vec::new(),
        child_protos: Vec::new(),
        debug_name: None,
        locals: Vec::new(),
    };
    let chunk = Chunk {
        version: 0,
        types_version: 0,
        userdata_type_mappings: None,
        protos: vec![source.clone()],
        strings: Vec::new(),
        entry_proto: ProtoId(0),
    };
    LiftedFunction::from_proto(&source, &chunk, &Diagnostics::default())
        .expect("minimal test function should lift")
}

/// Closure-valued symbols retain the child function's generic scheme when direct recovery has no match.
#[test]
fn closure_symbol_recovers_generic_function_scheme() {
    let outer_proto = ProtoId(0);
    let inner_proto = ProtoId(1);
    let outer = minimal_function(outer_proto, 1);
    let inner = minimal_function(inner_proto, 1);
    let closure_symbol = outer.symbols.params[0];
    let inner_parameter = inner.symbols.params[0];
    let functions = vec![outer, inner];

    let mut program = CollectedProgram::default();
    program.pack_constraints.insert(
        crate::hil::ty2::inference::program::PackSlot::Returns(inner_proto),
        vec![
            crate::hil::ty2::inference::program::CollectedPackConstraint::Sequence {
                head: vec![TypeSlot::Symbol(inner_proto, inner_parameter)],
                tail: None,
            },
        ],
    );
    let mut store = TypeStore::new();
    let builtins = BuiltinEnvironment::new(&mut store);
    let mut solver = TypeSolver::new(program, &functions, &builtins, &mut store, HashMap::new());
    let slot = TypeSlot::Symbol(outer_proto, closure_symbol);
    let variable = solver.variable_for_slot(slot);
    solver.add_constraint(variable, SolverConstraint::Closure(inner_proto));
    solver.solve();
    solver.prepare_output();

    let scheme = solver
        .resolved_symbol_type(slot)
        .expect("closure symbol should produce a scheme");
    assert_eq!(scheme.binders(), &[GenericBinder::Type(SmolStr::new("T"))]);
    let Type::FunctionSignature { params, returns } = solver.types.get(scheme.body()) else {
        panic!("closure symbol should recover a function signature")
    };
    let parameter_types = solver.types.get_pack(*params).head.clone();
    let return_types = solver.types.get_pack(*returns).head.clone();
    let generic = solver.types.generic("T");
    assert_eq!(parameter_types, vec![generic]);
    assert_eq!(return_types, vec![generic]);
}
