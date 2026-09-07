use std::path::Path;
use std::sync::OnceLock;

use mallow_core::TypesView;
use mallow_luau_toolchain::{BytecodeVersion, Installation, Manager};
use mallow_test_macros::inference_test;

/// Builds an inferred type view from one Luau fixture.
fn types_view(source_path: &Path) -> TypesView {
    let compiled = toolchain()
        .compiler()
        .arg("--binary")
        .arg(source_path)
        .arg("-O1")
        .arg("-g2")
        .output()
        .expect("run luau-compile for type-inference test");
    assert!(
        compiled.status.success(),
        "luau-compile rejected inference fixture:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    mallow_core::infer_bytecode_types(&compiled.stdout).expect("infer fixture types")
}

/// Returns the shared Luau release manager without installing a toolchain.
fn manager() -> &'static Manager {
    static MANAGER: OnceLock<Manager> = OnceLock::new();

    MANAGER.get_or_init(|| Manager::new().expect("create Luau toolchain manager"))
}

/// Returns the shared verified Luau toolchain installation.
fn toolchain() -> &'static Installation {
    static TOOLCHAIN: OnceLock<Installation> = OnceLock::new();

    TOOLCHAIN.get_or_init(|| {
        manager()
            .install_bytecode(BytecodeVersion::V9)
            .expect("install Luau toolchain for inference tests")
    })
}

/// A truthy cache hit narrows the function's observable return to `number`.
#[inference_test(fixture = "truthiness01")]
fn inferred_index_read_narrows_after_truthiness_check(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("lookup"),
        ty.function([ty.number()], [ty.number()])
    );
}

/// A truthy fact survives an inner branch and its join.
#[inference_test(fixture = "truthiness02")]
fn truthiness_propagates_through_nested_join(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("through_join"),
        ty.function([ty.optional(ty.number()), ty.boolean()], [ty.number()])
    );
}

/// A contradictory nested branch does not contribute an impossible return.
#[inference_test(fixture = "truthiness03")]
fn contradictory_truthiness_branch_is_unreachable(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("nested_truthiness"),
        ty.function([ty.optional(ty.number())], [ty.number()])
    );
}

/// A call can invalidate the truthiness of a captured local.
#[inference_test(fixture = "truthiness04")]
fn call_invalidates_captured_local_truthiness(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("clear_after_check"),
        ty.function([ty.optional(ty.number())], [ty.optional(ty.number())])
    );
}

/// A by-value capture does not invalidate the parent's branch fact.
#[inference_test(fixture = "truthiness05")]
fn value_capture_preserves_parent_truthiness(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("observe_after_call"),
        ty.function([ty.optional(ty.number())], [ty.number()])
    );
}

/// A reference to an enclosing upvalue shares writes through nested closures.
#[inference_test(fixture = "truthiness06")]
fn upvalue_capture_propagates_shared_storage(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("clear_after_check"),
        ty.function([], [ty.optional(ty.number())])
    );
}

/// A call does not invalidate a read-only by-value upvalue's truthiness.
#[inference_test(fixture = "truthiness07")]
fn call_preserves_value_upvalue_truthiness(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("read_after_call"),
        ty.function([ty.optional(ty.number())], [ty.number()])
    );
}

/// A transitive upvalue capture preserves its read-only value origin.
#[inference_test(fixture = "truthiness08")]
fn call_preserves_transitive_value_upvalue_truthiness(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("read_after_nested_call"),
        ty.function([ty.optional(ty.number())], [ty.number()])
    );
}

/// A local initialized from varargs retains its debug name.
#[inference_test(fixture = "varargs01")]
fn named_vararg_local_keeps_inferred_type(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("value"), ty.number());
}

/// Extra call arguments retain their positions through a variadic function.
#[inference_test(fixture = "varargs02")]
fn variadic_calls_forward_extra_arguments(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("forwarded_string"), ty.string());
    assert_eq!(view.local("forwarded_number"), ty.number());
}

/// Parameters of builtin functions are inferred from their call sites.
#[inference_test(fixture = "builtins01")]
fn builtin_function_parameters_are_inferred(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("substring"), ty.string());
    assert_eq!(view.local("d"), ty.number());
}

/// Metamethod-dependent values retain the result type of their operation.
#[ignore = "not yet supported"]
#[inference_test(fixture = "metatables01")]
fn addition_uses_metatable_method(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("add_one"),
        ty.function([ty.table([])], [ty.string()])
    );
}

/// Writes through deferred upvalue versions remain optional.
#[inference_test(fixture = "upvalues01")]
fn mutable_upvalue_versions_remain_optional(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("read"),
        ty.function([], [ty.optional(ty.number())])
    );
}

/// A table escape makes a field written later optional.
#[inference_test(fixture = "tables01")]
fn escaped_table_write_remains_optional(view: TypesView) {
    let ty = view.types();
    let table = ty.table([("value", ty.optional(ty.number()))]);

    assert_eq!(
        view.local("read_value"),
        ty.function([table], [ty.optional(ty.number())])
    );
}

/// Constructor writes create required fields and indexer values.
#[inference_test(fixture = "tables02")]
fn table_constructor_writes_are_required(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("record"), ty.table([("value", ty.number())]));
    assert_eq!(view.local("indexed"), ty.string());
    assert_eq!(
        view.local("construct"),
        ty.function([ty.number()], [ty.string()])
    );

    let choice = ty.table([("left", ty.number()), ("right", ty.optional(ty.number()))]);
    assert_eq!(view.local("choice"), choice);
    assert_eq!(view.local("choose"), ty.function([ty.boolean()], [choice]));
}

/// Callable `__index` supplies the indexed result type.
#[ignore = "not yet supported"]
#[inference_test(fixture = "metatables02")]
fn dynamic_index_uses_callable_metamethod(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("resolved"), ty.string());
}

/// A late `__index` link reconnects a named read.
#[ignore = "not yet supported"]
#[inference_test(fixture = "metatables03")]
fn late_metatable_link_reconnects_named_read(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("resolved"), ty.string());
}

/// Table-valued `__index` supplies the indexed result type.
#[ignore = "not yet supported"]
#[inference_test(fixture = "metatables04")]
fn dynamic_index_uses_table_metamethod(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("resolved"), ty.number());
}

/// Body requirements prevent false identity relations.
#[inference_test(fixture = "constraints01")]
fn body_constraints_prevent_false_identity_relations(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("numeric"),
        ty.function([ty.number()], [ty.number()])
    );
    assert_eq!(
        view.local("mixed"),
        ty.function(
            [ty.string(), ty.boolean()],
            [ty.union([ty.string(), ty.number()])]
        ),
    );
}

/// Additive branches retain both matching number and vector operands.
#[inference_test(fixture = "arithmetic01")]
fn additive_branches_keep_matching_number_and_vector_types(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("add"),
        ty.function([ty.boolean()], [ty.union([ty.number(), ty.vector()])])
    );
    assert_eq!(
        view.local("subtract"),
        ty.function([ty.boolean()], [ty.union([ty.number(), ty.vector()])])
    );
    assert_eq!(view.local("add_lhs"), ty.union([ty.number(), ty.vector()]));
    assert_eq!(view.local("add_rhs"), ty.union([ty.number(), ty.vector()]));
    assert_eq!(
        view.local("subtract_lhs"),
        ty.union([ty.number(), ty.vector()])
    );
    assert_eq!(
        view.local("subtract_rhs"),
        ty.union([ty.number(), ty.vector()])
    );
}

/// Fixed heads and open tails retain their positional behavior.
#[ignore = "not yet supported"]
#[inference_test(fixture = "packs01")]
fn value_packs_preserve_positional_flow(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("pair"),
        ty.function([], [ty.number(), ty.string()])
    );
    assert_eq!(view.local("a"), ty.boolean());
    assert_eq!(view.local("b"), ty.number());
    assert_eq!(view.local("c"), ty.string());
    assert_eq!(view.local("d"), ty.number());
    assert_eq!(view.local("e"), ty.string());
    assert_eq!(view.local("p"), ty.string());
    assert_eq!(view.local("q"), ty.number());
    assert_eq!(
        view.local("packed_values"),
        ty.indexed_table(
            ty.number(),
            ty.optional(ty.union([ty.number(), ty.string()]))
        ),
    );
}
