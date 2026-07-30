use std::{path::Path, sync::OnceLock};

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

/// Returns the shared verified Luau toolchain installation.
fn toolchain() -> &'static Installation {
    static TOOLCHAIN: OnceLock<Installation> = OnceLock::new();

    TOOLCHAIN.get_or_init(|| {
        Manager::new()
            .expect("create Luau toolchain manager")
            .install_bytecode(BytecodeVersion::V9)
            .expect("install Luau toolchain for inference tests")
    })
}

/// A truthy cache hit narrows the function's observable return to `number`.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "truthiness01")]
fn inferred_index_read_narrows_after_truthiness_check(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("lookup"),
        ty.function([ty.number()], [ty.number()])
    );
}

/// A local initialized from varargs retains its debug name.
#[inference_test(fixture = "varargs01")]
fn named_vararg_local_keeps_inferred_type(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("value"), ty.number());
}

/// Metamethod-dependent values retain the result type of their operation.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "metatables01")]
fn addition_uses_metatable_method(view: TypesView) {
    let ty = view.types();

    assert_eq!(
        view.local("add_one"),
        ty.function([ty.table([])], [ty.string()])
    );
}

/// Writes through deferred upvalue versions remain optional.
#[ignore = "not yet supported by the ty3 inference engine"]
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

/// Identity remains correlated when an argument is omitted.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "generics01")]
fn identity_with_omitted_argument_recovers_optional_generic(view: TypesView) {
    let ty = view.types();
    let generic = ty.generic("T");
    let identity = ty.function([ty.optional(generic.clone())], [ty.optional(generic)]);

    assert_eq!(view.local("id"), ty.forall(["T"], identity));
    assert_eq!(view.local("a"), ty.number());
    assert_eq!(view.local("b"), ty.nil());
}

/// An unconstrained truthy branch remains in the return type.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "generics02")]
fn unconstrained_truthy_return_is_preserved(view: TypesView) {
    let ty = view.types();
    let generic = ty.generic("T");
    let result = ty.union([generic.clone(), ty.number()]);
    let select = ty.function([generic], [result]);

    assert_eq!(view.local("selectTruthy"), ty.forall(["T"], select));
}

/// Callable `__index` supplies the indexed result type.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "metatables02")]
fn dynamic_index_uses_callable_metamethod(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("resolved"), ty.string());
}

/// A late `__index` link reconnects a named read.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "metatables03")]
fn late_metatable_link_reconnects_named_read(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("resolved"), ty.string());
}

/// Table-valued `__index` supplies the indexed result type.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "metatables04")]
fn dynamic_index_uses_table_metamethod(view: TypesView) {
    let ty = view.types();

    assert_eq!(view.local("resolved"), ty.number());
}

/// Generic results remain independent at each call site.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "generics03")]
fn direct_generic_results_do_not_pool_callsite_types(view: TypesView) {
    let ty = view.types();
    let generic = ty.generic("T");
    let identity = ty.function([generic.clone()], [generic]);

    assert_eq!(view.local("id"), ty.forall(["T"], identity));
    assert_eq!(view.local("number_value"), ty.number());
    assert_eq!(view.local("string_value"), ty.string());
}

/// Aliases and harmless uses preserve an identity relation.
#[ignore = "not yet supported by the ty3 inference engine"]
#[inference_test(fixture = "generics04")]
fn identity_relation_comes_from_body_value_flow(view: TypesView) {
    let ty = view.types();
    let generic = ty.generic("T");
    let identity = ty.function([generic.clone()], [generic]);

    assert_eq!(view.local("id"), ty.forall(["T"], identity));
    assert_eq!(view.local("number_value"), ty.number());
    assert_eq!(view.local("string_value"), ty.string());
}

/// Body requirements prevent false identity generics.
#[inference_test(fixture = "generics05")]
fn body_constraints_prevent_false_identity_generics(view: TypesView) {
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

/// Fixed heads and open tails retain their positional behavior.
#[ignore = "not yet supported by the ty3 inference engine"]
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
