use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use tempfile::TempDir;

/// Compiles `source`, decompiles it with inference, and validates the result.
fn infer_and_analyze(source: &str) -> String {
    let temp = TempDir::new().expect("create type-inference test directory");
    let bytecode = compile_source(source, &temp);
    let decompiled = infer_bytecode(&bytecode);
    analyze_source(&decompiled, &temp);
    decompiled
}

/// Compiles one source fixture to Luau bytecode in `temp`.
fn compile_source(source: &str, temp: &TempDir) -> Vec<u8> {
    let source_path = temp.path().join("source.luau");
    fs::write(&source_path, source).expect("write type-inference source");

    let compiled = Command::new(external_executable("luau-compile"))
        .arg("--binary")
        .arg(&source_path)
        .arg("-O1")
        .output()
        .expect("run luau-compile for type-inference test");
    assert!(
        compiled.status.success(),
        "luau-compile rejected inference fixture:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    compiled.stdout
}

/// Decompiles bytecode with whole-program inference enabled.
fn infer_bytecode(bytecode: &[u8]) -> String {
    mallow::decompile_bytecode(
        bytecode,
        mallow::DecompileOptions {
            infer_types: true,
            ..Default::default()
        },
    )
    .expect("decompile type-inference fixture")
}

/// Requires `luau-analyze` to accept one inferred source string.
fn analyze_source(decompiled: &str, temp: &TempDir) {
    let output_path = temp.path().join("decompiled.luau");
    fs::write(&output_path, decompiled).expect("write inferred Luau output");

    let analyzed = Command::new(external_executable("luau-analyze"))
        .arg(&output_path)
        .output()
        .expect("run luau-analyze for inferred output");
    assert!(
        analyzed.status.success(),
        "luau-analyze rejected inferred output:\n{}\n--- output ---\n{decompiled}",
        String::from_utf8_lossy(&analyzed.stderr)
    );
}

/// Finds one Luau executable beside the repository or through `PATH`.
fn external_executable(stem: &str) -> PathBuf {
    let local = Path::new(env!("CARGO_MANIFEST_DIR")).join(executable_name(stem));
    if local.is_file() {
        local
    } else {
        PathBuf::from(executable_name(stem))
    }
}

/// Returns the platform-specific executable filename for `stem`.
fn executable_name(stem: &str) -> OsString {
    let mut name = OsString::from(stem);
    if cfg!(windows) {
        name.push(".exe");
    }
    name
}

/// A truthy cache hit narrows the function's observable return to `number`.
#[test]
fn inferred_index_read_narrows_after_truthiness_check() {
    let output = infer_and_analyze(
        r#"
local memo = {}

local function lookup(n)
    local cached = memo[n]
    if cached then
        return cached
    end
    memo[n] = n
    return n
end

print(lookup(1), lookup(2))
"#,
    );

    assert!(
        output.contains("local function v1(p0: number): number"),
        "the cache lookup did not recover its numeric contract:\n{output}"
    );
}

/// Metamethod-dependent values are not annotated as their incomplete base table type.
#[test]
fn inferred_metamethod_program_analyzes() {
    infer_and_analyze(
        r#"
local value = {}
setmetatable(value, {
    __add = function(_, rhs)
        return tostring(rhs)
    end,
})

local function add_one(input)
    return input + 1
end

print(add_one(value))
"#,
    );
}

/// Writes through deferred upvalue versions remain nonlocal and optional.
#[test]
fn mutable_upvalue_versions_remain_nonlocal_storage() {
    let output = infer_and_analyze(
        r#"
local state

local function write()
    state = {}
    state.value = 1
end

local function read()
    return state.value
end

write()
print(read())
"#,
    );

    assert!(
        output.contains("local function v2(): nil | number"),
        "an upvalue write was mistaken for definite local construction:\n{output}"
    );
}

/// Recursive arithmetic must not depend on randomized worklist insertion order.
#[test]
fn recursive_memo_table_inference_is_deterministic() {
    let temp = TempDir::new().expect("create recursive inference test directory");
    let bytecode = compile_source(include_str!("../fib.luau"), &temp);
    let mut previous = None;

    for iteration in 0..24 {
        let output = infer_bytecode(&bytecode);
        assert!(
            output.contains("local function v1(p0: number): number"),
            "iteration {iteration} lost recursive numeric inference:\n{output}"
        );
        if let Some(previous) = &previous {
            assert_eq!(
                &output, previous,
                "iteration {iteration} emitted nondeterministic inferred output"
            );
        }
        analyze_source(&output, &temp);
        previous = Some(output);
    }
}

/// Same-table callback/data fields retain their relationship as a generic.
#[test]
fn correlated_table_callback_recovers_generic_signature() {
    let output = infer_and_analyze(include_str!("../type-playground.luau"));

    assert!(
        output.contains("local function v4(p0: boolean, p1: string): string"),
        "the earlier closure lost its annotations during local-slot reuse:\n{output}"
    );
    assert!(
        output.contains("local function v5<T>(p0: { data: T, f: (T) -> () }, ...): ()"),
        "correlated callback fields were flattened into unrelated unions:\n{output}"
    );
    assert!(
        output.contains("function(p0: number)"),
        "numeric callback parameter was not recovered:\n{output}"
    );
    assert!(
        output.contains("function(p0: { [number]: nil | number | string })")
            || output.contains("function(p0: { [number]: nil | string | number })"),
        "table callback parameter was not recovered:\n{output}"
    );
}

/// A table read or escape ends constructor initialization for later writes.
#[test]
fn escaped_table_write_remains_optional() {
    let output = infer_and_analyze(
        r#"
local function read_value(table)
    return table.value
end

local table = {}
print(read_value(table))
table.value = 42
print(read_value(table))
"#,
    );

    assert!(
        output.contains("nil | number"),
        "a post-escape mutation was mistaken for definite initialization:\n{output}"
    );
}

/// Direct identity closures retain argument-to-return correlation across omitted calls.
#[test]
fn identity_with_omitted_argument_recovers_optional_generic() {
    let output = infer_and_analyze(include_str!(
        "inference-cases/identity-omitted-argument.luau"
    ));

    assert!(
        output.contains("local function v0<T>(p0: nil | T): nil | T")
            || output.contains("local function v0<T>(p0: T | nil): T | nil"),
        "identity parameter and return were not tied by one optional generic:\n{output}"
    );
    assert!(
        output.contains("local v1 = v0(1)") || output.contains("print(v0(1),"),
        "the present identity call was neither retained nor inlined cleanly:\n{output}"
    );
    assert!(
        output.contains("local v2 = v0()") || output.contains("(v0()))"),
        "the omitted identity call was neither retained nor inlined cleanly:\n{output}"
    );
}

/// Unconstrained truthy values remain represented in the recovered return type.
#[test]
fn unconstrained_truthy_return_does_not_narrow_to_other_branches() {
    let output = infer_and_analyze(include_str!(
        "inference-cases/unconstrained-truthy-return.luau"
    ));

    assert!(
        !output.contains("local function v0(p0): number"),
        "an unconstrained truthy return path disappeared:\n{output}"
    );
}

/// Callable `__index` output remains accepted without a duplicate result annotation.
#[test]
fn dynamic_index_uses_callable_metamethod() {
    let output = infer_and_analyze(include_str!(
        "inference-cases/dynamic-index-metamethod.luau"
    ));

    assert!(
        !output.contains("unknown"),
        "callable `__index` leaked an unresolved annotation:\n{output}"
    );
}

/// A late `__index` link remains accepted without a duplicate read annotation.
#[test]
fn late_metatable_link_reconnects_named_read() {
    let output = infer_and_analyze(include_str!("inference-cases/late-index-metamethod.luau"));

    assert!(
        !output.contains("unknown"),
        "late `__index` linkage leaked an unresolved annotation:\n{output}"
    );
}

/// Table-valued `__index` output remains accepted without a duplicate result annotation.
#[test]
fn dynamic_index_uses_table_metamethod() {
    let output = infer_and_analyze(include_str!("inference-cases/table-index-metamethod.luau"));

    assert!(
        !output.contains("unknown"),
        "table-valued `__index` leaked an unresolved annotation:\n{output}"
    );
}

/// Direct generic results remain correlated independently at each callsite.
#[test]
fn direct_generic_pack_results_do_not_pool_callsite_types() {
    let output = infer_and_analyze(
        r#"
local function id(value)
    return value
end
local number_value = id(1)
local string_value = id("x")
print(number_value + 1, string.upper(string_value))
"#,
    );

    assert!(
        output.contains("local function v0<T>(p0: T): T"),
        "the identity pack lost its direct generic relation:\n{output}"
    );
}

/// Body value flow preserves identity through aliases and harmless uses.
#[test]
fn identity_relation_comes_from_body_value_flow() {
    let output = infer_and_analyze(
        r#"
local function id(value)
    print(value)
    local alias = value
    return alias
end
local number_value = id(1)
local string_value = id("x")
print(number_value + 1, string.upper(string_value))
"#,
    );

    assert!(
        output.contains("local function v0<T>(p0: T): T"),
        "body value flow did not preserve the identity relation:\n{output}"
    );
}

/// Mixed producers and body requirements do not become unconstrained generics.
#[test]
fn body_constraints_prevent_false_identity_generics() {
    let output = infer_and_analyze(
        r#"
local function mixed(value, condition)
    if condition then
        return value
    end
    return 1
end
local function numeric(value)
    local unused = value + 1
    return value
end
print(mixed("x", true), numeric(2))
"#,
    );

    assert!(
        !output.contains("function v0<T>") && !output.contains("function v1<T>"),
        "a mixed or constrained return became an unconstrained generic:\n{output}"
    );
    assert!(
        output.contains("function v1(p0: number): number"),
        "the body numeric requirement did not beat call evidence:\n{output}"
    );
}

/// Fixed heads and open tails retain their distinct positional behavior.
#[test]
fn value_packs_preserve_assignment_call_return_and_table_flow() {
    let output = infer_and_analyze(include_str!("inference-cases/value-packs.luau"));

    assert!(
        output.contains("local function v0(): (number, string)"),
        "the fixed two-result producer lost its return pack:\n{output}"
    );
    assert!(
        output.contains("local function v1<T, T1, T2>(p0: T, p1: T1, p2: T2): (T, T1, T2)"),
        "the open argument tail did not fill all fixed parameters:\n{output}"
    );
    assert!(
        output.contains("local v3, v4 = v0()")
            && output.contains("local v5 = v0()")
            && output.contains("local v7 = v0()")
            && output.contains("local v8 = nil"),
        "fixed and open assignment contexts were flattened together:\n{output}"
    );
    assert!(
        output.contains("take = function<T, T1>(p0, p1: T, p2: T1)"),
        "the method receiver displaced its open user-argument pack:\n{output}"
    );
    assert!(
        output.contains("local function v14(...): (string, number)"),
        "vararg forwarding lost the positional result types:\n{output}"
    );
    assert!(
        output.contains("local v10 = {\n    true,\n    v0()\n}")
            && (output.contains("local function v17(): { [number]: nil | number | string }")
                || output.contains("local function v17(): { [number]: nil | string | number }")),
        "open table constructor tails were collapsed to one scalar value:\n{output}"
    );
}

/// Real-world MD5 inference stays concise while retaining its useful contracts.
#[test]
fn md5_inference_recovers_numeric_and_table_contracts_without_unknown() {
    let output = infer_and_analyze(include_str!("cases/intg-md5.luau"));

    assert!(
        !output.contains("unknown"),
        "MD5 inference emitted unresolved placeholder types:\n{output}"
    );
    assert!(
        output.contains("local v0: number\n            if p0 <= 2147483647 then"),
        "the conditional Phi target was destructed before numeric inference:\n{output}"
    );
    assert!(
        output.contains("local function v32(p0: string, ...): { [number]: nil | number }"),
        "`table.insert` did not propagate its numeric element into the returned table:\n{output}"
    );
    assert!(
        output.contains("local v35 = function(p0: number, p1: number, p2: number)"),
        "numeric bit-operation parameters were not recovered:\n{output}"
    );
    assert!(
        output.contains("local v39 = function(p0: (number, number, number) -> number, p1: number"),
        "the MD5 round callback signature remained unresolved:\n{output}"
    );
    assert!(
        output.contains("local v43 = v0.new()"),
        "the constructor call repeated its inferred object type:\n{output}"
    );
}
