use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::TempDir;

#[test]
fn decompile_cases_roundtrip() {
    let cases = discover_cases();
    assert!(!cases.is_empty(), "no test cases found in tests/cases");

    for case_dir in cases {
        run_case(&case_dir);
    }
}

fn discover_cases() -> Vec<PathBuf> {
    let mut cases: Vec<_> = fs::read_dir(cases_root())
        .unwrap_or_else(|error| panic!("failed to read test cases directory: {error}"))
        .filter_map(|entry| {
            let entry =
                entry.unwrap_or_else(|error| panic!("failed to read test case entry: {error}"));
            let path = entry.path();
            path.is_dir().then_some(path)
        })
        .collect();

    cases.sort();
    cases
}

fn run_case(case_dir: &Path) {
    let case_name = case_dir
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("<invalid utf8>");
    let source_path = case_dir.join("source.luau");
    assert!(
        source_path.is_file(),
        "test case '{case_name}' is missing source.luau"
    );

    let expected_output_path = case_dir.join("expected.out");
    let temp_dir =
        TempDir::new().unwrap_or_else(|error| panic!("failed to create temp dir: {error}"));
    let bytecode_path = temp_dir.path().join("compiled.out");
    let decompiled_path = temp_dir.path().join("decompiled.luau");

    compile_luau(&source_path, &bytecode_path, case_name);
    decompile_bytecode(&bytecode_path, &decompiled_path, case_name);

    let source_output = run_luau(&source_path, case_name, "source.luau");
    let decompiled_output = run_luau(&decompiled_path, case_name, "decompiled.luau");

    assert_eq!(
        source_output, decompiled_output,
        "case '{case_name}' produced different output after decompilation"
    );

    if expected_output_path.is_file() {
        let expected_output = normalize_output(
            &fs::read_to_string(&expected_output_path).unwrap_or_else(|error| {
                panic!(
                    "failed to read expected output for case '{case_name}' at {}: {error}",
                    expected_output_path.display()
                )
            }),
        );

        assert_eq!(
            expected_output, source_output,
            "case '{case_name}' source output does not match expected.out"
        );
    }
}

fn compile_luau(source_path: &Path, bytecode_path: &Path, case_name: &str) {
    let output = Command::new(luau_compile_exe())
        .arg("--binary")
        .arg(source_path)
        .output()
        .unwrap_or_else(|error| {
            panic!("failed to run luau-compile.exe for case '{case_name}': {error}")
        });

    assert_command_success(&output, case_name, "luau-compile.exe");

    fs::write(bytecode_path, &output.stdout).unwrap_or_else(|error| {
        panic!(
            "failed to write compiled bytecode for case '{case_name}' to {}: {error}",
            bytecode_path.display()
        )
    });
}

fn decompile_bytecode(bytecode_path: &Path, decompiled_path: &Path, case_name: &str) {
    let output = Command::new(luaudec_exe())
        .arg("decompile")
        .arg("-i")
        .arg(bytecode_path)
        .arg("-o")
        .arg(decompiled_path)
        .output()
        .unwrap_or_else(|error| panic!("failed to run luaudec for case '{case_name}': {error}"));

    assert_command_success(&output, case_name, "luaudec decompile");
}

fn run_luau(script_path: &Path, case_name: &str, label: &str) -> String {
    let output = Command::new(luau_exe())
        .arg(script_path)
        .output()
        .unwrap_or_else(|error| panic!("failed to run luau.exe for case '{case_name}': {error}"));

    assert_command_success(&output, case_name, label);
    normalize_output(&String::from_utf8_lossy(&output.stdout))
}

fn assert_command_success(output: &Output, case_name: &str, command_name: &str) {
    if output.status.success() {
        return;
    }

    panic!(
        "case '{case_name}' failed during {command_name}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn normalize_output(output: &str) -> String {
    output.replace("\r\n", "\n")
}

fn cases_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("cases")
}

/// Returns the path to the `luau` executable.
/// Checks the repo root first, then falls back to looking it up on PATH.
fn luau_exe() -> PathBuf {
    find_external_exe("luau")
}

/// Returns the path to the `luau-compile` executable.
/// Checks the repo root first, then falls back to looking it up on PATH.
fn luau_compile_exe() -> PathBuf {
    find_external_exe("luau-compile")
}

/// Resolves an external executable by name. First checks whether it exists in
/// the repo root (for users who placed it there), and if not, returns just the
/// bare executable name so the OS will resolve it from `PATH`.
fn find_external_exe(stem: &str) -> PathBuf {
    let local = repo_root().join(exe_name(stem));
    if local.is_file() {
        return local;
    }

    // Fall back to bare name — Command will search PATH for it.
    PathBuf::from(exe_name(stem))
}

fn luaudec_exe() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_luaudec"))
}

fn repo_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn exe_name(stem: &str) -> OsString {
    let mut name = OsString::from(stem);
    if cfg!(windows) {
        name.push(".exe");
    }
    name
}
