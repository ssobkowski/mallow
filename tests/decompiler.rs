use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use libtest_mimic::{Arguments, Failed, Trial};
use tempfile::TempDir;

fn main() {
    let args = Arguments::from_args();
    let trials = discover_cases()
        .into_iter()
        .map(|case| {
            Trial::test(
                case.file_prefix()
                    .and_then(|n| n.to_str())
                    .unwrap_or("<invalid utf8>")
                    .to_string(),
                move || run_case(&case),
            )
        })
        .collect();

    libtest_mimic::run(&args, trials).exit();
}

#[derive(Debug)]
enum CaseError {
    CompileError(String),
    DecompileError(String),
    SourceRunError(String),
    DecompiledRunError(String),
    OutputMismatch { source: String, decompiled: String },
}

impl std::fmt::Display for CaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CompileError(msg) => write!(f, "luau-compile failed:\n{msg}"),
            Self::DecompileError(msg) => write!(f, "luaudec decompile failed:\n{msg}"),
            Self::SourceRunError(msg) => write!(f, "source.luau failed to run:\n{msg}"),
            Self::DecompiledRunError(msg) => write!(f, "decompiled.luau failed to run:\n{msg}"),
            Self::OutputMismatch { source, decompiled } => write!(
                f,
                "output mismatch after decompilation\n--- source ---\n{source}\n--- decompiled ---\n{decompiled}"
            ),
        }
    }
}

fn run_case(source_path: &Path) -> Result<(), Failed> {
    let temp_dir =
        TempDir::new().map_err(|e| Failed::from(format!("failed to create temp dir: {e}")))?;
    let bytecode_path = temp_dir.path().join("compiled.out");
    let decompiled_path = temp_dir.path().join("decompiled.luau");

    compile_luau(&source_path, &bytecode_path)?;
    decompile_bytecode(&bytecode_path, &decompiled_path)?;

    let source_output = run_luau(&source_path, "source.luau")?;
    let decompiled_output = run_luau(&decompiled_path, "decompiled.luau")?;

    if source_output != decompiled_output {
        return Err(CaseError::OutputMismatch {
            source: source_output,
            decompiled: decompiled_output,
        }
        .into());
    }

    Ok(())
}

fn compile_luau(source_path: &Path, bytecode_path: &Path) -> Result<(), Failed> {
    let output = Command::new(luau_compile_exe())
        .arg("--binary")
        .arg(source_path)
        .output()
        .map_err(|e| Failed::from(format!("failed to spawn luau-compile: {e}")))?;

    if !output.status.success() {
        return Err(CaseError::CompileError(format_output(&output)).into());
    }

    fs::write(bytecode_path, &output.stdout)
        .map_err(|e| Failed::from(format!("failed to write bytecode: {e}")))?;

    Ok(())
}

fn decompile_bytecode(bytecode_path: &Path, decompiled_path: &Path) -> Result<(), Failed> {
    let output = Command::new(luaudec_exe())
        .arg("decompile")
        .arg("-i")
        .arg(bytecode_path)
        .arg("-o")
        .arg(decompiled_path)
        .output()
        .map_err(|e| Failed::from(format!("failed to spawn luaudec: {e}")))?;

    if !output.status.success() {
        return Err(CaseError::DecompileError(format_output(&output)).into());
    }

    Ok(())
}

fn run_luau(script_path: &Path, label: &str) -> Result<String, Failed> {
    let output = Command::new(luau_exe())
        .arg(script_path)
        .output()
        .map_err(|e| Failed::from(format!("failed to spawn luau for {label}: {e}")))?;

    if !output.status.success() {
        let err = if label == "source.luau" {
            CaseError::SourceRunError(format_output(&output))
        } else {
            CaseError::DecompiledRunError(format_output(&output))
        };
        return Err(err.into());
    }

    Ok(normalize_output(&String::from_utf8_lossy(&output.stdout)))
}

fn format_output(output: &Output) -> String {
    format!(
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn normalize_output(output: &str) -> String {
    output.replace("\r\n", "\n")
}

fn discover_cases() -> Vec<PathBuf> {
    fs::read_dir(cases_root())
        .unwrap_or_else(|e| panic!("failed to read cases dir: {e}"))
        .filter_map(|entry| {
            let entry = entry.unwrap_or_else(|e| panic!("bad entry: {e}"));
            entry
                .file_type()
                .expect("failed to get the file type")
                .is_file()
                .then_some(entry.path())
        })
        .collect()
}

fn cases_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("cases")
}

fn luau_exe() -> PathBuf {
    find_external_exe("luau")
}
fn luau_compile_exe() -> PathBuf {
    find_external_exe("luau-compile")
}

fn find_external_exe(stem: &str) -> PathBuf {
    let local = repo_root().join(exe_name(stem));
    if local.is_file() {
        return local;
    }
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
