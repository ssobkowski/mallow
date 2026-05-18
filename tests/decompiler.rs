use std::ffi::OsString;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use libtest_mimic::{Arguments, Failed, Trial};
use tempfile::TempDir;

fn main() {
    let args = Arguments::from_args();
    let decompile_timeout = parse_timeout_env("MALLOW_TEST_DECOMPILE_TIMEOUT", 5);
    let runtime_timeout = parse_timeout_env("MALLOW_TEST_RUNTIME_TIMEOUT", 10);

    let trials = discover_cases()
        .into_iter()
        .map(|case| {
            Trial::test(case.trial_name(), move || {
                run_case(&case, decompile_timeout, runtime_timeout)
            })
        })
        .collect();

    libtest_mimic::run(&args, trials).exit();
}

fn parse_timeout_env(name: &str, default_secs: u64) -> Duration {
    let default = Duration::from_secs(default_secs);

    std::env::var(name)
        .ok()
        .and_then(|val| val.parse().ok())
        .filter(|&n| n > 0)
        .map(Duration::from_secs)
        .unwrap_or(default)
}

#[derive(Debug, Clone, Copy)]
enum OptLevel {
    O0,
    O1,
    O2,
}

impl OptLevel {
    const ALL: [Self; 3] = [Self::O0, Self::O1, Self::O2];

    const fn flag(self) -> &'static str {
        match self {
            Self::O0 => "O0",
            Self::O1 => "O1",
            Self::O2 => "O2",
        }
    }
}

#[derive(Debug)]
struct Case {
    source_path: PathBuf,
    opt: OptLevel,
}

impl Case {
    fn trial_name(&self) -> String {
        format!(
            "{}/{}",
            self.source_path
                .file_prefix()
                .and_then(|n| n.to_str())
                .unwrap_or("<invalid utf8>"),
            self.opt.flag()
        )
    }
}

enum LuauRunKind {
    Source,
    Decompiled,
}

impl LuauRunKind {
    const fn label(&self) -> &'static str {
        match self {
            Self::Source => "source",
            Self::Decompiled => "decompiled",
        }
    }
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
            Self::DecompileError(msg) => write!(f, "mallow decompile failed:\n{msg}"),
            Self::SourceRunError(msg) => write!(f, "source.luau failed to run:\n{msg}"),
            Self::DecompiledRunError(msg) => write!(f, "decompiled.luau failed to run:\n{msg}"),
            Self::OutputMismatch { source, decompiled } => write!(
                f,
                "output mismatch after decompilation\n--- source ---\n{source}\n--- decompiled ---\n{decompiled}"
            ),
        }
    }
}

fn run_case(
    case: &Case,
    decompile_timeout: Duration,
    runtime_timeout: Duration,
) -> Result<(), Failed> {
    let temp_dir =
        TempDir::new().map_err(|e| Failed::from(format!("failed to create temp dir: {e}")))?;
    let bytecode_path = temp_dir.path().join("compiled.out");
    let decompiled_path = temp_dir.path().join("decompiled.luau");

    compile_luau(&case, &bytecode_path, decompile_timeout)?;
    decompile_bytecode(
        &bytecode_path,
        &decompiled_path,
        // TODO: this is a hack
        case.source_path
            .file_stem()
            .is_some_and(|name| name == "intg-sha2"),
        decompile_timeout,
    )?;

    let source_output = run_luau(&case.source_path, LuauRunKind::Source, runtime_timeout)?;
    let decompiled_output = run_luau(&decompiled_path, LuauRunKind::Decompiled, runtime_timeout)?;

    if source_output != decompiled_output {
        return Err(CaseError::OutputMismatch {
            source: source_output,
            decompiled: decompiled_output,
        }
        .into());
    }

    Ok(())
}

fn run_command_with_timeout(
    mut command: Command,
    timeout: Duration,
    label: &str,
) -> Result<Output, Failed> {
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| Failed::from(format!("failed to spawn {label}: {e}")))?;

    let mut stdout_pipe = child.stdout.take().expect("piped stdout");
    let mut stderr_pipe = child.stderr.take().expect("piped stderr");

    let stdout_thread = thread::spawn(move || {
        let mut buf = Vec::new();
        stdout_pipe.read_to_end(&mut buf).map(|_| buf)
    });
    let stderr_thread = thread::spawn(move || {
        let mut buf = Vec::new();
        stderr_pipe.read_to_end(&mut buf).map(|_| buf)
    });

    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let stdout = stdout_thread
                    .join()
                    .unwrap_or_else(|_| Ok(Vec::new()))
                    .unwrap_or_default();
                let stderr = stderr_thread
                    .join()
                    .unwrap_or_else(|_| Ok(Vec::new()))
                    .unwrap_or_default();
                return Ok(Output {
                    status,
                    stdout,
                    stderr,
                });
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    let _ = stdout_thread.join();
                    let _ = stderr_thread.join();
                    return Err(Failed::from(format!(
                        "{label} timed out after {}s",
                        timeout.as_secs()
                    )));
                }
                thread::sleep(Duration::from_millis(50));
            }
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = stdout_thread.join();
                let _ = stderr_thread.join();
                return Err(Failed::from(format!("failed to wait for {label}: {e}")));
            }
        }
    }
}

fn compile_luau(case: &Case, bytecode_path: &Path, timeout: Duration) -> Result<(), Failed> {
    let mut cmd = Command::new(luau_compile_exe());
    cmd.arg("--binary")
        .arg(&case.source_path)
        .arg(&format!("-{}", case.opt.flag()));
    let output = run_command_with_timeout(cmd, timeout, "luau-compile")?;

    if !output.status.success() {
        return Err(CaseError::CompileError(format_output(&output)).into());
    }

    fs::write(bytecode_path, &output.stdout)
        .map_err(|e| Failed::from(format!("failed to write bytecode: {e}")))?;

    Ok(())
}

fn decompile_bytecode(
    bytecode_path: &Path,
    decompiled_path: &Path,
    spill_locals: bool,
    timeout: Duration,
) -> Result<(), Failed> {
    let mut command = Command::new(mallow_exe());
    command
        .arg("decompile")
        .arg("-i")
        .arg(bytecode_path)
        .arg("-o")
        .arg(decompiled_path);
    if spill_locals {
        command.arg("--spill-locals");
    }

    let output = run_command_with_timeout(command, timeout, "mallow decompile")?;

    if !output.status.success() {
        return Err(CaseError::DecompileError(format_output(&output)).into());
    }

    Ok(())
}

fn run_luau(script_path: &Path, kind: LuauRunKind, timeout: Duration) -> Result<String, Failed> {
    let mut cmd = Command::new(luau_exe());
    cmd.arg(script_path);
    let output = run_command_with_timeout(cmd, timeout, &format!("luau ({})", kind.label()))?;

    if !output.status.success() {
        let err = match kind {
            LuauRunKind::Source => CaseError::SourceRunError(format_output(&output)),
            LuauRunKind::Decompiled => CaseError::DecompiledRunError(format_output(&output)),
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

fn discover_cases() -> Vec<Case> {
    let sources = fs::read_dir(cases_root())
        .unwrap_or_else(|e| panic!("failed to read cases dir: {e}"))
        .filter_map(|entry| {
            let entry = entry.unwrap_or_else(|e| panic!("bad entry: {e}"));
            let path = entry.path();
            (entry.file_type().expect("file type").is_file()
                && path.extension().and_then(|e| e.to_str()) == Some("luau"))
            .then_some(path)
        });

    sources
        .flat_map(|source| {
            OptLevel::ALL.map(|opt| Case {
                source_path: source.clone(),
                opt,
            })
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

fn mallow_exe() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_mallow"))
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
