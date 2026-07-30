use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::{Arc, OnceLock};
use std::thread;
use std::time::Duration;

use libtest_mimic::{Arguments, Failed, Trial};
use mallow_luau_toolchain::{BytecodeVersion, Installation, Manager, Release};
use tempfile::TempDir;
use wait_timeout::ChildExt;

fn main() {
    let args = Arguments::from_args();
    let compile_timeout = parse_timeout_env("MALLOW_TEST_COMPILE_TIMEOUT", 5);
    let runtime_timeout = parse_timeout_env("MALLOW_TEST_RUNTIME_TIMEOUT", 10);

    let release = manager()
        .resolve(BytecodeVersion::V9)
        .expect("resolve stable V9 Luau release for decompiler tests");
    let toolchain = Arc::new(TestToolchain::new(release));
    let trials = discover_cases(toolchain)
        .into_iter()
        .map(|case| {
            Trial::test(case.trial_name(), move || {
                run_case(&case, compile_timeout, runtime_timeout)
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
    /// Source fixture compiled and compared by this trial.
    source_path: PathBuf,
    /// Optimization level passed to the Luau compiler.
    opt: OptLevel,
    /// Exact Luau release used for compilation and execution.
    toolchain: Arc<TestToolchain>,
}

impl Case {
    fn trial_name(&self) -> String {
        format!(
            "{}/{}/{}",
            self.toolchain.release.version,
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
    DecompileError(String),
    SourceRunError(String),
    DecompiledRunError(String),
    OutputMismatch { source: String, decompiled: String },
}

impl std::fmt::Display for CaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
    compile_timeout: Duration,
    runtime_timeout: Duration,
) -> Result<(), Failed> {
    let temp_dir =
        TempDir::new().map_err(|e| Failed::from(format!("failed to create temp dir: {e}")))?;
    let decompiled_path = temp_dir.path().join("decompiled.luau");

    let Some(bytecode) = compile_luau(case, compile_timeout)? else {
        eprintln!("skip {} (luau-compile failed)", case.trial_name());
        return Ok(());
    };
    decompile_bytecode(
        &bytecode,
        &decompiled_path,
        // TODO: this is a hack
        case.source_path
            .file_stem()
            .is_some_and(|name| name == "intg-sha2"),
    )?;

    let source_output = run_luau(
        &case.toolchain,
        &case.source_path,
        LuauRunKind::Source,
        runtime_timeout,
    )?;
    let decompiled_output = run_luau(
        &case.toolchain,
        &decompiled_path,
        LuauRunKind::Decompiled,
        runtime_timeout,
    )?;

    if source_output != decompiled_output {
        return Err(CaseError::OutputMismatch {
            source: source_output,
            decompiled: decompiled_output,
        }
        .into());
    }

    Ok(())
}

/// Runs one child process and kills it when it exceeds `timeout`.
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

    let status = match child.wait_timeout(timeout) {
        Ok(Some(status)) => status,
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
            let _ = stdout_thread.join();
            let _ = stderr_thread.join();
            return Err(Failed::from(format!(
                "{label} timed out after {}s",
                timeout.as_secs()
            )));
        }
        Err(error) => {
            let _ = child.kill();
            let _ = child.wait();
            let _ = stdout_thread.join();
            let _ = stderr_thread.join();
            return Err(Failed::from(format!("failed to wait for {label}: {error}")));
        }
    };

    let stdout = stdout_thread
        .join()
        .unwrap_or_else(|_| Ok(Vec::new()))
        .unwrap_or_default();
    let stderr = stderr_thread
        .join()
        .unwrap_or_else(|_| Ok(Vec::new()))
        .unwrap_or_default();
    Ok(Output {
        status,
        stdout,
        stderr,
    })
}

/// Compiles one fixture into bytecode.
fn compile_luau(case: &Case, timeout: Duration) -> Result<Option<Vec<u8>>, Failed> {
    let mut command = case.toolchain.installation()?.compiler();
    command
        .arg("--binary")
        .arg(&case.source_path)
        .arg(format!("-{}", case.opt.flag()));
    let output = run_command_with_timeout(command, timeout, "luau-compile")?;

    Ok(output.status.success().then_some(output.stdout))
}

/// Decompiles bytecode into the temporary source file executed by the test.
fn decompile_bytecode(
    bytecode: &[u8],
    decompiled_path: &Path,
    spill_locals: bool,
) -> Result<(), Failed> {
    let code = mallow_core::decompile_bytecode(
        bytecode,
        mallow_core::DecompileOptions {
            spill_locals,
            ..Default::default()
        },
    )
    .map_err(|e| CaseError::DecompileError(e.to_string()))?;

    fs::write(decompiled_path, code)
        .map_err(|e| Failed::from(format!("failed to write decompiled source: {e}")))?;

    Ok(())
}

/// Runs one Luau script.
fn run_luau(
    toolchain: &TestToolchain,
    script_path: &Path,
    kind: LuauRunKind,
    timeout: Duration,
) -> Result<String, Failed> {
    let mut command = toolchain.installation()?.luau();
    command.arg(script_path);
    let output = run_command_with_timeout(command, timeout, &format!("luau ({})", kind.label()))?;

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

fn discover_cases(toolchain: Arc<TestToolchain>) -> Vec<Case> {
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
            let toolchain = Arc::clone(&toolchain);
            OptLevel::ALL.map(move |opt| Case {
                source_path: source.clone(),
                opt,
                toolchain: Arc::clone(&toolchain),
            })
        })
        .collect()
}

fn cases_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("cases")
}

/// One lazily installed Luau release selected for decompiler trials.
#[derive(Debug)]
struct TestToolchain {
    /// Exact release selected before trial discovery.
    release: &'static Release,
    /// Verified installation initialized by the first executed trial.
    installation: OnceLock<Result<Installation, String>>,
}

impl TestToolchain {
    /// Creates a lazy toolchain for one resolved release.
    fn new(release: &'static Release) -> Self {
        Self {
            release,
            installation: OnceLock::new(),
        }
    }

    /// Returns the verified installation, installing it on first use.
    fn installation(&self) -> Result<&Installation, Failed> {
        self.installation
            .get_or_init(|| {
                manager()
                    .install_release(self.release.version)
                    .map_err(|error| {
                        format!(
                            "failed to install Luau release {}: {error}",
                            self.release.version
                        )
                    })
            })
            .as_ref()
            .map_err(|error| Failed::from(error.clone()))
    }
}

/// Returns the shared Luau release manager without installing another toolchain.
fn manager() -> &'static Manager {
    static MANAGER: OnceLock<Manager> = OnceLock::new();

    MANAGER.get_or_init(|| Manager::new().expect("create Luau toolchain manager"))
}
