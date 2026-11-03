//! Runs generated programs through Luau and mallow and sorts the results.
//!
//! First the generated program must compile, run cleanly and halt. A failure
//! there is a generator bug. Then, for every optimization level, the program
//! is compiled to bytecode and decompiled by mallow, and the decompiled source
//! must print exactly what the original printed.
//!
//! Decompilation runs in a child process. Then a stack overflow or a hang in
//! mallow only fails one case, and the timeout can kill it.

use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use anyhow::{Context, Result};
use wait_timeout::ChildExt;

use crate::{Config, generate_source};

/// The tools and settings for checking programs.
#[derive(Debug, Clone)]
pub struct Harness {
    /// The `luau` interpreter.
    pub luau: PathBuf,
    /// The `luau-compile` compiler.
    pub compiler: PathBuf,
    /// An executable that runs as `<decompiler> decompile <bytecode file>`
    /// and prints the decompiled source. The `mallow-fuzzer` binary is one.
    pub decompiler: PathBuf,
    /// Optimization levels to compile with before decompiling.
    pub opt_levels: Vec<u8>,
    /// Limit for each process and for each decompilation.
    pub timeout: Duration,
    /// Decompiles and compares output. With this off, only the generator is
    /// checked.
    pub decompile: bool,
}

/// The result of checking one seed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Ok,
    /// The generated program itself is broken, which is a generator bug.
    Generator(Failure),
    /// mallow got something wrong.
    Mallow(Failure),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failure {
    /// A short category such as `runtime-error`. It names the directory the
    /// case is saved in.
    pub kind: String,
    pub detail: String,
    /// Files saved next to the program, as `(file name, contents)`.
    pub files: Vec<(String, Vec<u8>)>,
}

impl Failure {
    fn new(kind: impl Into<String>, detail: String, files: Vec<(String, Vec<u8>)>) -> Self {
        Self {
            kind: kind.into(),
            detail,
            files,
        }
    }
}

impl Outcome {
    /// A label such as `mallow/O1-mismatch`.
    pub fn label(&self) -> String {
        match self {
            Outcome::Ok => "ok".into(),
            Outcome::Generator(failure) => format!("generator/{}", failure.kind),
            Outcome::Mallow(failure) => format!("mallow/{}", failure.kind),
        }
    }

    /// Saves a failing case under `out/<label>/<seed>/` and returns that
    /// directory.
    ///
    /// The directory holds the program, every file of the [`Failure`], and an
    /// `info.txt` with the detail and the `reproduce` command line.
    pub fn save(&self, out: &Path, seed: u64, source: &str, reproduce: &str) -> Result<PathBuf> {
        let failure = match self {
            Outcome::Ok => return Ok(out.to_path_buf()),
            Outcome::Generator(failure) | Outcome::Mallow(failure) => failure,
        };
        let dir = out.join(self.label()).join(seed.to_string());
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("program.luau"), source)?;
        for (name, contents) in &failure.files {
            fs::write(dir.join(name), contents)?;
        }
        fs::write(
            dir.join("info.txt"),
            format!(
                "seed: {seed}\noutcome: {}\nreproduce: {reproduce}\n\n{}\n",
                self.label(),
                failure.detail
            ),
        )?;
        Ok(dir)
    }
}

/// The result of one finished or killed process.
struct Run {
    status: Option<i32>,
    timed_out: bool,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

impl Run {
    fn ok(&self) -> bool {
        !self.timed_out && self.status == Some(0)
    }

    /// The exit status and the last lines of both output streams.
    fn describe(&self) -> String {
        if self.timed_out {
            return "timed out".into();
        }
        let tail = |bytes: &[u8]| {
            let text = String::from_utf8_lossy(bytes);
            let lines: Vec<&str> = text.lines().collect();
            lines[lines.len().saturating_sub(6)..].join("\n")
        };
        format!(
            "exit {:?}\n{}\n{}",
            self.status,
            tail(&self.stderr),
            tail(&self.stdout)
        )
    }

    fn mentions(&self, needle: &str) -> bool {
        let contains = |bytes: &[u8]| String::from_utf8_lossy(bytes).contains(needle);
        contains(&self.stderr) || contains(&self.stdout)
    }
}

impl Harness {
    /// Generates the program for `seed` and checks it.
    ///
    /// `work` is a scratch directory that only this call uses. Returns the
    /// program source along with the outcome.
    pub fn check(&self, seed: u64, config: &Config, work: &Path) -> Result<(String, Outcome)> {
        let source = generate_source(seed, config);
        let outcome = self.check_source(&source, work)?;
        Ok((source, outcome))
    }

    fn check_source(&self, source: &str, work: &Path) -> Result<Outcome> {
        let program = work.join("program.luau");
        fs::write(&program, source)?;

        // The original must compile, run cleanly and halt.
        let compiled = self.run(self.compile(&program), work)?;
        if !compiled.ok() {
            return Ok(Outcome::Generator(Failure::new(
                "syntax-error",
                compiled.describe(),
                Vec::new(),
            )));
        }
        let original = self.run(self.interpret(&program), work)?;
        if !original.ok() {
            let kind = if original.timed_out {
                "timeout"
            } else {
                "runtime-error"
            };
            return Ok(Outcome::Generator(Failure::new(
                kind,
                original.describe(),
                Vec::new(),
            )));
        }
        if !self.decompile {
            return Ok(Outcome::Ok);
        }
        for &level in &self.opt_levels {
            if let Some(failure) = self.check_level(&program, level, &original.stdout, work)? {
                return Ok(failure);
            }
        }
        Ok(Outcome::Ok)
    }

    /// Compiles `program` at `level`, decompiles it and compares the output
    /// with `expected`.
    fn check_level(
        &self,
        program: &Path,
        level: u8,
        expected: &[u8],
        work: &Path,
    ) -> Result<Option<Outcome>> {
        let mut command = Command::new(&self.compiler);
        command
            .arg("--binary")
            .arg(format!("-O{level}"))
            .arg(program);
        let compiled = self.run(command, work)?;
        if !compiled.ok() {
            return Ok(Some(Outcome::Generator(Failure::new(
                format!("O{level}-compile-error"),
                compiled.describe(),
                Vec::new(),
            ))));
        }
        let bytecode_name = format!("program-O{level}.bc");
        let bytecode_path = work.join(&bytecode_name);
        fs::write(&bytecode_path, &compiled.stdout)?;
        let mut files = vec![(bytecode_name, compiled.stdout)];
        let mallow = |kind: &str, detail: String, files: Vec<(String, Vec<u8>)>| {
            Ok(Some(Outcome::Mallow(Failure::new(
                format!("O{level}-{kind}"),
                detail,
                files,
            ))))
        };

        let mut command = Command::new(&self.decompiler);
        command.arg("decompile").arg(&bytecode_path);
        let decompiled = self.run(command, work)?;
        if !decompiled.ok() {
            let kind = if decompiled.timed_out {
                "decompile-timeout"
            } else if decompiled.mentions("overflowed its stack") {
                "decompile-stack-overflow"
            } else if decompiled.status == Some(101) || decompiled.mentions("panicked") {
                "decompile-panic"
            } else {
                "decompile-error"
            };
            return mallow(kind, decompiled.describe(), files);
        }
        let decompiled = decompiled.stdout;
        let decompiled_name = format!("decompiled-O{level}.luau");
        let decompiled_path = work.join(&decompiled_name);
        fs::write(&decompiled_path, &decompiled)?;
        files.push((decompiled_name, decompiled));
        files.push(("expected.txt".into(), expected.to_vec()));

        let recompiled = self.run(self.compile(&decompiled_path), work)?;
        if !recompiled.ok() {
            return mallow("invalid-output", recompiled.describe(), files);
        }
        let rerun = self.run(self.interpret(&decompiled_path), work)?;
        files.push((format!("actual-O{level}.txt"), rerun.stdout.clone()));
        if rerun.timed_out {
            return mallow("output-timeout", rerun.describe(), files);
        }
        if !rerun.ok() {
            let kind = if rerun.mentions("SyntaxError") {
                "invalid-output"
            } else {
                "output-runtime-error"
            };
            return mallow(kind, rerun.describe(), files);
        }
        if rerun.stdout != expected {
            return mallow("mismatch", first_difference(expected, &rerun.stdout), files);
        }
        Ok(None)
    }

    /// `luau-compile --null program`, which only checks syntax.
    fn compile(&self, program: &Path) -> Command {
        let mut command = Command::new(&self.compiler);
        command.arg("--null").arg(program);
        command
    }

    fn interpret(&self, program: &Path) -> Command {
        let mut command = Command::new(&self.luau);
        command.arg(program);
        command
    }

    /// Runs `command` with output captured in files under `work`, killing it
    /// after the timeout.
    fn run(&self, mut command: Command, work: &Path) -> Result<Run> {
        let stdout_path = work.join("stdout");
        let stderr_path = work.join("stderr");
        let mut child = command
            .stdin(Stdio::null())
            .stdout(File::create(&stdout_path)?)
            .stderr(File::create(&stderr_path)?)
            .spawn()
            .with_context(|| format!("spawning {command:?}"))?;
        let (status, timed_out) = match child.wait_timeout(self.timeout)? {
            Some(status) => (status.code(), false),
            None => {
                let _ = child.kill();
                let _ = child.wait();
                (None, true)
            }
        };
        Ok(Run {
            status,
            timed_out,
            stdout: fs::read(&stdout_path)?,
            stderr: fs::read(&stderr_path)?,
        })
    }
}

/// Describes the first output line where `expected` and `actual` differ.
fn first_difference(expected: &[u8], actual: &[u8]) -> String {
    let expected = String::from_utf8_lossy(expected);
    let actual = String::from_utf8_lossy(actual);
    let (mut expected, mut actual) = (expected.lines(), actual.lines());
    let mut line = 1;
    loop {
        match (expected.next(), actual.next()) {
            (Some(e), Some(a)) if e == a => line += 1,
            (e, a) => {
                return format!(
                    "first difference at output line {line}:\n  expected: {}\n  actual:   {}",
                    e.unwrap_or("<end of output>"),
                    a.unwrap_or("<end of output>")
                );
            }
        }
    }
}
