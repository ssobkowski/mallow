//! Command input: bytecode files are read as-is, Luau source files are compiled first.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, ensure};
use clap::ValueEnum;

#[cfg(feature = "luau-toolchain")]
use crate::toolchain::LuauSelector;

/// How an input file is interpreted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum InputKind {
    /// Luau source, compiled before use.
    Source,
    /// Compiled Luau bytecode.
    Bytecode,
}

/// Input file shared by every command that operates on bytecode.
#[derive(Debug, clap::Args)]
pub struct InputArgs {
    /// Luau source (.luau, .lua) or bytecode file. Source files are compiled first
    input: PathBuf,

    /// Interpret the input as this kind instead of inferring it from the extension
    #[arg(long, value_enum)]
    input_kind: Option<InputKind>,

    /// Compiler settings for source input.
    #[command(flatten)]
    compile: CompileArgs,
}

impl InputArgs {
    /// Returns the input's bytecode, compiling it first when the input is Luau source.
    pub fn bytecode(&self) -> Result<Vec<u8>> {
        match self.kind() {
            InputKind::Source => self.compile.compile(&self.input),
            InputKind::Bytecode => {
                ensure!(
                    !self.compile.is_set(),
                    "compiler options require Luau source input, but `{}` is read as bytecode; \
                     pass `--input-kind source` to compile it",
                    self.input.display()
                );
                std::fs::read(&self.input)
                    .with_context(|| format!("failed to read `{}`", self.input.display()))
            }
        }
    }

    /// Returns the explicit input kind, or infers it from the file extension.
    fn kind(&self) -> InputKind {
        self.input_kind
            .unwrap_or_else(|| match self.input.extension().and_then(OsStr::to_str) {
                Some("luau" | "lua") => InputKind::Source,
                _ => InputKind::Bytecode,
            })
    }
}

/// Luau compiler settings applied to source input.
#[derive(Debug, clap::Args)]
#[command(next_help_heading = "Compilation (source input only)")]
struct CompileArgs {
    /// Optimization level, passed as '-O<n>' to the Luau compiler
    #[arg(short = 'O', long, value_name = "N", value_parser = clap::value_parser!(u8).range(0..=2))]
    opt_level: Option<u8>,

    /// Debug info level, passed as '-g<n>' to the Luau compiler
    #[arg(short = 'g', long, value_name = "N", value_parser = clap::value_parser!(u8).range(0..=2))]
    debug_level: Option<u8>,

    /// Type info level, passed as '-t<n>' to the Luau compiler
    #[arg(short = 't', long, value_name = "N", value_parser = clap::value_parser!(u8).range(0..=1))]
    type_level: Option<u8>,

    /// Compile with a managed Luau release instead of `luau-compile` from PATH. Accepts an exact
    /// release, such as `0.700`, or `bc<N>` for the newest release emitting bytecode version N
    #[cfg(feature = "luau-toolchain")]
    #[arg(long, value_name = "RELEASE")]
    luau: Option<LuauSelector>,
}

impl CompileArgs {
    /// Reports whether any compiler setting was given.
    fn is_set(&self) -> bool {
        let levels =
            self.opt_level.is_some() || self.debug_level.is_some() || self.type_level.is_some();
        #[cfg(feature = "luau-toolchain")]
        let levels = levels || self.luau.is_some();
        levels
    }

    /// Compiles a Luau source file to bytecode.
    fn compile(&self, input: &Path) -> Result<Vec<u8>> {
        let managed = self.managed_compiler()?;
        let is_managed = managed.is_some();
        let mut command = managed.unwrap_or_else(|| Command::new("luau-compile"));

        command.arg("--binary");
        if let Some(opt_level) = self.opt_level {
            command.arg(format!("-O{opt_level}"));
        }
        if let Some(debug_level) = self.debug_level {
            command.arg(format!("-g{debug_level}"));
        }
        if let Some(type_level) = self.type_level {
            command.arg(format!("-t{type_level}"));
        }
        command.arg(input);

        let output = command.output().map_err(|error| {
            if is_managed {
                error.into()
            } else {
                system_compiler_error(error)
            }
        })?;
        ensure!(
            output.status.success(),
            "failed to compile `{}`:\n{}",
            input.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        );

        Ok(output.stdout)
    }

    /// Returns the explicitly selected managed compiler, installing it if needed.
    #[cfg(feature = "luau-toolchain")]
    fn managed_compiler(&self) -> Result<Option<Command>> {
        let Some(luau) = &self.luau else {
            return Ok(None);
        };
        let manager = mallow_luau_toolchain::Manager::new()?;
        Ok(Some(manager.compiler(luau.selector())?))
    }

    /// Returns no managed compiler, because the toolchain is not built in.
    #[cfg(not(feature = "luau-toolchain"))]
    fn managed_compiler(&self) -> Result<Option<Command>> {
        Ok(None)
    }
}

/// Adds installation guidance when the PATH compiler does not exist.
fn system_compiler_error(error: std::io::Error) -> anyhow::Error {
    if error.kind() != std::io::ErrorKind::NotFound {
        return error.into();
    }

    #[cfg(feature = "luau-toolchain")]
    {
        anyhow::anyhow!(
            "could not find `luau-compile` in PATH; install the Luau toolchain yourself and add `luau-compile` to PATH, or select a managed compiler with `--luau`"
        )
    }
    #[cfg(not(feature = "luau-toolchain"))]
    {
        anyhow::anyhow!(
            "could not find `luau-compile` in PATH; install the Luau toolchain yourself and add `luau-compile` to PATH, or rebuild mallow with the `luau-toolchain` feature and select a managed compiler"
        )
    }
}
