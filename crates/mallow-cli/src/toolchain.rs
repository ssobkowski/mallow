//! Managed Luau release selection and the `toolchain` subcommand.

use std::ffi::OsString;
use std::io::Write;
use std::process::ExitCode;
use std::str::FromStr;

use anyhow::{Context, Result};
use clap::{Subcommand, ValueEnum};
use mallow_luau_toolchain::{BytecodeVersion, Manager, Registry, Tool, VersionSelector};

/// Selects a managed Luau release by exact version or emitted bytecode format.
#[derive(Debug, Clone)]
pub enum LuauSelector {
    /// An exact upstream release, such as `0.700`.
    Release(String),
    /// The newest release emitting a bytecode version, written as `bc<N>`.
    Bytecode(BytecodeVersion),
}

impl FromStr for LuauSelector {
    type Err = String;

    /// Parses `bc<N>` as a bytecode selector and anything else as an exact release.
    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value.strip_prefix("bc") {
            Some(number) => parse_bytecode(number).map(Self::Bytecode),
            None => Ok(Self::Release(value.to_owned())),
        }
    }
}

impl LuauSelector {
    /// Returns the matching library selector.
    pub fn selector(&self) -> VersionSelector<'_> {
        match self {
            Self::Release(version) => VersionSelector::release(version),
            Self::Bytecode(bytecode) => VersionSelector::bytecode(*bytecode),
        }
    }
}

/// Parses a bytecode version supported by the managed Luau registry.
fn parse_bytecode(value: &str) -> Result<BytecodeVersion, String> {
    let number = value
        .parse::<u8>()
        .map_err(|_| format!("expected a bytecode version number, got '{value}'"))?;
    BytecodeVersion::try_from(number).map_err(|error| error.to_string())
}

/// Command-line name of one tool shipped in a Luau release.
#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum CliTool {
    /// The Luau interpreter.
    Luau,
    /// The Luau static analyzer.
    Analyze,
    /// The Luau compiler.
    Compile,
    /// The Luau AST parser.
    Ast,
}

impl From<CliTool> for Tool {
    fn from(tool: CliTool) -> Self {
        match tool {
            CliTool::Luau => Self::Luau,
            CliTool::Analyze => Self::Analyze,
            CliTool::Compile => Self::Compile,
            CliTool::Ast => Self::Ast,
        }
    }
}

/// Managed Luau release commands.
///
/// Releases are written as an exact version, such as `0.700`, or as `bc<N>` for the newest
/// release emitting bytecode version N.
#[derive(Debug, Subcommand)]
pub enum ToolchainCommand {
    /// List installed releases, newest first
    List {
        /// Only list releases emitting this bytecode version
        #[arg(long, value_name = "N", value_parser = parse_bytecode)]
        bytecode: Option<BytecodeVersion>,

        /// List every registry release, not just installed ones
        #[arg(long)]
        all: bool,
    },
    /// Download and verify releases
    Install {
        /// Releases to install
        #[arg(required = true, value_name = "RELEASE")]
        releases: Vec<LuauSelector>,
    },
    /// Remove installed releases
    Uninstall {
        /// Releases to remove
        #[arg(required = true, value_name = "RELEASE")]
        releases: Vec<LuauSelector>,
    },
    /// Print a release's installation directory or tool path, installing it if needed.
    /// Prints the cache root when no release is given
    Path {
        /// Release to locate
        release: Option<LuauSelector>,

        /// Print this tool's path instead of the installation directory
        #[arg(long, value_enum, requires = "release")]
        tool: Option<CliTool>,
    },
    /// Run a tool from a release, installing it if needed
    Run {
        /// Release providing the tool
        release: LuauSelector,

        /// Tool to run
        #[arg(value_enum)]
        tool: CliTool,

        /// Arguments passed to the tool
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<OsString>,
    },
    /// Remove cache entries that are not valid installations, such as interrupted installs and
    /// directories left by older cache layouts
    Prune,
}

impl ToolchainCommand {
    /// Runs the command, returning the exit code of a spawned tool when there is one.
    pub fn run(self) -> Result<ExitCode> {
        let manager = Manager::new()?;
        let mut out = std::io::stdout().lock();

        match self {
            Self::List { bytecode, all } => {
                for release in Registry::releases()
                    .iter()
                    .filter(|release| bytecode.is_none_or(|bytecode| release.bytecode == bytecode))
                {
                    let status = if !release.is_available() {
                        "unavailable"
                    } else if manager.installed(release.version)?.is_some() {
                        "installed"
                    } else {
                        ""
                    };
                    if !all && status != "installed" {
                        continue;
                    }

                    let line = format!("{:<8} bc{:<3} {status}", release.version, release.bytecode);
                    writeln!(out, "{}", line.trim_end())?;
                }
            }
            Self::Install { releases } => {
                for release in &releases {
                    let installation = manager.install(release.selector())?;
                    let release = installation.release();
                    writeln!(
                        out,
                        "{} (bc{}) {}",
                        release.version,
                        release.bytecode,
                        installation.path().display()
                    )?;
                }
            }
            Self::Uninstall { releases } => {
                for selector in &releases {
                    let release = manager.resolve(selector.selector())?;
                    if manager.uninstall(release.version)? {
                        writeln!(out, "removed {}", release.version)?;
                    } else {
                        writeln!(out, "{} is not installed", release.version)?;
                    }
                }
            }
            Self::Path { release, tool } => {
                let Some(release) = release else {
                    writeln!(out, "{}", manager.cache_root().display())?;
                    return Ok(ExitCode::SUCCESS);
                };
                let installation = manager.install(release.selector())?;
                let path = match tool {
                    None => installation.path().to_path_buf(),
                    Some(CliTool::Ast) => installation.ast_path().with_context(|| {
                        format!(
                            "release {} does not ship luau-ast",
                            installation.release().version
                        )
                    })?,
                    Some(tool) => installation.tool_path(tool.into()),
                };
                writeln!(out, "{}", path.display())?;
            }
            Self::Run {
                release,
                tool,
                args,
            } => {
                let installation = manager.install(release.selector())?;
                let mut command = match tool {
                    CliTool::Ast => installation.ast().with_context(|| {
                        format!(
                            "release {} does not ship luau-ast",
                            installation.release().version
                        )
                    })?,
                    tool => installation.command(tool.into()),
                };
                let status = command.args(args).status()?;
                let code = status.code().and_then(|code| u8::try_from(code).ok());
                return Ok(ExitCode::from(code.unwrap_or(1)));
            }
            Self::Prune => {
                for path in manager.prune()? {
                    writeln!(out, "removed {}", path.display())?;
                }
            }
        }

        Ok(ExitCode::SUCCESS)
    }
}
