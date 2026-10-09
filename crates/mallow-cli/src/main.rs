mod diagnostics;
mod input;
mod render;

#[cfg(feature = "luau-toolchain")]
mod toolchain;

#[cfg(feature = "ai")]
mod ai;

use std::io::Write;
use std::process::ExitCode;

use anyhow::Result;
use clap::{Parser, Subcommand, ValueEnum};
#[cfg(feature = "ai")]
use mallow_core::decompile_source;
use mallow_core::{
    DEFAULT_MAX_PASS_ITERATIONS, DecompileOptions, Diagnostics, EmitMode, LogLevel, LogTarget,
    ProtoSelector, decompile_bytecode_into, disassemble_bytecode_with_diagnostics,
};

use crate::diagnostics::{CliLogLevel, CliLogTarget};
use crate::input::InputArgs;
use crate::render::{ColorChoice, StdoutPainter};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    #[arg(short, long, global = true)]
    verbose: bool,

    /// When to color output.
    #[arg(
        long,
        global = true,
        value_enum,
        value_name = "WHEN",
        default_value = "auto"
    )]
    color: ColorChoice,

    /// Diagnostic verbosity. Use with --log-target and --log-proto for large files.
    #[arg(long, global = true, value_enum)]
    log_level: Option<CliLogLevel>,

    /// Diagnostic target to enable. Repeatable. Defaults to all targets at the selected level.
    #[arg(long, global = true, value_enum, value_delimiter = ',')]
    log_target: Vec<CliLogTarget>,

    /// Proto diagnostic filter. Accepts a proto index or 'entry'. Repeatable.
    #[arg(long, global = true, value_delimiter = ',')]
    log_proto: Vec<ProtoSelector>,

    /// Write a Chrome trace profile to this path.
    #[cfg(feature = "profile")]
    #[arg(long, global = true, value_name = "PATH")]
    profile_output: Option<std::path::PathBuf>,
}

/// Output form selected by the command line.
#[derive(Debug, Clone, Copy, ValueEnum)]
enum Emit {
    /// Emit cleaned Luau source code.
    Source,
    /// Emit flat intermediate representation.
    Ir,
    /// Emit nested intermediate representation debug text.
    Nir,
}

impl Emit {
    /// Returns the matching library output mode.
    const fn mode(self) -> EmitMode {
        match self {
            Self::Source => EmitMode::Source,
            Self::Ir => EmitMode::Ir,
            Self::Nir => EmitMode::Nir,
        }
    }
}

/// Decompiler settings shared by commands that emit decompiled output.
#[derive(Debug, clap::Args)]
struct DecompileArgs {
    /// Output form to emit
    #[arg(long, value_enum, default_value = "source")]
    emit: Emit,

    /// Spill emitter-introduced locals into table storage when Luau's local limit is exceeded
    #[arg(long)]
    spill_locals: bool,

    /// Maximum number of cleanup pass iterations per function
    #[arg(
        long,
        default_value_t = DEFAULT_MAX_PASS_ITERATIONS,
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..)
    )]
    max_pass_iterations: usize,

    /// Ask an LLM through OpenRouter to rename decompiled locals. Reads the API key from OPENROUTER_API_KEY
    #[cfg(feature = "ai")]
    #[arg(
        long,
        value_name = "MODEL",
        num_args = 0..=1,
        default_missing_value = ai::DEFAULT_MODEL
    )]
    ai_rename: Option<String>,

    /// How much the --ai-rename model may reason before answering
    #[cfg(feature = "ai")]
    #[arg(
        long,
        value_enum,
        value_name = "EFFORT",
        default_value = "medium",
        requires = "ai_rename"
    )]
    ai_reasoning: ai::Reasoning,
}

impl DecompileArgs {
    /// Returns the matching library decompiler settings.
    const fn options(&self) -> DecompileOptions {
        DecompileOptions {
            emit: self.emit.mode(),
            spill_locals: self.spill_locals,
            max_pass_iterations: self.max_pass_iterations,
        }
    }
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Disassemble bytecode
    Disasm {
        /// Input to disassemble.
        #[command(flatten)]
        input: InputArgs,
    },
    /// Decompile bytecode into the selected output form
    Decompile {
        /// Input to decompile.
        #[command(flatten)]
        input: InputArgs,

        /// Settings for decompiled output.
        #[command(flatten)]
        decompile: DecompileArgs,
    },
    /// Generate a control flow graph visualization
    #[cfg(feature = "visualize")]
    Visualize {
        /// Input to visualize.
        #[command(flatten)]
        input: InputArgs,
    },
    /// Manage the Luau releases used for compilation and testing
    #[cfg(feature = "luau-toolchain")]
    Toolchain {
        #[command(subcommand)]
        command: toolchain::ToolchainCommand,
    },
}

fn main() -> Result<ExitCode> {
    let cli = Cli::parse();
    let diagnostic_config = diagnostics::diagnostic_config(&cli);
    let _tracing_guard = diagnostics::init_tracing(&cli);
    let diagnostics = Diagnostics::new(diagnostic_config);
    cli.color.apply();

    match cli.command {
        Commands::Disasm { input } => {
            let bytecode = input.bytecode()?;

            let chunk = disassemble_bytecode_with_diagnostics(&bytecode, &diagnostics)?;
            let mut out = StdoutPainter::default();
            chunk.write_listing(&mut out)?;
            std::io::stdout()
                .lock()
                .write_all(out.as_str().as_bytes())?;
        }
        Commands::Decompile { input, decompile } => {
            let bytecode = input.bytecode()?;

            diagnostics
                .at(LogLevel::Info, LogTarget::Driver)
                .line(0, format_args!("decompiling..."));
            #[cfg(feature = "ai")]
            if let Some(model) = &decompile.ai_rename {
                anyhow::ensure!(
                    matches!(decompile.emit, Emit::Source),
                    "--ai-rename requires --emit source"
                );
                let renamer = ai::AiRenamer::from_env(model, decompile.ai_reasoning)?;
                let mut source = decompile_source(&bytecode, decompile.options(), &diagnostics)?;
                match renamer.rename(&mut source) {
                    Ok(report) => renamer.report(&report, cli.verbose),
                    Err(error) => diagnostics::warning(
                        ai::LOG_TARGET,
                        format_args!("AI renaming failed: {error:#}"),
                    ),
                }
                std::io::stdout()
                    .lock()
                    .write_all(source.print().as_bytes())?;
                return Ok(ExitCode::SUCCESS);
            }
            let mut out = StdoutPainter::default();
            decompile_bytecode_into(&bytecode, decompile.options(), &diagnostics, &mut out)?;
            std::io::stdout()
                .lock()
                .write_all(out.as_str().as_bytes())?;
        }
        #[cfg(feature = "visualize")]
        Commands::Visualize { input } => {
            let bytecode = input.bytecode()?;
            let html = mallow_core::visualize_bytecode(&bytecode, &diagnostics)?;
            std::io::stdout().lock().write_all(html.as_bytes())?;
        }
        #[cfg(feature = "luau-toolchain")]
        Commands::Toolchain { command } => return command.run(),
    }

    Ok(ExitCode::SUCCESS)
}
