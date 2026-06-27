use std::{path::PathBuf, process::Command};

use anyhow::{Result, ensure};
use clap::{Parser, Subcommand};
use mallow::{
    DecompileOptions, DiagnosticConfig, Diagnostics, LogLevel, LogTarget, ProtoSelector,
    decompile_bytecode_with_diagnostics, disassemble_bytecode_with_diagnostics,
};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    #[arg(short, long, global = true)]
    verbose: bool,

    /// Diagnostic verbosity. Use with --log-target and --log-proto for large files.
    #[arg(long, global = true, value_enum)]
    log_level: Option<LogLevel>,

    /// Diagnostic target to enable. Repeatable. Defaults to all targets at the selected level.
    #[arg(long, global = true, value_enum, value_delimiter = ',')]
    log_target: Vec<LogTarget>,

    /// Proto diagnostic filter. Accepts a proto index or 'entry'. Repeatable.
    #[arg(long, global = true, value_delimiter = ',')]
    log_proto: Vec<ProtoSelector>,

    /// Write a Chrome trace profile to this path.
    #[cfg(feature = "profile")]
    #[arg(long, global = true, value_name = "PATH")]
    profile_output: Option<PathBuf>,
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Disassemble a bytecode file
    Disasm {
        /// Path to the input bytecode file
        #[arg(short, long)]
        input: PathBuf,

        /// Output file path. Prints to stdout if omitted
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Decompile a bytecode file to Luau source code
    Decompile {
        /// Path to the input bytecode file
        #[arg(short, long)]
        input: PathBuf,

        /// Output file path. Prints to stdout if omitted
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Spill emitter-introduced locals into table storage when Luau's local limit is exceeded
        #[arg(long)]
        spill_locals: bool,

        /// Emit conservative decompiler-inferred type annotations
        #[arg(long)]
        infer_types: bool,
    },
    /// Compile a Luau source file and decompile the resulting bytecode
    Roundtrip {
        /// Path to the input Luau source file
        #[arg(short, long)]
        input: PathBuf,

        /// Output file path. Prints to stdout if omitted
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Optimization level, passed as '-O<n>' to the Luau compiler.
        #[arg(long, value_parser = clap::value_parser!(u8).range(0..=2))]
        opt_level: Option<u8>,

        /// Debug info level, passed as '-g<n>' to the Luau compiler.
        #[arg(long, value_parser = clap::value_parser!(u8).range(0..=2))]
        debug_level: Option<u8>,

        /// Type info level, passed as '-t<n>' to the Luau compiler.
        #[arg(long, value_parser = clap::value_parser!(u8).range(0..=1))]
        type_level: Option<u8>,

        /// Spill emitter-introduced locals into table storage when Luau's local limit is exceeded
        #[arg(long)]
        spill_locals: bool,

        /// Emit conservative decompiler-inferred type annotations
        #[arg(long)]
        infer_types: bool,
    },
    /// Generate a control flow graph visualization for a bytecode file
    #[cfg(feature = "visualize")]
    Visualize {
        /// Path to the input bytecode file
        #[arg(short, long)]
        input: PathBuf,

        /// Output file path
        #[arg(short, long)]
        output: PathBuf,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let diagnostic_config = diagnostic_config(&cli);
    let _tracing_guard = init_tracing(&cli, diagnostic_config.is_enabled());
    let diagnostics = Diagnostics::new(diagnostic_config);

    match cli.command {
        Commands::Disasm { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            let chunk = disassemble_bytecode_with_diagnostics(&bytecode, &diagnostics)?;
            let mut out = get_output(output)?;
            chunk.dump(&mut out)?;
            Ok(())
        }
        Commands::Decompile {
            input,
            output,
            spill_locals,
            infer_types,
        } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            diagnostics
                .at(LogLevel::Info, LogTarget::Driver)
                .line(0, format_args!("decompiling..."));
            let code = decompile_bytecode_with_diagnostics(
                &bytecode,
                DecompileOptions {
                    spill_locals,
                    infer_types,
                },
                &diagnostics,
            )?;

            let mut out = get_output(output)?;
            out.write_all(code.as_bytes())?;
            Ok(())
        }
        Commands::Roundtrip {
            input,
            output,
            opt_level,
            debug_level,
            type_level,
            spill_locals,
            infer_types,
        } => {
            let mut cmd = Command::new("luau-compile");
            cmd.arg("--binary");
            cmd.arg(input);
            if let Some(opt_level) = opt_level {
                cmd.arg(format!("-O{}", opt_level));
            }
            if let Some(debug_level) = debug_level {
                cmd.arg(format!("-g{}", debug_level));
            }
            if let Some(type_level) = type_level {
                cmd.arg(format!("-t{}", type_level));
            }

            let compile_out = cmd.output()?;

            ensure!(
                compile_out.status.success(),
                "failed to compile:\n{}",
                String::from_utf8_lossy(&compile_out.stderr).trim()
            );

            let code = decompile_bytecode_with_diagnostics(
                &compile_out.stdout,
                DecompileOptions {
                    spill_locals,
                    infer_types,
                },
                &diagnostics,
            )?;

            let mut out = get_output(output)?;
            out.write_all(code.as_bytes())?;
            Ok(())
        }
        #[cfg(feature = "visualize")]
        Commands::Visualize { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");
            mallow::visualize_bytecode(&bytecode, output, &diagnostics)
        }
    }
}

#[cfg(not(feature = "profile"))]
fn init_tracing(cli: &Cli, diagnostics_enabled: bool) -> mallow::TracingGuard {
    let _ = cli;
    mallow::init_tracing(diagnostics_enabled).unwrap_or_else(|e| {
        eprintln!("failed to initialize tracing: {e}");
        std::process::exit(1);
    })
}

#[cfg(feature = "profile")]
fn init_tracing(cli: &Cli, diagnostics_enabled: bool) -> mallow::TracingGuard {
    mallow::init_tracing(diagnostics_enabled, cli.profile_output.clone()).unwrap_or_else(|e| {
        eprintln!("failed to initialize tracing: {e}");
        std::process::exit(1);
    })
}

fn diagnostic_config(cli: &Cli) -> DiagnosticConfig {
    let level = cli
        .log_level
        .or_else(|| cli.verbose.then_some(LogLevel::Info));

    DiagnosticConfig::new(level, cli.log_target.iter().copied(), cli.log_proto.clone())
}

fn get_output(path: Option<PathBuf>) -> std::io::Result<Box<dyn std::io::Write>> {
    match path {
        Some(path) => Ok(Box::new(std::fs::File::create(path)?)),
        None => Ok(Box::new(std::io::stdout())),
    }
}
