use std::{path::PathBuf, process::Command};

use clap::{Parser, Subcommand};
use mallow::{
    DiagnosticConfig, Diagnostics, LogLevel, LogTarget, ProtoSelector,
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
    },
    /// Compile a Luau source file and decompile the resulting bytecode
    Roundtrip {
        /// Path to the input Luau source file
        #[arg(short, long)]
        input: PathBuf,

        /// Output file path. Prints to stdout if omitted
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Spill emitter-introduced locals into table storage when Luau's local limit is exceeded
        #[arg(long)]
        spill_locals: bool,
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

fn main() {
    let cli = Cli::parse();
    let diagnostic_config = diagnostic_config(&cli);
    let _tracing_guard = init_tracing(&cli, diagnostic_config.is_enabled());
    let diagnostics = Diagnostics::new(diagnostic_config);

    match cli.command {
        Commands::Disasm { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            match disassemble_bytecode_with_diagnostics(&bytecode, &diagnostics) {
                Ok(d) => {
                    let content = d.to_string();
                    if let Err(e) = write_output(output, &content) {
                        eprintln!("Error writing disassembly output: {e}");
                    }
                }
                Err(e) => eprintln!("Error during disassembly: {}", e),
            }
        }
        Commands::Decompile {
            input,
            output,
            spill_locals,
        } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            diagnostics
                .at(LogLevel::Info, LogTarget::Driver)
                .line(0, format_args!("decompiling..."));
            let code =
                match decompile_bytecode_with_diagnostics(&bytecode, spill_locals, &diagnostics) {
                    Ok(c) => c,
                    Err(e) => {
                        eprintln!("Error during decompilation: {}", e);
                        return;
                    }
                };

            if let Err(e) = write_output(output, &code) {
                eprintln!("Error writing decompilation output: {e}");
            }
        }
        Commands::Roundtrip {
            input,
            output,
            spill_locals,
        } => {
            let compile_out = match Command::new("luau-compile")
                .arg("--binary")
                .arg(input)
                .output()
            {
                Ok(o) => o,
                Err(e) => {
                    eprintln!("failed to spawn luau-compile: {e}");
                    return;
                }
            };

            if !compile_out.status.success() {
                eprintln!("failed to compile: {:?}", &output);
                return;
            }

            let code = match decompile_bytecode_with_diagnostics(
                &compile_out.stdout,
                spill_locals,
                &diagnostics,
            ) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("Error during decompilation: {}", e);
                    return;
                }
            };

            if let Err(e) = write_output(output, &code) {
                eprintln!("Error writing decompilation output: {e}");
            }
        }
        #[cfg(feature = "visualize")]
        Commands::Visualize { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");
            if let Err(e) = mallow::visualize_bytecode(&bytecode, output, &diagnostics) {
                eprintln!("Error during visualization: {e}");
            }
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

fn write_output(output: Option<PathBuf>, content: &str) -> std::io::Result<()> {
    if let Some(path) = output {
        std::fs::write(path, content)
    } else {
        println!("{content}");
        Ok(())
    }
}
