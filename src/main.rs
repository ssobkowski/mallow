mod ast;
mod common;
mod disasm;
mod emitter;
mod hil;
mod il;
mod logging;
mod printer;
mod scopes;

use std::{path::PathBuf, process::Command};

use clap::{Parser, Subcommand};

use crate::{
    disasm::{DisasmError, Disassembly},
    emitter::options::EmitterOptions,
    hil::StructuredFunction,
    logging::{DiagnosticConfig, Diagnostics, LogLevel, LogTarget, ProtoSelector},
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

fn disassemble_bytecode(
    bytecode: &[u8],
    diagnostics: &Diagnostics,
) -> Result<Disassembly, DisasmError> {
    let info = diagnostics.at(LogLevel::Info, LogTarget::Driver);
    info.line(0, format_args!("disassembling..."));

    let d = disasm::disassemble(bytecode)?;

    info.line(1, format_args!("LBC Version: {}", d.version));
    info.line(1, format_args!("Proto count: {}", d.protos.len()));
    info.line(1, format_args!("Entry: {}", d.entry_proto));

    Ok(d)
}

fn decompile_bytecode(
    bytecode: &[u8],
    options: EmitterOptions,
    diagnostics: &Diagnostics,
) -> Result<String, DisasmError> {
    let disasssembled = disassemble_bytecode(bytecode, diagnostics)?;
    let diagnostics = diagnostics.with_entry_proto(disasssembled.entry_proto as usize);

    let mut fns: Vec<_> = disasssembled
        .protos
        .iter()
        .map(|proto| StructuredFunction::from_proto(proto, &disasssembled.protos, &diagnostics))
        .collect();

    diagnostics
        .at(LogLevel::Info, LogTarget::Driver)
        .line(0, format_args!("running passes..."));
    hil::passes::run(&mut fns);

    diagnostics
        .at(LogLevel::Info, LogTarget::Driver)
        .line(0, format_args!("emitting AST..."));
    let ast = emitter::emit_ast(fns, disasssembled.entry_proto as usize, options);

    let comments = vec![format!(
        "Decompiled by mallow {}",
        env!("CARGO_PKG_VERSION")
    )];

    diagnostics
        .at(LogLevel::Info, LogTarget::Driver)
        .line(0, format_args!("done"));
    Ok(printer::print(&ast, &comments))
}

fn main() {
    let cli = Cli::parse();
    let diagnostics = Diagnostics::new(diagnostic_config(&cli));

    match cli.command {
        Commands::Disasm { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            match disassemble_bytecode(&bytecode, &diagnostics) {
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
            let code = match decompile_bytecode(
                &bytecode,
                EmitterOptions { spill_locals },
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

            let code = match decompile_bytecode(
                &compile_out.stdout,
                EmitterOptions { spill_locals },
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
            use crate::hil::cflow::{cfg::ControlFlowGraph, visualize::dump_cfgs};

            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");
            let disasm =
                disassemble_bytecode(&bytecode, &diagnostics).expect("failed to disassemble");

            let cfgs: Vec<_> = disasm
                .protos
                .iter()
                .map(|proto| ControlFlowGraph::from_proto(proto, &disasm.protos))
                .collect();

            dump_cfgs(&cfgs, disasm.entry_proto as usize, output);
        }
    }
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
