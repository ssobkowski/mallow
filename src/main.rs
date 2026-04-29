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
    logging::verbose,
};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    #[arg(short, long, global = true)]
    verbose: bool,
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

fn disassemble_bytecode(bytecode: &[u8]) -> Result<Disassembly, DisasmError> {
    verbose!("disassembling...");
    let d = disasm::disassemble(bytecode)?;

    verbose!(indent: 1, "LBC Version: {}", d.version);
    verbose!(indent: 1, "Proto count: {}", d.protos.len());
    verbose!(indent: 1, "Entry: {}", d.entry_proto);

    Ok(d)
}

fn decompile_bytecode(bytecode: &[u8], options: EmitterOptions) -> Result<String, DisasmError> {
    let diasssembled = disassemble_bytecode(bytecode)?;

    let mut fns: Vec<_> = diasssembled
        .protos
        .iter()
        .map(|proto| StructuredFunction::from_proto(proto, &diasssembled.protos))
        .collect();
    let error = fns.iter().any(|f| !f.was_reduced);

    verbose!("running passes...");
    hil::passes::run(&mut fns);

    let ast = emitter::emit_ast(fns, diasssembled.entry_proto as usize, options);

    let mut comments = vec![format!(
        "Decompiled by mallow {}",
        env!("CARGO_PKG_VERSION")
    )];
    if error {
        comments.push("Failed to structure all functions - output may be incomplete".to_string());
    }

    Ok(printer::print(&ast, &comments))
}

fn main() {
    let cli = Cli::parse();
    logging::set_verbose(cli.verbose);

    match cli.command {
        Commands::Disasm { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            match disassemble_bytecode(&bytecode) {
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

            verbose!("decompiling...");
            let code = match decompile_bytecode(&bytecode, EmitterOptions { spill_locals }) {
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

            let code =
                match decompile_bytecode(&compile_out.stdout, EmitterOptions { spill_locals }) {
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
            use crate::hil::cflow::{graph::ControlFlowGraph, visualize::dump_cfgs};

            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");
            let disasm = disassemble_bytecode(&bytecode).expect("failed to disassemble");

            let cfgs: Vec<_> = disasm
                .protos
                .iter()
                .map(|proto| ControlFlowGraph::from_proto(proto, &disasm.protos))
                .collect();

            dump_cfgs(&cfgs, disasm.entry_proto as usize, output);
        }
    }
}

fn write_output(output: Option<PathBuf>, content: &str) -> std::io::Result<()> {
    if let Some(path) = output {
        std::fs::write(path, content)
    } else {
        println!("{content}");
        Ok(())
    }
}
