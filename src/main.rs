mod ast;
mod common;
mod disasm;
mod hil;
mod il;
mod printer;
mod scopes;
mod structurer;

use std::{path::PathBuf, process::Command};

use clap::{Parser, Subcommand};

use crate::{disasm::DisasmError, hil::StructuredFunction};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
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
    },
    /// Compile a Luau source file and decompile the resulting bytecode
    Roundtrip {
        /// Path to the input Luau source file
        #[arg(short, long)]
        input: PathBuf,

        /// Output file path. Prints to stdout if omitted
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
}

fn decompile_bytecode(bytecode: &[u8]) -> Result<String, DisasmError> {
    let diasssembled = disasm::disassemble(bytecode)?;

    let fns: Vec<_> = diasssembled
        .protos
        .iter()
        .map(|proto| StructuredFunction::from_proto(proto, &diasssembled.protos))
        .collect();

    let ast = structurer::structure(fns, diasssembled.entry_proto as usize);
    Ok(printer::print(&ast))
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Disasm { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            match disasm::disassemble(&bytecode) {
                Ok(d) => {
                    let content = format!("{:#?}", &d);
                    if let Err(e) = write_output(output, &content) {
                        eprintln!("Error writing disassembly output: {e}");
                    }
                }
                Err(e) => eprintln!("Error during disassembly: {}", e),
            }
        }
        Commands::Decompile { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");
            let code = match decompile_bytecode(&bytecode) {
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
        Commands::Roundtrip { input, output } => {
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

            let code = match decompile_bytecode(&compile_out.stdout) {
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
