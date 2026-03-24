mod ast;
mod common;
mod disasm;
mod hil;
mod il;
mod logging;
// mod passes;
mod printer;
mod scopes;
// mod structurer;

use std::path::PathBuf;

use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Enable verbose logging
    #[arg(short, long, global = true)]
    verbose: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Disassemble a bytecode file
    Disasm {
        /// Path to the bytecode file
        #[arg(short, long)]
        input: PathBuf,

        /// Path to the output file (optional)
        /// If not provided, output will be printed to stdout
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Decompile a bytecode file to a readable luau source code
    Decompile {
        /// Path to the bytecode file
        #[arg(short, long)]
        input: PathBuf,

        /// Path to the output file (optional)
        /// If not provided, output will be printed to stdout
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
}

fn main() {
    let cli = Cli::parse();
    logging::set_verbose(cli.verbose);

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

            let disassembled = match disasm::disassemble(&bytecode) {
                Ok(d) => d,
                Err(e) => {
                    eprintln!("Error during disassembly: {}", e);
                    return;
                }
            };

            let cfgs: Vec<_> = disassembled
                .protos
                .iter()
                .map(|proto| {
                    let cfg = hil::cflow::graph::ControlFlowGraph::from_proto(
                        proto,
                        &disassembled.protos,
                    );
                    // let mut region = hil::cflow::region::RegionBuilder::new(&cfg);
                    // (region.build_region(cfg.entry_block, None), cfg)
                    cfg
                })
                .collect();

            for (i, cfg) in cfgs.iter().enumerate() {
                println!("[{}]: {:#?}", i, cfg);
            }

            // let ast = structurer::structure(
            //     &regions,
            //     &cfgs,
            //     disassembled.entry_proto as usize,
            //     &disassembled.protos,
            // );
            // let code = printer::print(&ast);

            // if let Err(e) = write_output(output, &code) {
            //     eprintln!("Error writing decompilation output: {e}");
            // }
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
