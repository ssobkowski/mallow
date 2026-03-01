mod ast;
mod disasm;
mod hil;
mod il;
mod logging;
mod passes;
mod printer;
mod scopes;
mod structurer;

use std::path::PathBuf;

use clap::{Parser, Subcommand};

use crate::{
    il::{Constant, Instr},
    printer::print,
};

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
                    let content = format_disassembly_plaintext(&d);
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
            if logging::verbose_enabled() {
                eprintln!(
                    "[decompile] protos={}, entry={}",
                    disassembled.protos.len(),
                    disassembled.entry_proto
                );
                for proto in &disassembled.protos {
                    eprintln!(
                        "[decompile] proto {}: instrs={}, consts={}, child_protos={}, params={}, upvals={}, vararg={}",
                        proto.index,
                        proto.instrs.len(),
                        proto.consts.len(),
                        proto.protos.len(),
                        proto.num_params,
                        proto.num_upvals,
                        proto.is_vararg
                    );
                }
            }

            let proto_cfgs = disassembled
                .protos
                .iter()
                .map(|proto| hil::build_cfg_for_proto(proto, &disassembled.protos))
                .collect::<Vec<_>>();
            let ast = structurer::structure(
                &proto_cfgs,
                disassembled.entry_proto as usize,
                &disassembled.protos,
            );

            // let ast = passes::run_all(ast); CURRENTLY BROKEN; DO NOT UNCOMMENT
            let src = print(&ast);

            if let Err(e) = write_output(output, &src) {
                eprintln!("Error writing decompiled output: {e}");
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

fn format_disassembly_plaintext(disassembly: &disasm::Disassembly) -> String {
    let mut out = String::new();

    for proto in &disassembly.protos {
        if !out.is_empty() {
            out.push('\n');
        }

        out.push_str(&format!(
            "-- proto {}{}\n",
            proto.index,
            if proto.index == disassembly.entry_proto {
                " (entry)"
            } else {
                ""
            }
        ));

        for instr in &proto.instrs {
            out.push_str("0: ");
            out.push_str(&format_instruction(instr, &proto.consts));
            out.push('\n');
        }
    }

    out
}

fn format_instruction(instr: &Instr, consts: &[Constant]) -> String {
    match instr {
        Instr::Nop => "NOP".to_string(),
        Instr::Break => "BREAK".to_string(),
        Instr::LoadNil { reg } => format!("LOADNIL R{reg}"),
        Instr::LoadB { reg, value, jump } => {
            format!("LOADB R{reg} {} {jump}", if *value { 1 } else { 0 })
        }
        Instr::LoadN { reg, value } => format!("LOADN R{reg} {value}"),
        Instr::LoadK { reg, index } => format!("LOADK R{reg} {}", fmt_k(*index as usize, consts)),
        Instr::Move { dest, src } => format!("MOVE R{dest} R{src}"),
        Instr::GetGlobal { dest, key, .. } => {
            format!("GETGLOBAL R{dest} {}", fmt_k(*key as usize, consts))
        }
        Instr::SetGlobal { src, key, .. } => {
            format!("SETGLOBAL R{src} {}", fmt_k(*key as usize, consts))
        }
        Instr::GetUpval { dest, upval } => format!("GETUPVAL R{dest} U{upval}"),
        Instr::SetUpval { src, upval } => format!("SETUPVAL R{src} U{upval}"),
        Instr::CloseUpvals { reg } => format!("CLOSEUPVALS R{reg}"),
        Instr::GetImport { dest, index, path } => format!("GETIMPORT R{dest} K{index} {path}"),
        Instr::GetTable { dest, table, key } => format!("GETTABLE R{dest} R{table} R{key}"),
        Instr::SetTable { src, table, key } => format!("SETTABLE R{src} R{table} R{key}"),
        Instr::GetTableKS {
            dest, table, key, ..
        } => format!(
            "GETTABLEKS R{dest} R{table} {}",
            fmt_k(*key as usize, consts)
        ),
        Instr::SetTableKS {
            src, table, key, ..
        } => {
            format!(
                "SETTABLEKS R{src} R{table} {}",
                fmt_k(*key as usize, consts)
            )
        }
        Instr::GetTableN { dest, table, index } => format!("GETTABLEN R{dest} R{table} {index}"),
        Instr::SetTableN { src, table, index } => format!("SETTABLEN R{src} R{table} {index}"),
        Instr::NewClosure { dest, proto } => format!("NEWCLOSURE R{dest} P{proto}"),
        Instr::NameCall {
            dest,
            object,
            method,
            ..
        } => format!(
            "NAMECALL R{dest} R{object} {}",
            fmt_k(*method as usize, consts)
        ),
        Instr::Call {
            func,
            arg_count,
            ret_count,
        } => format!(
            "CALL R{func} {} {}",
            luau_count(*arg_count),
            luau_count(*ret_count)
        ),
        Instr::Return { base, count } => format!("RETURN R{base} {}", luau_count(*count)),
        Instr::Jump { offset } => format!("JUMP {offset}"),
        Instr::JumpBack { offset } => format!("JUMPBACK {offset}"),
        Instr::JumpIf { reg, offset } => format!("JUMPIF R{reg} {offset}"),
        Instr::JumpIfNot { reg, offset } => format!("JUMPIFNOT R{reg} {offset}"),
        Instr::JumpIfEq { reg, aux, offset } => format!("JUMPIFEQ R{reg} R{aux} {offset}"),
        Instr::JumpIfLe { reg, aux, offset } => format!("JUMPIFLE R{reg} R{aux} {offset}"),
        Instr::JumpIfLt { reg, aux, offset } => format!("JUMPIFLT R{reg} R{aux} {offset}"),
        Instr::JumpIfNotEq { reg, aux, offset } => format!("JUMPIFNOTEQ R{reg} R{aux} {offset}"),
        Instr::JumpIfNotLe { reg, aux, offset } => format!("JUMPIFNOTLE R{reg} R{aux} {offset}"),
        Instr::JumpIfNotLt { reg, aux, offset } => format!("JUMPIFNOTLT R{reg} R{aux} {offset}"),
        Instr::Add { dest, a, b } => format!("ADD R{dest} R{a} R{b}"),
        Instr::Sub { dest, a, b } => format!("SUB R{dest} R{a} R{b}"),
        Instr::Mul { dest, a, b } => format!("MUL R{dest} R{a} R{b}"),
        Instr::Div { dest, a, b } => format!("DIV R{dest} R{a} R{b}"),
        Instr::Mod { dest, a, b } => format!("MOD R{dest} R{a} R{b}"),
        Instr::Pow { dest, a, b } => format!("POW R{dest} R{a} R{b}"),
        Instr::AddK { dest, reg, k } => {
            format!("ADDK R{dest} R{reg} {}", fmt_k(*k as usize, consts))
        }
        Instr::SubK { dest, reg, k } => {
            format!("SUBK R{dest} R{reg} {}", fmt_k(*k as usize, consts))
        }
        Instr::MulK { dest, reg, k } => {
            format!("MULK R{dest} R{reg} {}", fmt_k(*k as usize, consts))
        }
        Instr::DivK { dest, reg, k } => {
            format!("DIVK R{dest} R{reg} {}", fmt_k(*k as usize, consts))
        }
        Instr::ModK { dest, reg, k } => {
            format!("MODK R{dest} R{reg} {}", fmt_k(*k as usize, consts))
        }
        Instr::PowK { dest, reg, k } => {
            format!("POWK R{dest} R{reg} {}", fmt_k(*k as usize, consts))
        }
        Instr::And { dest, a, b } => format!("AND R{dest} R{a} R{b}"),
        Instr::Or { dest, a, b } => format!("OR R{dest} R{a} R{b}"),
        Instr::AndK { dest, reg, k } => {
            format!("ANDK R{dest} R{reg} {}", fmt_k(*k as usize, consts))
        }
        Instr::OrK { dest, reg, k } => format!("ORK R{dest} R{reg} {}", fmt_k(*k as usize, consts)),
        Instr::Concat { dest, a, b } => format!("CONCAT R{dest} R{a} R{b}"),
        Instr::Not { dest, reg } => format!("NOT R{dest} R{reg}"),
        Instr::Minus { dest, reg } => format!("MINUS R{dest} R{reg}"),
        Instr::Length { dest, reg } => format!("LENGTH R{dest} R{reg}"),
        Instr::NewTable {
            dest,
            hash_size,
            array_size,
        } => format!("NEWTABLE R{dest} {hash_size} {array_size}"),
        Instr::DupTable { dest, k } => format!("DUPTABLE R{dest} {}", fmt_k(*k as usize, consts)),
        Instr::SetList {
            table,
            base,
            count,
            index,
        } => format!("SETLIST R{table} R{base} {count} {index}"),
        Instr::FornPrep { base, offset } => format!("FORNPREP R{base} {offset}"),
        Instr::FornLoop { base, offset } => format!("FORNLOOP R{base} {offset}"),
        Instr::ForgLoop {
            base,
            offset,
            var_count,
            ipairs,
        } => format!(
            "FORGLOOP R{base} {offset} {var_count} {}",
            if *ipairs { 1 } else { 0 }
        ),
        Instr::ForgPrepInext { base, offset } => format!("FORGPREP_INEXT R{base} {offset}"),
        Instr::FastCall3 {
            builtin,
            arg1,
            arg2,
            arg3,
            jump,
        } => format!("FASTCALL3 {builtin} R{arg1} R{arg2} R{arg3} {jump}"),
        Instr::ForgPrepNext { base, offset } => format!("FORGPREP_NEXT R{base} {offset}"),
        Instr::NativeCall => "NATIVECALL".to_string(),
        Instr::GetVarArgs { dest, count } => format!("GETVARARGS R{dest} {count}"),
        Instr::DupClosure { dest, k } => {
            format!("DUPCLOSURE R{dest} {}", fmt_k(*k as usize, consts))
        }
        Instr::PrepVarArgs { nparams } => format!("PREPVARARGS {nparams}"),
        Instr::LoadKX { dest, k } => format!("LOADKX R{dest} {}", fmt_k(*k as usize, consts)),
        Instr::JumpX { offset } => format!("JUMPX {offset}"),
        Instr::FastCall { builtin, jump } => format!("FASTCALL {builtin} {jump}"),
        Instr::Coverage => "COVERAGE".to_string(),
        Instr::Capture { capture_type, reg } => {
            format!("CAPTURE {} R{reg}", capture_type_name(*capture_type))
        }
        Instr::SubRK { dest, k, reg } => {
            format!("SUBRK R{dest} {} R{reg}", fmt_k(*k as usize, consts))
        }
        Instr::DivRK { dest, k, reg } => {
            format!("DIVRK R{dest} {} R{reg}", fmt_k(*k as usize, consts))
        }
        Instr::FastCall1 { builtin, arg, jump } => format!("FASTCALL1 {builtin} R{arg} {jump}"),
        Instr::FastCall2 {
            builtin,
            arg1,
            arg2,
            jump,
        } => format!("FASTCALL2 {builtin} R{arg1} R{arg2} {jump}"),
        Instr::FastCall2K {
            builtin,
            arg,
            k,
            jump,
        } => format!(
            "FASTCALL2K {builtin} R{arg} {} {jump}",
            fmt_k(*k as usize, consts)
        ),
        Instr::ForgPrep { base, offset } => format!("FORGPREP R{base} {offset}"),
        Instr::JumpXEqKNil {
            reg,
            invert,
            offset,
        } => format!(
            "JUMPXEQKNIL R{reg} {} {offset}",
            if *invert { 1 } else { 0 }
        ),
        Instr::JumpXEqKB {
            reg,
            k,
            invert,
            offset,
        } => format!(
            "JUMPXEQKB R{reg} {} {} {offset}",
            if *k { 1 } else { 0 },
            if *invert { 1 } else { 0 }
        ),
        Instr::JumpXEqKN {
            reg,
            k,
            invert,
            offset,
        } => format!(
            "JUMPXEQKN R{reg} {} {} {offset}",
            fmt_k(*k as usize, consts),
            if *invert { 1 } else { 0 }
        ),
        Instr::JumpXEqKS {
            reg,
            k,
            invert,
            offset,
        } => format!(
            "JUMPXEQKS R{reg} {} {} {offset}",
            fmt_k(*k as usize, consts),
            if *invert { 1 } else { 0 }
        ),
        Instr::IDiv { dest, a, b } => format!("IDIV R{dest} R{a} R{b}"),
        Instr::IDivK { dest, reg, k } => {
            format!("IDIVK R{dest} R{reg} {}", fmt_k(*k as usize, consts))
        }
    }
}

fn fmt_k(index: usize, consts: &[Constant]) -> String {
    let mut out = format!("K{index}");
    if let Some(Constant::String(s)) = consts.get(index) {
        out.push_str(" ['");
        out.push_str(&escape_single_quoted(s));
        out.push_str("']");
    }
    out
}

fn luau_count(raw: u8) -> i16 {
    if raw == 0 { -1 } else { raw as i16 - 1 }
}

fn capture_type_name(capture_type: u8) -> &'static str {
    match capture_type {
        0 => "VAL",
        1 => "REF",
        2 => "UPVAL",
        _ => "UNKNOWN",
    }
}

fn escape_single_quoted(input: &str) -> String {
    input
        .replace('\\', "\\\\")
        .replace('\'', "\\'")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}
