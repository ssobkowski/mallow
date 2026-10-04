mod ast;
mod bytecode_types;
mod collections;
mod common;
mod disasm;
mod emitter;
mod il;
mod ir;
mod logging;
mod operator;
mod printer;
pub mod style;

#[cfg(feature = "visualize")]
mod visualize;

use anyhow::{Result, ensure};
pub use logging::{
    DIAGNOSTIC_EVENT_TARGET, DiagnosticConfig, Diagnostics, LogLevel, LogTarget, ProtoSelector,
};

use crate::disasm::Chunk;
use crate::ir::{Unit, fir};
use crate::logging::{LogLevel as DiagnosticLevel, LogTarget as DiagnosticTarget};
use crate::style::StyledWrite;

/// Output form produced by bytecode decompilation.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum EmitMode {
    /// Emit cleaned Luau source code.
    #[default]
    Source,
    /// Emit flat intermediate representation without source structuring.
    Ir,
    /// Emit the nested intermediate representation as debug text.
    Nir,
}

/// Default maximum number of post-region pass iterations per function.
pub const DEFAULT_MAX_PASS_ITERATIONS: usize = 20;

/// Options controlling bytecode decompilation.
#[derive(Debug, Clone, Copy)]
pub struct DecompileOptions {
    /// Selects the output form.
    pub emit: EmitMode,
    /// Spill emitter-introduced locals into table storage when Luau's local limit
    /// is exceeded.
    pub spill_locals: bool,
    /// Maximum number of post-region pass iterations per function.
    pub max_pass_iterations: usize,
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            emit: EmitMode::default(),
            spill_locals: false,
            max_pass_iterations: DEFAULT_MAX_PASS_ITERATIONS,
        }
    }
}

/// Disassembles Luau bytecode without emitting diagnostics.
pub fn disassemble_bytecode(bytecode: &[u8]) -> Result<Chunk> {
    disassemble_bytecode_with_diagnostics(bytecode, &Diagnostics::default())
}

/// Disassembles Luau bytecode using the provided diagnostics configuration.
pub fn disassemble_bytecode_with_diagnostics(
    bytecode: &[u8],
    diagnostics: &Diagnostics,
) -> Result<Chunk> {
    let span = tracing::info_span!("disassemble", byte_len = bytecode.len());
    let _enter = span.enter();

    let info = diagnostics.at(DiagnosticLevel::Info, DiagnosticTarget::Driver);
    info.line(0, format_args!("disassembling..."));

    let chunk = disasm::disassemble(bytecode)?;

    info.line(1, format_args!("LBC Version: {}", chunk.version));
    info.line(1, format_args!("Type Version: {}", chunk.types_version));
    info.line(1, format_args!("Proto count: {}", chunk.protos.len()));
    info.line(1, format_args!("Entry: {}", chunk.entry_proto));
    info.line(1, format_args!("Type info:"));

    match &chunk.userdata_type_mappings {
        None => info.line(2, format_args!("userdata mappings: <none>")),
        Some(mappings) => {
            info.line(2, format_args!("userdata mappings:"));
            for mapping in mappings {
                info.line(3, format_args!("[{}] {:?}", mapping.index, mapping.name));
            }
        }
    }

    for proto in &chunk.protos {
        let type_info = &proto.type_info;
        if type_info.function.is_none()
            && type_info.upvalues.is_empty()
            && type_info.locals.is_empty()
        {
            info.line(2, format_args!("proto {}: <none>", proto.id));
            continue;
        }

        info.line(2, format_args!("proto {}:", proto.id));
        if let Some(function) = &type_info.function {
            let params = function
                .params
                .iter()
                .enumerate()
                .map(|(i, tag)| format!("R{i}: {}", chunk.type_name(*tag)))
                .collect::<Vec<_>>()
                .join(", ");
            info.line(
                3,
                format_args!("function params({}): {}", function.num_params, params),
            );
        }

        if !type_info.upvalues.is_empty() {
            info.line(3, format_args!("upvalues:"));
            for (index, tag) in type_info.upvalues.iter().enumerate() {
                info.line(4, format_args!("U{index}: {}", chunk.type_name(*tag)));
            }
        }

        if !type_info.locals.is_empty() {
            info.line(3, format_args!("locals/temporaries:"));
            for local in &type_info.locals {
                info.line(
                    4,
                    format_args!(
                        "R{}: {} from {} to {}",
                        local.register,
                        chunk.type_name(local.ty),
                        local.start_pc,
                        local.end_pc
                    ),
                );
            }
        }
    }

    Ok(chunk)
}

/// Lifts Luau bytecode into the FIR.
///
/// Returns one FIR unit containing every lifted function.
pub fn lift_bytecode(bytecode: &[u8]) -> Result<Unit<fir::Function>> {
    lift_bytecode_with_diagnostics(bytecode, &Diagnostics::default())
}

/// Lifts Luau bytecode into the FIR using an existing diagnostics context.
///
/// Returns one FIR unit containing every lifted function.
pub fn lift_bytecode_with_diagnostics(
    bytecode: &[u8],
    diagnostics: &Diagnostics,
) -> Result<Unit<fir::Function>> {
    let span = tracing::info_span!("lift_bytecode", byte_len = bytecode.len());
    let _enter = span.enter();
    let chunk = disassemble_bytecode_with_diagnostics(bytecode, diagnostics)?;
    ir::fir::lift(chunk)
}

/// Emits Luau bytecode as cleaned source or intermediate representation text.
pub fn decompile_bytecode(bytecode: &[u8], options: DecompileOptions) -> Result<String> {
    decompile_bytecode_with_diagnostics(bytecode, options, &Diagnostics::default())
}

/// Emits Luau bytecode using an already constructed diagnostics context.
pub fn decompile_bytecode_with_diagnostics(
    bytecode: &[u8],
    options: DecompileOptions,
    diagnostics: &Diagnostics,
) -> Result<String> {
    let mut out = String::new();
    decompile_bytecode_into(bytecode, options, diagnostics, &mut out)?;
    Ok(out)
}

/// Emits Luau bytecode into a styled sink using an already constructed diagnostics context.
pub fn decompile_bytecode_into<W: StyledWrite>(
    bytecode: &[u8],
    options: DecompileOptions,
    diagnostics: &Diagnostics,
    out: &mut W,
) -> Result<()> {
    let span = tracing::info_span!(
        "decompile_bytecode",
        byte_len = bytecode.len(),
        spill_locals = options.spill_locals,
        max_pass_iterations = options.max_pass_iterations,
        emit = ?options.emit,
    );
    let _enter = span.enter();

    ensure!(
        options.max_pass_iterations > 0,
        "max pass iterations must be greater than zero"
    );
    let chunk = disassemble_bytecode_with_diagnostics(bytecode, diagnostics)?;
    let unit = ir::fir::lift(chunk)?;

    match options.emit {
        EmitMode::Source => {
            let types = bytecode_types::BytecodeTypes::read(&unit);
            let mut nested_unit = unit.map_functions(|function| {
                let diagnostics = diagnostics.for_proto(function.id.0);
                ir::nir::lift(function, &diagnostics)
            })?;

            ir::nir::passes::run(&mut nested_unit);
            for function in nested_unit.functions_mut() {
                ir::nir::materialize::destroy_ssa(function);
            }
            let block = emitter::emit_ast(nested_unit, &types, options)?;
            out.write_str(&printer::print(&block))?;
        }
        EmitMode::Ir | EmitMode::Nir => {
            for (index, function) in unit.into_iter().enumerate() {
                if index != 0 {
                    out.write_str("\n\n")?;
                }
                match options.emit {
                    EmitMode::Ir => function.write(out)?,
                    EmitMode::Nir => {
                        let diagnostics = diagnostics.for_proto(function.id.0);
                        let function = ir::nir::lift(function, &diagnostics)?;
                        write!(out, "{function:#?}")?;
                    }
                    EmitMode::Source => unreachable!("handled above"),
                }
            }
        }
    }
    Ok(())
}

/// Renders a control-flow graph visualization of Luau bytecode as a standalone HTML page.
#[cfg(feature = "visualize")]
pub fn visualize_bytecode(bytecode: &[u8], diagnostics: &Diagnostics) -> Result<String> {
    let span = tracing::info_span!("visualize_bytecode", byte_len = bytecode.len());
    let _enter = span.enter();

    let unit = lift_bytecode_with_diagnostics(bytecode, diagnostics)?;
    Ok(visualize::render_cfgs(&unit))
}
