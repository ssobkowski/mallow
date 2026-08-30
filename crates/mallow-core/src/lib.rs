mod ast;
mod common;
mod disasm;
mod emitter;
mod il;
mod ir;
mod logging;
mod operator;
mod printer;
mod scopes;

#[cfg(feature = "visualize")]
mod visualize;

use anyhow::{Result, ensure};
pub use logging::{
    DIAGNOSTIC_EVENT_TARGET, DiagnosticConfig, Diagnostics, LogLevel, LogTarget, ProtoSelector,
};

use crate::disasm::Chunk;
use crate::il::{BytecodeType, ProtoId, TypeTag};
use crate::ir::fir;
use crate::logging::{LogLevel as DiagnosticLevel, LogTarget as DiagnosticTarget};

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
    /// Emit conservative decompiler-inferred type annotations in addition to
    /// bytecode-recovered type annotations.
    pub infer_types: bool,
    /// Maximum number of post-region pass iterations per function.
    pub max_pass_iterations: usize,
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            emit: EmitMode::default(),
            spill_locals: false,
            infer_types: false,
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
                .map(|(i, tag)| format!("R{i}: {}", format_type_tag(*tag, &chunk)))
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
                info.line(
                    4,
                    format_args!("U{index}: {}", format_type_tag(*tag, &chunk)),
                );
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
                        format_type_tag(local.ty, &chunk),
                        local.start_pc,
                        local.end_pc
                    ),
                );
            }
        }
    }

    Ok(chunk)
}

fn format_type_tag(tag: TypeTag, chunk: &Chunk) -> String {
    let mut base = match tag.ty {
        BytecodeType::TaggedUserdata(index) => chunk
            .userdata_type_mappings
            .as_ref()
            .and_then(|mappings| {
                mappings
                    .iter()
                    .find(|mapping| mapping.index == index)
                    .map(|mapping| format!("{:?}", mapping.name))
            })
            .unwrap_or_else(|| format!("tagged-userdata[{index}]")),
        _ => tag.ty.to_string(),
    };

    if tag.optional {
        base.push('?');
    }

    base
}

/// Lifts Luau bytecode into the FIR.
///
/// Returns a tuple of the entry proto, and a vector of lifted functions.
pub fn lift_bytecode(bytecode: &[u8]) -> Result<(ProtoId, Vec<fir::Function>)> {
    lift_bytecode_with_diagnostics(bytecode, &Diagnostics::default())
}

/// Lifts Luau bytecode into the FIR using an existing diagnostics context.
///
/// Returns a tuple of the entry proto, and a vector of lifted functions.
pub fn lift_bytecode_with_diagnostics(
    bytecode: &[u8],
    diagnostics: &Diagnostics,
) -> Result<(ProtoId, Vec<fir::Function>)> {
    let span = tracing::info_span!("lift_bytecode", byte_len = bytecode.len());
    let _enter = span.enter();
    let chunk = disassemble_bytecode_with_diagnostics(bytecode, diagnostics)?;
    let functions = ir::fir::lift(&chunk)?;
    Ok((chunk.entry_proto, functions))
}

pub struct TypesView;

/// Infers named-local types from Luau bytecode.
pub fn infer_bytecode_types(bytecode: &[u8]) -> Result<TypesView> {
    infer_bytecode_types_with_diagnostics(bytecode, &Diagnostics::default())
}

/// Infers named-local types using an existing diagnostics context.
pub fn infer_bytecode_types_with_diagnostics(
    _bytecode: &[u8],
    _diagnostics: &Diagnostics,
) -> Result<TypesView> {
    // let span = tracing::info_span!("infer_bytecode_types", byte_len = bytecode.len());
    // let _enter = span.enter();
    // let (_, functions) = lift_bytecode_with_diagnostics(bytecode, diagnostics)?;
    // ty::inference::run(&mut functions);
    // Ok(TypesView::from_inferred(&functions))
    todo!("in works")
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
    let span = tracing::info_span!(
        "decompile_bytecode",
        byte_len = bytecode.len(),
        spill_locals = options.spill_locals,
        infer_types = options.infer_types,
        max_pass_iterations = options.max_pass_iterations,
        emit = ?options.emit,
    );
    let _enter = span.enter();

    // TODO: NonZeroUsize?
    ensure!(
        options.max_pass_iterations > 0,
        "max pass iterations must be greater than zero"
    );
    let chunk = disassemble_bytecode_with_diagnostics(bytecode, diagnostics)?;
    let functions = ir::fir::lift(&chunk)?;

    use core::fmt::Write;

    match options.emit {
        EmitMode::Source => {
            let mut nested_functions: Vec<_> = functions
                .iter()
                .map(|function| {
                    let diagnostics = diagnostics.for_proto(function.proto.0);
                    ir::nir::materialize::lower(function, &diagnostics)
                })
                .collect::<Result<_>>()?;
            ir::nir::passes::run(&mut nested_functions);
            for function in &mut nested_functions {
                ir::nir::materialize::destroy_ssa(function);
            }
            let block = emitter::emit_ast(nested_functions, chunk.entry_proto, options)?;
            Ok(printer::print(&block, &[]))
        }
        EmitMode::Ir | EmitMode::Nir => {
            let mut out = String::new();
            for (index, function) in functions.into_iter().enumerate() {
                if index != 0 {
                    out.push_str("\n\n");
                }
                match options.emit {
                    EmitMode::Ir => write!(out, "{function}"),
                    EmitMode::Nir => {
                        let diagnostics = diagnostics.for_proto(function.proto.0);
                        let function = ir::nir::materialize::lower(&function, &diagnostics)?;
                        write!(out, "{function:#?}")
                    }
                    EmitMode::Source => unreachable!("handled above"),
                }
                .expect("writing should not fail here");
            }
            Ok(out)
        }
    }
}

/// Generates a control-flow graph visualization from Luau bytecode.
#[cfg(feature = "visualize")]
pub fn visualize_bytecode(
    bytecode: &[u8],
    output: impl AsRef<std::path::Path>,
    diagnostics: &Diagnostics,
) -> Result<()> {
    let span = tracing::info_span!("visualize_bytecode", byte_len = bytecode.len());
    let _enter = span.enter();

    let (entry, functions) = lift_bytecode_with_diagnostics(bytecode, diagnostics)?;
    visualize::dump_cfgs(&functions, entry.0 as usize, output.as_ref().to_path_buf());
    Ok(())
}
