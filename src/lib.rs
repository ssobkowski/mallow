mod ast;
mod common;
mod disasm;
mod emitter;
mod hil;
mod il;
mod logging;
mod operator;
mod printer;
mod scopes;

pub use logging::{
    DiagnosticConfig, Diagnostics, LogLevel, LogTarget, ProtoSelector, TracingGuard, init_tracing,
};

use anyhow::Result;

use crate::{
    disasm::Chunk,
    hil::{StructuredFunction, lifted::LiftedFunction},
    il::{BytecodeType, ProtoTypeInfo, TypeTag},
    logging::{LogLevel as DiagnosticLevel, LogTarget as DiagnosticTarget},
};

/// Options controlling bytecode decompilation.
#[derive(Debug, Clone, Copy, Default)]
pub struct DecompileOptions {
    /// Spill emitter-introduced locals into table storage when Luau's local limit
    /// is exceeded.
    pub spill_locals: bool,
    /// Emit conservative decompiler-inferred type annotations in addition to
    /// bytecode-recovered type annotations.
    pub infer_types: bool,
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
    dump_type_info(&chunk, &info);

    Ok(chunk)
}

fn dump_type_info(chunk: &Chunk, info: &logging::DiagnosticSink<'_>) {
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
        dump_proto_type_info(type_info, chunk, info);
    }
}

fn dump_proto_type_info(
    type_info: &ProtoTypeInfo,
    chunk: &Chunk,
    info: &logging::DiagnosticSink<'_>,
) {
    if let Some(function) = &type_info.function {
        let params = function
            .params
            .iter()
            .enumerate()
            .map(|(i, tag)| format!("R{i}: {}", format_type_tag(*tag, chunk)))
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
                format_args!("U{index}: {}", format_type_tag(*tag, chunk)),
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
                    format_type_tag(local.ty, chunk),
                    local.start_pc,
                    local.end_pc
                ),
            );
        }
    }
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

/// Decompiles Luau bytecode into Luau source code.
pub fn decompile_bytecode(bytecode: &[u8], options: DecompileOptions) -> Result<String> {
    decompile_bytecode_with_diagnostics(bytecode, options, &Diagnostics::default())
}

/// Decompiles Luau bytecode using an already constructed diagnostics context.
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
    );
    let _enter = span.enter();

    let disassembled = disassemble_bytecode_with_diagnostics(bytecode, diagnostics)?;
    let diagnostics = diagnostics.with_entry_proto(disassembled.entry_proto.0);

    let mut lifted: Vec<_> = {
        let span = tracing::info_span!("lift_protos", proto_count = disassembled.protos.len());
        let _enter = span.enter();

        disassembled
            .protos
            .iter()
            .map(|proto| LiftedFunction::from_proto(proto, &disassembled, &diagnostics))
            .collect::<Result<_, _>>()?
    };

    if options.infer_types {
        hil::ty2::inference::run(&mut lifted);
    }

    let mut functions: Vec<_> = lifted
        .into_iter()
        .map(|fun| StructuredFunction::from_lifted(fun, &diagnostics))
        .collect::<Result<_, _>>()?;

    diagnostics
        .at(DiagnosticLevel::Info, DiagnosticTarget::Driver)
        .line(0, format_args!("running passes..."));
    {
        let span = tracing::info_span!("run_post_region_passes", function_count = functions.len());
        let _enter = span.enter();
        hil::passes::run(&mut functions);
    }

    diagnostics
        .at(DiagnosticLevel::Info, DiagnosticTarget::Driver)
        .line(0, format_args!("emitting AST..."));
    let ast = {
        let span = tracing::info_span!("emit_ast", entry_proto = disassembled.entry_proto.0);
        let _enter = span.enter();
        emitter::emit_ast(
            functions,
            disassembled.entry_proto.0 as usize,
            options,
            &diagnostics,
        )
    };

    let comments = vec![format!(
        "Decompiled by mallow {}",
        env!("CARGO_PKG_VERSION")
    )];

    diagnostics
        .at(DiagnosticLevel::Info, DiagnosticTarget::Driver)
        .line(0, format_args!("done"));
    let source = {
        let span = tracing::info_span!("print_ast");
        let _enter = span.enter();
        printer::print(&ast, &comments)
    };
    Ok(source)
}

/// Generates a control-flow graph visualization from Luau bytecode.
#[cfg(feature = "visualize")]
pub fn visualize_bytecode(
    bytecode: &[u8],
    output: impl AsRef<std::path::Path>,
    diagnostics: &Diagnostics,
) -> Result<()> {
    use crate::hil::{cflow::visualize::dump_cfgs, lifted::LiftedFunction};

    let span = tracing::info_span!("visualize_bytecode", byte_len = bytecode.len());
    let _enter = span.enter();

    let disassembly = disassemble_bytecode_with_diagnostics(bytecode, diagnostics)?;
    let cfgs: Vec<_> = disassembly
        .protos
        .iter()
        .map(|proto| {
            LiftedFunction::from_proto(proto, &disassembly, diagnostics).map(|lifted| lifted.cfg)
        })
        .collect::<Result<_, _>>()?;

    dump_cfgs(
        &cfgs,
        disassembly.entry_proto.0 as usize,
        output.as_ref().to_path_buf(),
    );
    Ok(())
}
