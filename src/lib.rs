mod ast;
mod common;
mod disasm;
mod emitter;
mod hil;
mod il;
mod logging;
mod printer;
mod scopes;

pub use disasm::{DisasmError, Disassembly};
pub use logging::{
    DiagnosticConfig, Diagnostics, LogLevel, LogTarget, ProtoSelector, TracingGuard, init_tracing,
};

use crate::{
    emitter::options::EmitterOptions,
    hil::StructuredFunction,
    logging::{LogLevel as DiagnosticLevel, LogTarget as DiagnosticTarget},
};

/// Options controlling bytecode decompilation.
#[derive(Debug, Clone, Default)]
pub struct DecompileOptions {
    /// Spill emitter-introduced locals into table storage when Luau's local limit
    /// is exceeded.
    pub spill_locals: bool,
    /// Diagnostic output configuration.
    pub diagnostics: DiagnosticConfig,
}

/// Disassembles Luau bytecode without emitting diagnostics.
pub fn disassemble_bytecode(bytecode: &[u8]) -> Result<Disassembly, DisasmError> {
    disassemble_bytecode_with_diagnostics(bytecode, &Diagnostics::default())
}

/// Disassembles Luau bytecode using the provided diagnostics configuration.
pub fn disassemble_bytecode_with_diagnostics(
    bytecode: &[u8],
    diagnostics: &Diagnostics,
) -> Result<Disassembly, DisasmError> {
    let span = tracing::info_span!("disassemble", byte_len = bytecode.len());
    let _enter = span.enter();

    let info = diagnostics.at(DiagnosticLevel::Info, DiagnosticTarget::Driver);
    info.line(0, format_args!("disassembling..."));

    let disassembly = disasm::disassemble(bytecode)?;

    info.line(1, format_args!("LBC Version: {}", disassembly.version));
    info.line(1, format_args!("Proto count: {}", disassembly.protos.len()));
    info.line(1, format_args!("Entry: {}", disassembly.entry_proto));

    Ok(disassembly)
}

/// Decompiles Luau bytecode into Luau source code.
pub fn decompile_bytecode(
    bytecode: &[u8],
    options: DecompileOptions,
) -> Result<String, DisasmError> {
    let diagnostics = Diagnostics::new(options.diagnostics);
    decompile_bytecode_with_diagnostics(bytecode, options.spill_locals, &diagnostics)
}

/// Decompiles Luau bytecode using an already constructed diagnostics context.
pub fn decompile_bytecode_with_diagnostics(
    bytecode: &[u8],
    spill_locals: bool,
    diagnostics: &Diagnostics,
) -> Result<String, DisasmError> {
    let span = tracing::info_span!(
        "decompile_bytecode",
        byte_len = bytecode.len(),
        spill_locals
    );
    let _enter = span.enter();

    let disassembled = disassemble_bytecode_with_diagnostics(bytecode, diagnostics)?;
    let diagnostics = diagnostics.with_entry_proto(disassembled.entry_proto as usize);

    let mut functions: Vec<_> = {
        let span = tracing::info_span!("structure_protos", proto_count = disassembled.protos.len());
        let _enter = span.enter();

        disassembled
            .protos
            .iter()
            .map(|proto| StructuredFunction::from_proto(proto, &disassembled.protos, &diagnostics))
            .collect()
    };

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
        let span = tracing::info_span!("emit_ast", entry_proto = disassembled.entry_proto as usize);
        let _enter = span.enter();
        emitter::emit_ast(
            functions,
            disassembled.entry_proto as usize,
            EmitterOptions { spill_locals },
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
) -> Result<(), DisasmError> {
    let span = tracing::info_span!("visualize_bytecode", byte_len = bytecode.len());
    let _enter = span.enter();

    use crate::hil::cflow::{cfg::ControlFlowGraph, visualize::dump_cfgs};

    let disassembly = disassemble_bytecode_with_diagnostics(bytecode, diagnostics)?;
    let cfgs: Vec<_> = disassembly
        .protos
        .iter()
        .map(|proto| ControlFlowGraph::from_proto(proto, &disassembly.protos))
        .collect();

    dump_cfgs(
        &cfgs,
        disassembly.entry_proto as usize,
        output.as_ref().to_path_buf(),
    );
    Ok(())
}
