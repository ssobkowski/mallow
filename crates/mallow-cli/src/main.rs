use std::{
    error::Error,
    fmt,
    io::{IsTerminal, Write},
    path::PathBuf,
    process::Command,
    sync::OnceLock,
    time::Instant,
};

use anyhow::{Result, ensure};
use clap::{Parser, Subcommand, ValueEnum};
use mallow_core::{
    DEFAULT_MAX_PASS_ITERATIONS, DIAGNOSTIC_EVENT_TARGET, DecompileOptions, DiagnosticConfig,
    Diagnostics, EmitMode, LogLevel, LogTarget, ProtoSelector, decompile_bytecode_with_diagnostics,
    disassemble_bytecode_with_diagnostics,
};
use tracing::{Event, Subscriber, field::Visit};
use tracing_subscriber::{
    Layer, Registry,
    layer::{Context, SubscriberExt},
    util::SubscriberInitExt,
};

static START: OnceLock<Instant> = OnceLock::new();

const TARGET_WIDTH: usize = 6;

/// Command-line diagnostic verbosity.
#[derive(Debug, Clone, Copy, ValueEnum)]
enum CliLogLevel {
    /// Show high-level progress.
    Info,
    /// Show detailed structure diagnostics.
    Debug,
    /// Show the most detailed diagnostics.
    Trace,
}

impl From<CliLogLevel> for LogLevel {
    fn from(level: CliLogLevel) -> Self {
        match level {
            CliLogLevel::Info => Self::Info,
            CliLogLevel::Debug => Self::Debug,
            CliLogLevel::Trace => Self::Trace,
        }
    }
}

/// Command-line diagnostic target.
#[derive(Debug, Clone, Copy, ValueEnum)]
enum CliLogTarget {
    /// Driver-level diagnostics.
    Driver,
    /// HIL diagnostics.
    Hil,
    /// Control-flow graph diagnostics.
    Cfg,
    /// Region structuring diagnostics.
    Region,
    /// Emitter diagnostics.
    Emitter,
}

impl From<CliLogTarget> for LogTarget {
    fn from(target: CliLogTarget) -> Self {
        match target {
            CliLogTarget::Driver => Self::Driver,
            CliLogTarget::Hil => Self::Hil,
            CliLogTarget::Cfg => Self::Cfg,
            CliLogTarget::Region => Self::Region,
            CliLogTarget::Emitter => Self::Emitter,
        }
    }
}

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    #[arg(short, long, global = true)]
    verbose: bool,

    /// Diagnostic verbosity. Use with --log-target and --log-proto for large files.
    #[arg(long, global = true, value_enum)]
    log_level: Option<CliLogLevel>,

    /// Diagnostic target to enable. Repeatable. Defaults to all targets at the selected level.
    #[arg(long, global = true, value_enum, value_delimiter = ',')]
    log_target: Vec<CliLogTarget>,

    /// Proto diagnostic filter. Accepts a proto index or 'entry'. Repeatable.
    #[arg(long, global = true, value_delimiter = ',')]
    log_proto: Vec<ProtoSelector>,

    /// Write a Chrome trace profile to this path.
    #[cfg(feature = "profile")]
    #[arg(long, global = true, value_name = "PATH")]
    profile_output: Option<PathBuf>,
}

/// Output form selected by the command line.
#[derive(Debug, Clone, Copy, ValueEnum)]
enum Emit {
    /// Emit cleaned Luau source code.
    Source,
    /// Emit regioned SSA with its original symbol IDs.
    Ssa,
}

impl Emit {
    /// Returns the matching library output mode.
    const fn mode(self) -> EmitMode {
        match self {
            Self::Source => EmitMode::Source,
            Self::Ssa => EmitMode::Ssa,
        }
    }
}

/// Parses a positive cleanup pass iteration limit.
fn parse_max_pass_iterations(value: &str) -> Result<usize, String> {
    let iterations = value
        .parse::<usize>()
        .map_err(|_| format!("expected a positive integer, got '{value}'"))?;
    if iterations == 0 {
        return Err("max pass iterations must be greater than zero".to_string());
    }
    Ok(iterations)
}

#[cfg(test)]
mod tests {
    use super::parse_max_pass_iterations;

    /// Positive pass limits are accepted.
    #[test]
    fn parses_max_pass_iterations() {
        assert_eq!(parse_max_pass_iterations("12"), Ok(12));
    }

    /// A zero pass limit is rejected.
    #[test]
    fn rejects_zero_max_pass_iterations() {
        assert_eq!(
            parse_max_pass_iterations("0"),
            Err("max pass iterations must be greater than zero".to_string())
        );
    }
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
    /// Emit a bytecode file as cleaned Luau or regioned SSA
    Decompile {
        /// Path to the input bytecode file
        #[arg(short, long)]
        input: PathBuf,

        /// Output file path. Prints to stdout if omitted
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Output form to emit
        #[arg(long, value_enum, default_value = "source")]
        emit: Emit,

        /// Spill emitter-introduced locals into table storage when Luau's local limit is exceeded
        #[arg(long)]
        spill_locals: bool,

        /// Emit conservative decompiler-inferred type annotations
        #[arg(long)]
        infer_types: bool,

        /// Maximum number of cleanup pass iterations per function
        #[arg(
            long,
            default_value_t = DEFAULT_MAX_PASS_ITERATIONS,
            value_parser = parse_max_pass_iterations
        )]
        max_pass_iterations: usize,
    },
    /// Compile a Luau source file and emit cleaned Luau or regioned SSA
    Roundtrip {
        /// Path to the input Luau source file
        #[arg(short, long)]
        input: PathBuf,

        /// Output file path. Prints to stdout if omitted
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Optimization level, passed as '-O<n>' to the Luau compiler.
        #[arg(long, value_parser = clap::value_parser!(u8).range(0..=2))]
        opt_level: Option<u8>,

        /// Debug info level, passed as '-g<n>' to the Luau compiler.
        #[arg(long, value_parser = clap::value_parser!(u8).range(0..=2))]
        debug_level: Option<u8>,

        /// Type info level, passed as '-t<n>' to the Luau compiler.
        #[arg(long, value_parser = clap::value_parser!(u8).range(0..=1))]
        type_level: Option<u8>,

        /// Output form to emit
        #[arg(long, value_enum, default_value = "source")]
        emit: Emit,

        /// Spill emitter-introduced locals into table storage when Luau's local limit is exceeded
        #[arg(long)]
        spill_locals: bool,

        /// Emit conservative decompiler-inferred type annotations
        #[arg(long)]
        infer_types: bool,

        /// Maximum number of cleanup pass iterations per function
        #[arg(
            long,
            default_value_t = DEFAULT_MAX_PASS_ITERATIONS,
            value_parser = parse_max_pass_iterations
        )]
        max_pass_iterations: usize,
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

fn main() -> Result<()> {
    let cli = Cli::parse();
    let diagnostic_config = diagnostic_config(&cli);
    let _tracing_guard = init_tracing(&cli, diagnostic_config.is_enabled());
    let diagnostics = Diagnostics::new(diagnostic_config);

    match cli.command {
        Commands::Disasm { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            let chunk = disassemble_bytecode_with_diagnostics(&bytecode, &diagnostics)?;
            let mut out = get_output(output)?;
            chunk.dump(&mut out)?;
            Ok(())
        }
        Commands::Decompile {
            input,
            output,
            emit,
            spill_locals,
            infer_types,
            max_pass_iterations,
        } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");

            diagnostics
                .at(LogLevel::Info, LogTarget::Driver)
                .line(0, format_args!("decompiling..."));
            let code = decompile_bytecode_with_diagnostics(
                &bytecode,
                DecompileOptions {
                    emit: emit.mode(),
                    spill_locals,
                    infer_types,
                    max_pass_iterations,
                },
                &diagnostics,
            )?;

            let mut out = get_output(output)?;
            out.write_all(code.as_bytes())?;
            Ok(())
        }
        Commands::Roundtrip {
            input,
            output,
            opt_level,
            debug_level,
            type_level,
            emit,
            spill_locals,
            infer_types,
            max_pass_iterations,
        } => {
            let mut cmd = Command::new("luau-compile");
            cmd.arg("--binary");
            cmd.arg(input);
            if let Some(opt_level) = opt_level {
                cmd.arg(format!("-O{}", opt_level));
            }
            if let Some(debug_level) = debug_level {
                cmd.arg(format!("-g{}", debug_level));
            }
            if let Some(type_level) = type_level {
                cmd.arg(format!("-t{}", type_level));
            }

            let compile_out = cmd.output()?;

            ensure!(
                compile_out.status.success(),
                "failed to compile:\n{}",
                String::from_utf8_lossy(&compile_out.stderr).trim()
            );

            let code = decompile_bytecode_with_diagnostics(
                &compile_out.stdout,
                DecompileOptions {
                    emit: emit.mode(),
                    spill_locals,
                    infer_types,
                    max_pass_iterations,
                },
                &diagnostics,
            )?;

            let mut out = get_output(output)?;
            out.write_all(code.as_bytes())?;
            Ok(())
        }
        #[cfg(feature = "visualize")]
        Commands::Visualize { input, output } => {
            let bytecode = std::fs::read(input).expect("Failed to read bytecode file");
            mallow_core::visualize_bytecode(&bytecode, output, &diagnostics)
        }
    }
}

/// Keeps optional tracing resources alive until process exit.
#[derive(Default)]
struct TracingGuard {
    #[cfg(feature = "profile")]
    _chrome_guard: Option<tracing_chrome::FlushGuard>,
}

#[cfg(not(feature = "profile"))]
fn init_tracing(cli: &Cli, diagnostics_enabled: bool) -> TracingGuard {
    let _ = cli;
    init_tracing_layers(diagnostics_enabled).unwrap_or_else(|e| {
        eprintln!("failed to initialize tracing: {e}");
        std::process::exit(1);
    })
}

#[cfg(feature = "profile")]
fn init_tracing(cli: &Cli, diagnostics_enabled: bool) -> TracingGuard {
    init_tracing_layers(diagnostics_enabled, cli.profile_output.clone()).unwrap_or_else(|e| {
        eprintln!("failed to initialize tracing: {e}");
        std::process::exit(1);
    })
}

/// Initializes tracing for CLI diagnostics.
#[cfg(not(feature = "profile"))]
fn init_tracing_layers(
    diagnostics_enabled: bool,
) -> Result<TracingGuard, Box<dyn Error + Send + Sync>> {
    if diagnostics_enabled {
        START.get_or_init(Instant::now);
        Registry::default().with(DiagnosticLayer).try_init()?;
    }

    Ok(TracingGuard::default())
}

/// Initializes tracing for CLI diagnostics and optional Chrome trace output.
#[cfg(feature = "profile")]
fn init_tracing_layers(
    diagnostics_enabled: bool,
    profile_output: Option<PathBuf>,
) -> Result<TracingGuard, Box<dyn Error + Send + Sync>> {
    if diagnostics_enabled || profile_output.is_some() {
        START.get_or_init(Instant::now);
    }

    let chrome_guard = match profile_output {
        Some(output) => {
            if diagnostics_enabled {
                let (chrome_layer, guard) = tracing_chrome::ChromeLayerBuilder::new()
                    .include_args(true)
                    .file(output)
                    .build();
                Registry::default()
                    .with(DiagnosticLayer)
                    .with(chrome_layer)
                    .try_init()?;
                Some(guard)
            } else {
                let (chrome_layer, guard) = tracing_chrome::ChromeLayerBuilder::new()
                    .include_args(true)
                    .file(output)
                    .build();
                Registry::default().with(chrome_layer).try_init()?;
                Some(guard)
            }
        }
        None => {
            if diagnostics_enabled {
                Registry::default().with(DiagnosticLayer).try_init()?;
            }

            None
        }
    };

    Ok(TracingGuard {
        _chrome_guard: chrome_guard,
    })
}

fn diagnostic_config(cli: &Cli) -> DiagnosticConfig {
    let level = cli
        .log_level
        .map(LogLevel::from)
        .or_else(|| cli.verbose.then_some(LogLevel::Info));
    let targets = cli.log_target.iter().copied().map(LogTarget::from);

    DiagnosticConfig::new(level, targets, cli.log_proto.clone())
}

fn get_output(path: Option<PathBuf>) -> std::io::Result<Box<dyn std::io::Write>> {
    match path {
        Some(path) => Ok(Box::new(std::fs::File::create(path)?)),
        None => Ok(Box::new(std::io::stdout())),
    }
}

/// Returns elapsed milliseconds since tracing began.
fn elapsed_ms() -> u128 {
    START.get_or_init(Instant::now).elapsed().as_millis()
}

/// Returns whether diagnostics should use terminal color.
fn use_color() -> bool {
    std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none()
}

/// Fits a diagnostic target into the fixed CLI target column.
fn fit_target(target: &str) -> &str {
    if target.len() <= TARGET_WIDTH {
        return target;
    }

    &target[target.len() - TARGET_WIDTH..]
}

/// Writes one formatted diagnostic line to stderr.
fn write_diagnostic_line(target: &str, proto: Option<u16>, indent: u64, message: &str) {
    let target = fit_target(target);
    let indent_width = (indent * 2) as usize;
    let proto = proto
        .map(|proto| format!(" P{proto:<4}"))
        .unwrap_or_default();

    if use_color() {
        eprintln!(
            "\x1b[2mT+{:>4}ms\x1b[0m \x1b[36m[{:<TARGET_WIDTH$}]\x1b[0m{proto} {:indent_width$}{}",
            elapsed_ms(),
            target,
            "",
            message,
        );
    } else {
        eprintln!(
            "T+{:>4}ms [{:<TARGET_WIDTH$}]{proto} {:indent_width$}{}",
            elapsed_ms(),
            target,
            "",
            message,
        );
    }
}

/// Tracing layer that renders core diagnostic events for humans.
struct DiagnosticLayer;

impl<S> Layer<S> for DiagnosticLayer
where
    S: Subscriber,
{
    fn on_event(&self, event: &Event<'_>, _ctx: Context<'_, S>) {
        if event.metadata().target() != DIAGNOSTIC_EVENT_TARGET {
            return;
        }

        let mut diagnostic = DiagnosticEvent::default();
        event.record(&mut diagnostic);

        let Some(message) = diagnostic.message else {
            return;
        };

        write_diagnostic_line(
            diagnostic
                .log_target
                .as_deref()
                .unwrap_or(LogTarget::Driver.label()),
            diagnostic
                .proto
                .and_then(|proto| (proto >= 0).then_some(proto as u16)),
            diagnostic.indent.unwrap_or(0),
            &message,
        );
    }
}

/// Parsed fields for one diagnostic tracing event.
#[derive(Default)]
struct DiagnosticEvent {
    log_target: Option<String>,
    proto: Option<i64>,
    indent: Option<u64>,
    message: Option<String>,
}

impl Visit for DiagnosticEvent {
    fn record_i64(&mut self, field: &tracing::field::Field, value: i64) {
        if field.name() == "proto" {
            self.proto = Some(value);
        }
    }

    fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
        if field.name() == "indent" {
            self.indent = Some(value);
        }
    }

    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        match field.name() {
            "log_target" => self.log_target = Some(value.to_owned()),
            "message" => self.message = Some(value.to_owned()),
            _ => {}
        }
    }

    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn fmt::Debug) {
        if field.name() == "message" {
            self.message = Some(format!("{value:?}"));
        }
    }
}
