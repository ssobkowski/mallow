//! Diagnostic command-line options and the tracing layer that renders them.

use std::error::Error;
use std::fmt;
use std::io::IsTerminal;
use std::sync::OnceLock;
use std::time::Instant;

#[cfg(feature = "profile")]
use std::path::PathBuf;

use clap::ValueEnum;
use mallow_core::{DIAGNOSTIC_EVENT_TARGET, DiagnosticConfig, LogLevel, LogTarget};
use tracing::field::Visit;
use tracing::{Event, Subscriber};
use tracing_subscriber::layer::{Context, SubscriberExt};
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{Layer, Registry};

use crate::Cli;

static START: OnceLock<Instant> = OnceLock::new();

const TARGET_WIDTH: usize = 6;

/// Command-line diagnostic verbosity.
#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum CliLogLevel {
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
pub enum CliLogTarget {
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

/// Keeps optional tracing resources alive until process exit.
#[derive(Default)]
pub struct TracingGuard {
    #[cfg(feature = "profile")]
    _chrome_guard: Option<tracing_chrome::FlushGuard>,
}

#[cfg(not(feature = "profile"))]
pub fn init_tracing(cli: &Cli) -> TracingGuard {
    let _ = cli;
    init_tracing_layers().unwrap_or_else(|e| {
        eprintln!("failed to initialize tracing: {e}");
        std::process::exit(1);
    })
}

#[cfg(feature = "profile")]
pub fn init_tracing(cli: &Cli) -> TracingGuard {
    init_tracing_layers(cli.profile_output.clone()).unwrap_or_else(|e| {
        eprintln!("failed to initialize tracing: {e}");
        std::process::exit(1);
    })
}

/// Initializes tracing for CLI diagnostics.
#[cfg(not(feature = "profile"))]
fn init_tracing_layers() -> Result<TracingGuard, Box<dyn Error + Send + Sync>> {
    START.get_or_init(Instant::now);
    Registry::default().with(DiagnosticLayer).try_init()?;

    Ok(TracingGuard::default())
}

/// Initializes tracing for CLI diagnostics and optional Chrome trace output.
#[cfg(feature = "profile")]
fn init_tracing_layers(
    profile_output: Option<PathBuf>,
) -> Result<TracingGuard, Box<dyn Error + Send + Sync>> {
    START.get_or_init(Instant::now);

    let chrome_guard = match profile_output {
        Some(output) => {
            let (chrome_layer, guard) = tracing_chrome::ChromeLayerBuilder::new()
                .include_args(true)
                .file(output)
                .build();
            Registry::default()
                .with(DiagnosticLayer)
                .with(chrome_layer)
                .try_init()?;
            Some(guard)
        }
        None => {
            Registry::default().with(DiagnosticLayer).try_init()?;
            None
        }
    };

    Ok(TracingGuard {
        _chrome_guard: chrome_guard,
    })
}

pub fn diagnostic_config(cli: &Cli) -> DiagnosticConfig {
    let level = cli
        .log_level
        .map(LogLevel::from)
        .or_else(|| cli.verbose.then_some(LogLevel::Info));
    let targets = cli.log_target.iter().copied().map(LogTarget::from);

    DiagnosticConfig::new(level, targets, cli.log_proto.clone())
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
fn write_diagnostic_line(
    target: &str,
    proto: Option<u16>,
    indent: u64,
    warning: bool,
    message: &str,
) {
    let target = fit_target(target);
    let indent_width = (indent * 2) as usize;
    let proto = proto
        .map(|proto| format!(" P{proto:<4}"))
        .unwrap_or_default();

    if use_color() {
        let color = if warning { "\x1b[33m" } else { "\x1b[36m" };
        let message_color = if warning { color } else { "" };

        eprintln!(
            "\x1b[2mT+{:>4}ms\x1b[0m {color}[{:<TARGET_WIDTH$}]\x1b[0m{proto} {:indent_width$}{message_color}{}\x1b[0m",
            elapsed_ms(),
            target,
            "",
            message,
        );
    } else {
        eprintln!(
            "T+{:>4}ms [{:<TARGET_WIDTH$}]{proto} {:indent_width$}{message}",
            elapsed_ms(),
            target,
            "",
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
            event.metadata().level() == &tracing::Level::WARN,
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
