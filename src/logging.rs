use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;
use std::io::IsTerminal;
#[cfg(feature = "profile")]
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::OnceLock;
use std::time::Instant;

use clap::ValueEnum;
use tracing::{Event, Subscriber, field::Visit};
use tracing_subscriber::{
    Layer, Registry,
    layer::{Context, SubscriberExt},
    util::SubscriberInitExt,
};

static START: OnceLock<Instant> = OnceLock::new();

const TARGET_WIDTH: usize = 6;
const DIAGNOSTIC_EVENT_TARGET: &str = "mallow::diagnostic";

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum LogLevel {
    Info,
    Debug,
    Trace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum LogTarget {
    Driver,
    Hil,
    Cfg,
    Region,
    Emitter,
}

impl LogTarget {
    pub const fn label(&self) -> &'static str {
        match self {
            LogTarget::Driver => "driver",
            LogTarget::Hil => "hil",
            LogTarget::Cfg => "cfg",
            LogTarget::Region => "region",
            LogTarget::Emitter => "emit",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtoSelector {
    Entry,
    Index(u16),
}

impl FromStr for ProtoSelector {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if value.eq_ignore_ascii_case("entry") {
            return Ok(Self::Entry);
        }

        value
            .parse()
            .map(Self::Index)
            .map_err(|_| format!("expected proto index or 'entry', got '{value}'"))
    }
}

#[derive(Debug, Clone)]
pub struct DiagnosticConfig {
    level: Option<LogLevel>,
    targets: BTreeSet<LogTarget>,
    protos: Vec<ProtoSelector>,
    entry_proto: Option<u16>,
}

impl DiagnosticConfig {
    pub fn quiet() -> Self {
        Self {
            level: None,
            targets: BTreeSet::new(),
            protos: Vec::new(),
            entry_proto: None,
        }
    }

    pub fn new(
        level: Option<LogLevel>,
        targets: impl IntoIterator<Item = LogTarget>,
        protos: Vec<ProtoSelector>,
    ) -> Self {
        START.get_or_init(Instant::now);

        Self {
            level,
            targets: targets.into_iter().collect(),
            protos,
            entry_proto: None,
        }
    }

    pub fn is_enabled(&self) -> bool {
        self.level.is_some()
    }

    pub fn with_entry_proto(&self, entry_proto: u16) -> Self {
        let mut config = self.clone();
        config.entry_proto = Some(entry_proto);
        config
    }

    fn enabled(&self, level: LogLevel, target: LogTarget, proto: Option<u16>) -> bool {
        let Some(configured_level) = self.level else {
            return false;
        };

        configured_level >= level
            && (self.targets.is_empty() || self.targets.contains(&target))
            && self.proto_matches(target, proto)
    }

    fn proto_matches(&self, target: LogTarget, proto: Option<u16>) -> bool {
        if self.protos.is_empty() || matches!(target, LogTarget::Driver) {
            return true;
        }

        let Some(proto) = proto else {
            return false;
        };

        self.protos.iter().any(|selector| match selector {
            ProtoSelector::Index(index) => *index == proto,
            ProtoSelector::Entry => self.entry_proto == Some(proto),
        })
    }
}

impl Default for DiagnosticConfig {
    fn default() -> Self {
        Self::quiet()
    }
}

#[derive(Debug, Clone)]
pub struct Diagnostics {
    config: DiagnosticConfig,
    proto: Option<u16>,
}

impl Diagnostics {
    pub fn new(config: DiagnosticConfig) -> Self {
        Self {
            config,
            proto: None,
        }
    }

    pub fn with_entry_proto(&self, entry_proto: u16) -> Self {
        Self {
            config: self.config.with_entry_proto(entry_proto),
            proto: self.proto,
        }
    }

    pub fn for_proto(&self, proto: u16) -> Self {
        Self {
            config: self.config.clone(),
            proto: Some(proto),
        }
    }

    pub fn enabled(&self, level: LogLevel, target: LogTarget) -> bool {
        self.config.enabled(level, target, self.proto)
    }

    pub fn at(&self, level: LogLevel, target: LogTarget) -> DiagnosticSink<'_> {
        DiagnosticSink {
            diagnostics: self,
            level,
            target,
        }
    }
}

impl Default for Diagnostics {
    fn default() -> Self {
        Self::new(DiagnosticConfig::default())
    }
}

pub struct DiagnosticSink<'a> {
    diagnostics: &'a Diagnostics,
    level: LogLevel,
    target: LogTarget,
}

impl DiagnosticSink<'_> {
    pub fn enabled(&self) -> bool {
        self.diagnostics.enabled(self.level, self.target)
    }

    pub fn line(&self, indent: u16, args: std::fmt::Arguments<'_>) {
        if self.enabled() {
            emit_diagnostic_event(
                self.level,
                self.target,
                self.diagnostics.proto,
                indent,
                args,
            );
        }
    }

    pub fn block(&self, title: &str, write_body: impl FnOnce(&Self)) {
        if !self.enabled() {
            return;
        }

        self.line(0, format_args!("{title}"));
        write_body(self);
    }
}

#[derive(Default)]
pub struct TracingGuard {
    #[cfg(feature = "profile")]
    _chrome_guard: Option<tracing_chrome::FlushGuard>,
}

/// Initializes tracing for CLI diagnostics.
#[cfg(not(feature = "profile"))]
pub fn init_tracing(
    diagnostics_enabled: bool,
) -> Result<TracingGuard, Box<dyn Error + Send + Sync>> {
    if diagnostics_enabled {
        Registry::default().with(DiagnosticLayer).try_init()?;
    }

    Ok(TracingGuard::default())
}

/// Initializes tracing for CLI diagnostics and optional Chrome trace output.
#[cfg(feature = "profile")]
pub fn init_tracing(
    diagnostics_enabled: bool,
    profile_output: Option<PathBuf>,
) -> Result<TracingGuard, Box<dyn Error + Send + Sync>> {
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

pub fn elapsed_ms() -> u128 {
    START.get_or_init(Instant::now).elapsed().as_millis()
}

pub fn use_color() -> bool {
    std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none()
}

fn fit_target(target: &str) -> &str {
    if target.len() <= TARGET_WIDTH {
        return target;
    }

    &target[target.len() - TARGET_WIDTH..]
}

fn emit_diagnostic_event(
    level: LogLevel,
    target: LogTarget,
    proto: Option<u16>,
    indent: u16,
    args: std::fmt::Arguments<'_>,
) {
    let proto = proto.map(|proto| proto as i64).unwrap_or(-1);
    let indent = indent as u64;

    match level {
        LogLevel::Info => tracing::event!(
            target: DIAGNOSTIC_EVENT_TARGET,
            tracing::Level::INFO,
            log_target = target.label(),
            proto,
            indent,
            message = %args
        ),
        LogLevel::Debug => tracing::event!(
            target: DIAGNOSTIC_EVENT_TARGET,
            tracing::Level::DEBUG,
            log_target = target.label(),
            proto,
            indent,
            message = %args
        ),
        LogLevel::Trace => tracing::event!(
            target: DIAGNOSTIC_EVENT_TARGET,
            tracing::Level::TRACE,
            log_target = target.label(),
            proto,
            indent,
            message = %args
        ),
    }
}

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
