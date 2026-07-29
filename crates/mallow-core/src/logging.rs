use std::collections::BTreeSet;
use std::str::FromStr;

/// Target used for structured diagnostic tracing events.
pub const DIAGNOSTIC_EVENT_TARGET: &str = "mallow::diagnostic";

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogLevel {
    Info,
    Debug,
    Trace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
