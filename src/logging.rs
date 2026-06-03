use std::collections::BTreeSet;
use std::io::IsTerminal;
use std::str::FromStr;
use std::sync::OnceLock;
use std::time::Instant;

use clap::ValueEnum;

static START: OnceLock<Instant> = OnceLock::new();

const TARGET_WIDTH: usize = 6;

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
}

impl LogTarget {
    pub const fn label(&self) -> &'static str {
        match self {
            LogTarget::Driver => "driver",
            LogTarget::Hil => "hil",
            LogTarget::Cfg => "cfg",
            LogTarget::Region => "region",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtoSelector {
    Entry,
    Index(usize),
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
    entry_proto: Option<usize>,
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

    pub fn with_entry_proto(&self, entry_proto: usize) -> Self {
        let mut config = self.clone();
        config.entry_proto = Some(entry_proto);
        config
    }

    fn enabled(&self, level: LogLevel, target: LogTarget, proto: Option<usize>) -> bool {
        let Some(configured_level) = self.level else {
            return false;
        };

        configured_level >= level
            && (self.targets.is_empty() || self.targets.contains(&target))
            && self.proto_matches(target, proto)
    }

    fn proto_matches(&self, target: LogTarget, proto: Option<usize>) -> bool {
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
    proto: Option<usize>,
}

impl Diagnostics {
    pub fn new(config: DiagnosticConfig) -> Self {
        Self {
            config,
            proto: None,
        }
    }

    pub fn with_entry_proto(&self, entry_proto: usize) -> Self {
        Self {
            config: self.config.with_entry_proto(entry_proto),
            proto: self.proto,
        }
    }

    pub fn for_proto(&self, proto: usize) -> Self {
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

    pub fn line(&self, indent: usize, args: std::fmt::Arguments<'_>) {
        if self.enabled() {
            log_args(self.target, self.diagnostics.proto, indent, args);
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

pub fn elapsed_ms() -> u128 {
    START.get_or_init(Instant::now).elapsed().as_millis()
}

pub fn use_color() -> bool {
    std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none()
}

fn fit_target(target: &'static str) -> &'static str {
    if target.len() <= TARGET_WIDTH {
        return target;
    }

    &target[target.len() - TARGET_WIDTH..]
}

pub fn log_args(
    target: LogTarget,
    proto: Option<usize>,
    indent: usize,
    args: std::fmt::Arguments<'_>,
) {
    let target = fit_target(target.label());
    let indent_width = indent * 2;
    let proto = proto
        .map(|proto| format!(" P{proto:<4}"))
        .unwrap_or_default();

    if use_color() {
        eprintln!(
            "\x1b[2mT+{:>4}ms\x1b[0m \x1b[36m[{:<TARGET_WIDTH$}]\x1b[0m{proto} {:indent_width$}{}",
            elapsed_ms(),
            target,
            "",
            args,
        );
    } else {
        eprintln!(
            "T+{:>4}ms [{:<TARGET_WIDTH$}]{proto} {:indent_width$}{}",
            elapsed_ms(),
            target,
            "",
            args,
        );
    }
}
