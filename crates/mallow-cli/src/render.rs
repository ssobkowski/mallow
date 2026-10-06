//! Terminal rendering of styled library output.

use std::fmt::{self, Write};

use clap::ValueEnum;
use mallow_core::style::{Style, StyledWrite};
use owo_colors::{OwoColorize, Stream, Style as Paint};

/// When to color output.
#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum ColorChoice {
    /// Color when writing to a terminal and `NO_COLOR` is unset.
    Auto,
    /// Always color.
    Always,
    /// Never color.
    Never,
}

impl ColorChoice {
    /// Applies this choice to every colored write in the process.
    pub fn apply(self) {
        match self {
            Self::Auto => {}
            Self::Always => owo_colors::set_override(true),
            Self::Never => owo_colors::set_override(false),
        }
    }
}

/// Buffers styled text, painted for stdout if stdout supports color.
#[derive(Default)]
pub struct StdoutPainter {
    buf: String,
}

impl StdoutPainter {
    /// Returns the rendered text.
    pub fn as_str(&self) -> &str {
        &self.buf
    }
}

impl Write for StdoutPainter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.buf.write_str(s)
    }
}

impl StyledWrite for StdoutPainter {
    fn write_styled(&mut self, style: Style, args: fmt::Arguments<'_>) -> fmt::Result {
        let paint = paint(style);
        write!(
            self.buf,
            "{}",
            args.if_supports_color(Stream::Stdout, |text| text.style(paint))
        )
    }
}

/// Returns the terminal look of a style.
fn paint(style: Style) -> Paint {
    let paint = Paint::new();
    match style {
        Style::Heading => paint.red().bold(),
        Style::Opcode => paint.cyan().bold(),
        Style::Register => paint.blue(),
        Style::Upvalue => paint.yellow(),
        Style::Constant => paint.magenta(),
        Style::Number => paint.magenta(),
        Style::String => paint.green(),
        Style::Label => paint.red().bold(),
        Style::Name => paint.bold(),
        Style::Comment | Style::Gutter => paint.dimmed(),
        _ => paint,
    }
}
