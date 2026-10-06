//! Semantic styling for rendered text.
//!
//! Renderers tag each piece of text with a [`Style`] describing what it is.
//! How a style looks, if at all, is up to the [`StyledWrite`] sink: the plain
//! sinks provided here ignore styles entirely.

use std::fmt;

/// The kind of a piece of rendered text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Style {
    /// A section or function header.
    Heading,
    /// An instruction mnemonic.
    Opcode,
    /// A register reference.
    Register,
    /// An upvalue reference.
    Upvalue,
    /// A constant table reference.
    Constant,
    /// A number or boolean literal.
    Number,
    /// A string literal.
    String,
    /// A branch label.
    Label,
    /// A function, global or other symbol name.
    Name,
    /// Annotations that explain, rather than are, the output.
    Comment,
    /// Positions and line numbers in the margin.
    Gutter,
}

/// A text sink that can attach a [`Style`] to what it writes.
pub trait StyledWrite: fmt::Write {
    /// Writes `args` tagged with `style`.
    fn write_styled(&mut self, style: Style, args: fmt::Arguments<'_>) -> fmt::Result {
        let _ = style;
        self.write_fmt(args)
    }
}

impl StyledWrite for String {}

impl StyledWrite for fmt::Formatter<'_> {}

/// Writes formatted text tagged with a [`Style`] to a [`StyledWrite`] sink.
macro_rules! write_styled {
    ($w:expr, $style:expr, $($arg:tt)*) => {
        $w.write_styled($style, format_args!($($arg)*))
    };
}

pub(crate) use write_styled;
