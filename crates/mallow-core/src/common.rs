use std::{fmt, rc::Rc};

use smol_str::SmolStr;

/// Owns the exact bytes of one Luau string.
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct ByteString(Rc<[u8]>);

impl ByteString {
    /// Returns the exact string bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Returns the string as UTF-8 when every byte is valid.
    #[must_use]
    pub fn as_utf8(&self) -> Option<&str> {
        std::str::from_utf8(self.as_bytes()).ok()
    }
}

impl fmt::Display for ByteString {
    /// Formats bytes with the same escapes used by quoted Luau literals.
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&escape_bytes(self.as_bytes()))
    }
}

impl From<&[u8]> for ByteString {
    /// Copies bytes into an owned Luau string.
    fn from(value: &[u8]) -> Self {
        Self(Rc::from(value))
    }
}

impl From<Vec<u8>> for ByteString {
    /// Moves bytes into an owned Luau string.
    fn from(value: Vec<u8>) -> Self {
        Self(Rc::from(value))
    }
}

impl From<Rc<[u8]>> for ByteString {
    /// Reuses shared byte storage for a Luau string.
    fn from(value: Rc<[u8]>) -> Self {
        Self(value)
    }
}

impl From<&str> for ByteString {
    /// Copies UTF-8 text into an owned Luau string.
    fn from(value: &str) -> Self {
        Self::from(value.as_bytes())
    }
}

impl From<String> for ByteString {
    /// Moves UTF-8 text into an owned Luau string.
    fn from(value: String) -> Self {
        Self::from(value.into_bytes())
    }
}

impl From<SmolStr> for ByteString {
    /// Copies compact UTF-8 text into an owned Luau string.
    fn from(value: SmolStr) -> Self {
        Self::from(value.as_str())
    }
}

/// Escapes bytes for use inside a quoted Luau string literal.
pub fn escape_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        match byte {
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            b'\0' => out.push_str("\\000"),
            b'"' => out.push_str("\\\""),
            0x20..=0x7E => out.push(char::from(byte)),
            _ => {
                use std::fmt::Write;
                write!(out, "\\{byte:03}").unwrap();
            }
        }
    }
    out
}

/// Returns whether if the given string is a valid Lua identifier.
pub fn is_valid_luau_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    let mut chars = s.chars();
    let first = chars.next().unwrap();

    // 1. Must start with a letter or underscore
    if !first.is_ascii_alphabetic() && first != '_' {
        return false;
    }

    // 2. Remaining characters must be alphanumeric or underscore
    for c in chars {
        if !c.is_ascii_alphanumeric() && c != '_' {
            return false;
        }
    }

    // 3. Must not be a strict reserved keyword
    const KEYWORDS: [&str; 21] = [
        "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in",
        "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while",
    ];
    !KEYWORDS.contains(&s)
}

#[cfg(test)]
mod tests {
    use super::is_valid_luau_identifier;

    #[test]
    fn test_valid_identifiers() {
        assert!(is_valid_luau_identifier("hello"));
        assert!(is_valid_luau_identifier("_hello"));
        assert!(is_valid_luau_identifier("hello_world"));
        assert!(is_valid_luau_identifier("_"));
        assert!(is_valid_luau_identifier("___"));
        assert!(is_valid_luau_identifier("hello123"));
        assert!(is_valid_luau_identifier("_123"));
        assert!(is_valid_luau_identifier("HelloWorld"));
        assert!(is_valid_luau_identifier("camelCase"));
        assert!(is_valid_luau_identifier("h1e2l3l4o5"));
    }

    #[test]
    fn test_empty_string() {
        assert!(!is_valid_luau_identifier(""));
    }

    #[test]
    fn test_starts_with_number() {
        assert!(!is_valid_luau_identifier("123hello"));
        assert!(!is_valid_luau_identifier("1"));
        assert!(!is_valid_luau_identifier("9_name"));
    }

    #[test]
    fn test_special_characters() {
        assert!(!is_valid_luau_identifier("hello-world"));
        assert!(!is_valid_luau_identifier("hello world"));
        assert!(!is_valid_luau_identifier("hello.world"));
        assert!(!is_valid_luau_identifier("hello@world"));
        assert!(!is_valid_luau_identifier("hello#world"));
        assert!(!is_valid_luau_identifier("hello$world"));
        assert!(!is_valid_luau_identifier("hello&world"));
        assert!(!is_valid_luau_identifier("hello*world"));
    }

    // Non-ASCII characters
    #[test]
    fn test_non_ascii_characters() {
        assert!(!is_valid_luau_identifier("héllo"));
        assert!(!is_valid_luau_identifier("你好"));
        assert!(!is_valid_luau_identifier("cześć"));
    }

    #[test]
    fn test_reserved_keywords() {
        let keywords = [
            "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in",
            "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while",
        ];
        for keyword in &keywords {
            assert!(
                !is_valid_luau_identifier(keyword),
                "keyword '{}' should be reserved",
                keyword
            );
        }
    }

    #[test]
    fn test_keyword_variations_valid() {
        assert!(is_valid_luau_identifier("hello_and"));
        assert!(is_valid_luau_identifier("whileSomething"));
        assert!(is_valid_luau_identifier("_if"));
        assert!(is_valid_luau_identifier("notValid"));
        assert!(is_valid_luau_identifier("and_123"));
    }
}
