#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub pc: u32,
}

impl<T> Spanned<T> {
    #[inline]
    #[must_use]
    pub const fn new(node: T, pc: u32) -> Self {
        Self { node, pc }
    }

    #[inline]
    #[must_use]
    pub fn strip(self) -> T {
        self.node
    }

    #[inline]
    #[must_use]
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        Spanned {
            node: f(self.node),
            pc: self.pc,
        }
    }
}

pub trait ToSpanned {
    fn to_spanned(self, pc: u32) -> Spanned<Self>
    where
        Self: Sized,
    {
        Spanned::new(self, pc)
    }
}

/// Escapes a string for use in Lua string literals.
pub fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() * 2);
    for ch in s.chars() {
        let code = u32::from(ch);
        let byte = u8::try_from(code).unwrap_or(b'?');
        match byte {
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            b'\0' => out.push_str("\\0"),
            b'"' => out.push_str("\\\""),
            // printable ASCII (space through ~, excluding backslash already handled)
            0x20..=0x7E => out.push(byte as char),
            // control chars + high bytes
            _ => {
                use std::fmt::Write;
                write!(out, "\\{byte}").unwrap();
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
