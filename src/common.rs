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
pub fn is_lua_ident(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) if c == '_' || c.is_ascii_alphabetic() => {}
        _ => return false,
    }

    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}
