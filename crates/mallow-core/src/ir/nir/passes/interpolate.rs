//! Turns `("a%*b"):format(x)` calls into string interpolations like `` `a{x}b` ``.
//!
//! The Luau compiler lowers every interpolated string to such a call and keeps
//! one result. A call qualifies when its receiver is a constant string, every
//! format specifier in it is `%*` or `%%`, and it passes exactly one value per
//! `%*`. Both forms build the same string, so the rewrite holds for calls
//! written by hand too.

use crate::common::ByteString;
use crate::ir::fir::Constant;
use crate::ir::nir::visitor::{VisitorMut, walk_expr_mut};
use crate::ir::nir::{Expr, Function, PackExpr, TemplatePart};

pub(super) fn run(function: &mut Function) -> bool {
    let mut rewriter = Rewriter::default();
    rewriter.visit_function(function);
    rewriter.changed
}

#[derive(Default)]
struct Rewriter {
    changed: bool,
}

impl VisitorMut for Rewriter {
    fn visit_expr(&mut self, expr: &mut Expr) {
        walk_expr_mut(self, expr);
        if let Some(parts) = template_parts(expr) {
            *expr = Expr::Interpolation(parts);
            self.changed = true;
        }
    }
}

/// Returns the parts of the interpolation that builds the same string as the
/// expression, taking the call arguments out of it.
///
/// Returns `None` and leaves the expression unchanged when it does not qualify.
fn template_parts(expr: &mut Expr) -> Option<Vec<TemplatePart>> {
    let Expr::Project { pack, index: 0 } = expr else {
        return None;
    };
    let PackExpr::MethodCall {
        object,
        method,
        args,
    } = pack.as_mut()
    else {
        return None;
    };
    let Expr::Constant(Constant::String(format)) = object.as_ref() else {
        return None;
    };
    if method != "format" {
        return None;
    }

    // A format string without slots builds plain text, which the compiler
    // never emits as a call.
    let texts = split_format(format)?;
    let slots = texts.len() - 1;
    if slots == 0 || args.fixed_len() != Some(slots) {
        return None;
    }

    let empty = PackExpr::Values {
        head: Vec::new(),
        tail: None,
    };
    let mut values = std::mem::replace(args.as_mut(), empty).into_iter();
    let mut parts = Vec::with_capacity(texts.len() + slots);
    for (i, text) in texts.into_iter().enumerate() {
        if i > 0 {
            let value = values.next().expect("argument count matches slot count");
            parts.push(TemplatePart::Value(value));
        }
        if !text.as_ref().is_empty() {
            parts.push(TemplatePart::Text(text));
        }
    }
    Some(parts)
}

/// Splits a format string at each `%*` slot and turns each `%%` into `%`.
///
/// The result always holds one more text than there are slots. Returns `None`
/// when the string holds any other specifier or ends in a lone `%`.
fn split_format(format: &ByteString) -> Option<Vec<ByteString>> {
    let mut texts = Vec::new();
    let mut text = Vec::new();
    let mut bytes = format.as_ref().iter().copied();
    while let Some(byte) = bytes.next() {
        if byte != b'%' {
            text.push(byte);
            continue;
        }
        match bytes.next()? {
            b'*' => texts.push(ByteString::from(std::mem::take(&mut text))),
            b'%' => text.push(b'%'),
            _ => return None,
        }
    }
    texts.push(ByteString::from(text));
    Some(texts)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn split(format: &str) -> Option<Vec<String>> {
        let texts = split_format(&ByteString::from(format.as_bytes()))?;
        Some(
            texts
                .iter()
                .map(|text| text.as_utf8().unwrap().to_string())
                .collect(),
        )
    }

    #[test]
    fn splits_at_slots() {
        assert_eq!(split("%* %*").unwrap(), ["", " ", ""]);
        assert_eq!(split("a%*b").unwrap(), ["a", "b"]);
        assert_eq!(split("plain").unwrap(), ["plain"]);
    }

    #[test]
    fn turns_double_percent_into_text() {
        assert_eq!(split("%%*").unwrap(), ["%*"]);
        assert_eq!(split("100%% %*").unwrap(), ["100% ", ""]);
    }

    #[test]
    fn rejects_other_specifiers() {
        assert_eq!(split("%d"), None);
        assert_eq!(split("%* %5s"), None);
        assert_eq!(split("trailing %"), None);
    }
}
