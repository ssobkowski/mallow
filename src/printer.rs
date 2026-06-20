use crate::{
    ast::{BinOp, Block, ElseClause, Expr, If, Literal, Parameter, Stmt, TableItem, UnOp},
    common::escape_string,
};

pub fn print(block: &Block, top_comments: &[String]) -> String {
    let mut buf = String::new();

    if !top_comments.is_empty() {
        for comment in top_comments {
            buf.push_str("-- ");
            buf.push_str(comment);
            buf.push('\n');
        }
        buf.push('\n');
    }

    let mut printer = AstPrinter::new();
    printer.walk_block(block);
    buf.push_str(&printer.finish());
    buf.push('\n');
    buf
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Assoc {
    Left,
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Left,
    Right,
    None,
}

struct AstPrinter {
    out: String,
    indent: usize,
    line_start: bool,
}

impl AstPrinter {
    fn new() -> Self {
        Self {
            out: String::new(),
            indent: 0,
            line_start: true,
        }
    }

    fn finish(mut self) -> String {
        while self.out.ends_with('\n') {
            self.out.pop();
        }
        self.out
    }

    fn walk_block(&mut self, block: &Block) {
        for stmt in block.stmts() {
            self.walk_stmt(stmt);
        }
    }

    fn walk_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assignment { lhs, rhs } => {
                self.write("");
                self.write_punctuated(lhs, ", ", |p, lv| p.walk_expr(lv, 0, Side::None));
                self.write(" = ");
                self.write_punctuated(rhs, ", ", |p, rv| p.walk_expr(rv, 0, Side::None));
                self.newline();
            }
            Stmt::Comment { text } => {
                self.write("-- ");
                self.write(text);
                self.newline();
            }
            Stmt::CompoundAssignment { lhs, op, rhs } => {
                self.walk_expr(lhs, 0, Side::None);
                self.write(" ");
                self.write(op.as_str());
                self.write(" ");
                self.walk_expr(rhs, 0, Side::None);
                self.newline();
            }
            Stmt::Break => {
                self.write("break");
                self.newline();
            }
            Stmt::Continue => {
                self.write("continue");
                self.newline();
            }
            Stmt::Do { body } => {
                self.write("do");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("end");
                self.newline();
            }
            Stmt::Expression { expr } => {
                self.write("");
                self.walk_expr(expr, 0, Side::None);
                self.newline();
            }
            Stmt::GenericFor { vars, exprs, body } => {
                self.write("for ");
                self.write_punctuated(vars, ", ", |p, var| p.write(var.as_str()));
                self.write(" in ");
                self.write_punctuated(exprs, ", ", |p, expr| p.walk_expr(expr, 0, Side::None));
                self.write(" do");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("end");
                self.newline();
            }
            Stmt::If(if_stmt) => {
                self.walk_if_stmt(if_stmt, true);
            }
            Stmt::LocalFunction { name, params, body } => {
                self.write("local function ");
                self.write(name.as_str());
                self.write("(");
                self.write_params(params);
                self.write(")");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("end");
                self.newline();
            }
            Stmt::LocalDeclaration { names, values } => {
                self.write("local ");
                self.write_punctuated(names, ", ", |p, name| p.write(name.as_str()));
                if !values.is_empty() {
                    self.write(" = ");
                    self.write_punctuated(values, ", ", |p, value| {
                        p.walk_expr(value, 0, Side::None)
                    });
                }
                self.newline();
            }
            Stmt::NumericFor {
                var,
                start,
                end,
                step,
                body,
            } => {
                self.write("for ");
                self.write(var.as_str());
                self.write(" = ");
                self.walk_expr(start, 0, Side::None);
                self.write(", ");
                self.walk_expr(end, 0, Side::None);
                if let Some(step) = step
                    && !matches!(step, Expr::Literal(Literal::Float(1.0)))
                {
                    self.write(", ");
                    self.walk_expr(step, 0, Side::None);
                }
                self.write(" do");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("end");
                self.newline();
            }
            Stmt::Return { values } => {
                self.write("return");
                if !values.is_empty() {
                    self.write(" ");
                    self.write_punctuated(values, ", ", |p, value| {
                        p.walk_expr(value, 0, Side::None)
                    });
                }
                self.newline();
            }
            Stmt::While { condition, body } => {
                self.write("while ");
                self.walk_expr(condition, 0, Side::None);
                self.write(" do");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("end");
                self.newline();
            }
            Stmt::RepeatUntil { condition, body } => {
                self.write("repeat");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("until ");
                self.walk_expr(condition, 0, Side::None);
                self.newline();
            }
        }
    }

    fn walk_if_stmt(&mut self, if_stmt: &If, emit_end: bool) {
        self.write("if ");
        self.walk_expr(&if_stmt.condition, 0, Side::None);
        self.write(" then");
        self.newline();
        self.indent += 1;
        self.walk_block(&if_stmt.then_body);
        self.indent -= 1;
        match &if_stmt.else_clause {
            Some(ElseClause::If(else_if)) => {
                self.write("else");
                self.walk_if_stmt(else_if, false);
            }
            Some(ElseClause::Else(block)) => {
                self.write("else");
                self.newline();
                self.indent += 1;
                self.walk_block(block);
                self.indent -= 1;
            }
            None => {}
        }
        if emit_end {
            self.write("end");
            self.newline();
        }
    }

    fn walk_expr(&mut self, expr: &Expr, parent_prec: u8, side: Side) {
        match expr {
            Expr::Named(name) => self.write(name.as_str()),
            Expr::Binary { lhs, op, rhs } => {
                let prec = op.precedence();
                let assoc = binary_assoc(op);
                let needs_parens = needs_parens(prec, parent_prec, assoc, side);

                if needs_parens {
                    self.write("(");
                }
                self.walk_expr(lhs, prec, Side::Left);
                self.write(" ");
                self.write(op.as_str());
                self.write(" ");
                self.walk_expr(rhs, prec, Side::Right);
                if needs_parens {
                    self.write(")");
                }
            }
            Expr::Unary { op, expr } => {
                let prec = 7;
                let needs_parens = prec < parent_prec;
                if needs_parens {
                    self.write("(");
                }
                self.write(op.as_str());
                if op == &UnOp::Not {
                    self.write(" ");
                }
                self.walk_expr(expr, prec, Side::Right);
                if needs_parens {
                    self.write(")");
                }
            }
            Expr::FunctionCall { func, args } => {
                let prec = 9;
                let needs_parens = prec < parent_prec;
                if needs_parens {
                    self.write("(");
                }
                let func_needs_parens = needs_prefix_wrap(func);
                if func_needs_parens {
                    self.write("(");
                }
                self.walk_expr(func, prec, Side::Left);
                if func_needs_parens {
                    self.write(")");
                }
                self.write("(");
                self.write_punctuated(args, ", ", |p, arg| p.walk_expr(arg, 0, Side::None));
                self.write(")");
                if needs_parens {
                    self.write(")");
                }
            }
            Expr::MethodCall {
                object,
                method,
                args,
            } => {
                let prec = 9;
                let needs_parens = prec < parent_prec;
                if needs_parens {
                    self.write("(");
                }
                let object_needs_parens = needs_prefix_wrap(object);
                if object_needs_parens {
                    self.write("(");
                }
                self.walk_expr(object, prec, Side::Left);
                if object_needs_parens {
                    self.write(")");
                }
                self.write(":");
                self.write(method.as_str());
                self.write("(");
                self.write_punctuated(args, ", ", |p, arg| p.walk_expr(arg, 0, Side::None));
                self.write(")");
                if needs_parens {
                    self.write(")");
                }
            }
            Expr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => {
                let prec = 0;
                let needs_parens = prec < parent_prec;
                if needs_parens {
                    self.write("(");
                }
                self.write("if ");
                self.walk_expr(condition, 0, Side::None);
                self.write(" then ");
                self.walk_expr(then_expr, 0, Side::None);
                self.write(" else ");
                self.walk_expr(else_expr, 0, Side::None);
                if needs_parens {
                    self.write(")");
                }
            }
            Expr::AnonymousFunction { params, body } => {
                let prec = 1;
                let needs_parens = prec < parent_prec;
                if needs_parens {
                    self.write("(");
                }
                self.write("function(");
                self.write_params(params);
                self.write(")");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("end");
                if needs_parens {
                    self.write(")");
                }
            }
            Expr::Field { base, field } => {
                let prec = 9;
                let needs_parens = prec < parent_prec;
                if needs_parens {
                    self.write("(");
                }
                let base_needs_parens = needs_prefix_wrap(base);
                if base_needs_parens {
                    self.write("(");
                }
                self.walk_expr(base, prec, Side::Left);
                if base_needs_parens {
                    self.write(")");
                }
                self.write(".");
                self.write(field.as_str());
                if needs_parens {
                    self.write(")");
                }
            }
            Expr::Index { base, index } => {
                let prec = 9;
                let needs_parens = prec < parent_prec;
                if needs_parens {
                    self.write("(");
                }
                let base_needs_parens = needs_prefix_wrap(base);
                if base_needs_parens {
                    self.write("(");
                }
                self.walk_expr(base, prec, Side::Left);
                if base_needs_parens {
                    self.write(")");
                }
                self.write("[");
                self.walk_expr(index, 0, Side::None);
                self.write("]");
                if needs_parens {
                    self.write(")");
                }
            }
            Expr::Table { items } => self.write_table(items),
            Expr::Vararg => self.write("..."),
            Expr::Literal(lit) => self.write_literal(lit),
        }
    }

    fn write_params(&mut self, params: &[Parameter]) {
        self.write_punctuated(params, ", ", |p, param| match param {
            Parameter::Regular(name) => p.write(name.as_str()),
            Parameter::Vararg => p.write("..."),
        });
    }

    fn write_literal(&mut self, lit: &Literal) {
        match lit {
            Literal::Nil => self.write("nil"),
            Literal::Integer(num) => {
                if *num == i64::MIN {
                    self.write("(-9223372036854775807i - 1i)");
                } else {
                    self.write(&format!("{num}i"));
                }
            }
            Literal::Float(num) => {
                let rendered = if num.is_nan() {
                    "(0/0)".to_string()
                } else if num.is_infinite() {
                    if num.is_sign_positive() {
                        "math.huge".to_string()
                    } else {
                        "-math.huge".to_string()
                    }
                } else {
                    num.to_string()
                };
                self.write(&rendered);
            }
            Literal::String(value) => {
                if should_use_long_string(value)
                    && let Some(level) = long_string_level(value)
                {
                    self.write_long_string(value, level);
                    return;
                }
                self.write("\"");
                self.write(&escape_string(value));
                self.write("\"");
            }
            Literal::Bool(value) => self.write(if *value { "true" } else { "false" }),
        }
    }

    /// Emits a Lua long string literal `[==[value]==]` at the given bracket level.
    ///
    /// Lua/Luau strips the very first newline that immediately follows the
    /// opening bracket.  When the value itself starts with `\n` we emit an
    /// extra one before the content so the round-trip is correct.
    ///
    /// The content and closing bracket are written directly to the output
    /// buffer (bypassing the indent-injecting `write()`) because any
    /// whitespace inside a long string is literal and must not be altered.
    fn write_long_string(&mut self, value: &str, level: usize) {
        let eq = "=".repeat(level);
        // Opening bracket — goes through write() to pick up any pending indent.
        self.write(&format!("[{eq}["));
        // If the value starts with '\n', Lua would strip it on read, so we
        // emit one extra to compensate.
        if value.starts_with('\n') {
            self.out.push('\n');
        }
        // Content goes verbatim; no indentation must be injected.
        self.out.push_str(value);
        // Closing bracket immediately after the last byte of content.
        self.out.push_str(&format!("]{}]", eq));
        // We are no longer at the start of a line.
        self.line_start = false;
    }

    fn write_table(&mut self, items: &[TableItem]) {
        if items.is_empty() {
            self.write("{}");
            return;
        }

        self.write("{");
        self.newline();
        self.indent += 1;
        for (i, item) in items.iter().enumerate() {
            self.write("");
            match item {
                TableItem::Named { name, value } => {
                    self.write(name.as_str());
                    self.write(" = ");
                    self.walk_expr(value, 0, Side::None);
                }
                TableItem::Indexed { index, value } => {
                    self.write("[");
                    self.walk_expr(index, 0, Side::None);
                    self.write("] = ");
                    self.walk_expr(value, 0, Side::None);
                }
                TableItem::Implicit { value } => {
                    self.walk_expr(value, 0, Side::None);
                }
            }
            if i + 1 < items.len() {
                self.write(",");
            }
            self.newline();
        }
        self.indent -= 1;
        self.write("}");
    }

    fn write(&mut self, s: &str) {
        if self.line_start {
            for _ in 0..self.indent {
                self.out.push_str("    ");
            }
            self.line_start = false;
        }
        self.out.push_str(s);
    }

    fn write_punctuated<T>(&mut self, items: &[T], sep: &str, mut f: impl FnMut(&mut Self, &T)) {
        for (i, item) in items.iter().enumerate() {
            if i > 0 {
                self.write(sep);
            }
            f(self, item);
        }
    }

    fn newline(&mut self) {
        self.out.push('\n');
        self.line_start = true;
    }
}

const fn needs_parens(prec: u8, parent_prec: u8, assoc: Assoc, side: Side) -> bool {
    prec < parent_prec
        || (prec == parent_prec
            && matches!(
                (assoc, side),
                (Assoc::Left, Side::Right) | (Assoc::Right, Side::Left)
            ))
}

const fn needs_prefix_wrap(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Literal(_)
            | Expr::Table { .. }
            | Expr::AnonymousFunction { .. }
            | Expr::IfElse { .. }
    )
}

const fn binary_assoc(op: &BinOp) -> Assoc {
    match op {
        BinOp::Concat | BinOp::Pow => Assoc::Right,
        _ => Assoc::Left,
    }
}

/// Returns the length that `escape_string` would produce for `s`, without allocating.
///
/// This mirrors the escaping logic in [`escape_string`] exactly.
fn escaped_len(s: &str) -> usize {
    let mut len = 0;
    for ch in s.chars() {
        let code = u32::from(ch);
        let byte = u8::try_from(code).unwrap_or(b'?');
        len += match byte {
            // Two-character escape sequences
            b'\\' | b'\n' | b'\r' | b'\t' | b'\0' | b'"' => 2,
            // Printable ASCII - emitted verbatim
            0x20..=0x7E => 1,
            // Numeric escapes: `\NNN` where NNN is the decimal byte value
            b => {
                1 + if b < 10 {
                    1
                } else if b < 100 {
                    2
                } else {
                    3
                }
            }
        };
    }
    len
}

/// Returns the minimum long-string bracket level needed to embed `s` as a Lua
/// long string, or `None` if the string cannot be represented as one at all.
fn long_string_level(s: &str) -> Option<usize> {
    if s.contains('\r') || s.contains('\0') {
        return None;
    }

    // probably not the best way to do this
    for level in 0..=16 {
        let closing = format!("]{}]", "=".repeat(level));
        if !s.contains(&closing) {
            return Some(level);
        }
    }

    None
}

/// Returns `true` when emitting `s` as a Lua long string would produce
/// cleaner output than a quoted string with escape sequences.
fn should_use_long_string(s: &str) -> bool {
    if s.contains('\r') || s.contains('\0') || s == "\n" || s == "\t" {
        return false;
    }
    let has_newlines = s.contains('\n');
    let escape_ratio = escaped_len(s) as f64 / s.len().max(1) as f64;
    let long_and_escaped = s.len() > 80 && escape_ratio > 1.2;
    has_newlines || long_and_escaped
}

#[cfg(test)]
mod tests {
    use super::{escape_string, escaped_len, long_string_level, print, should_use_long_string};
    use crate::ast::{Block, Expr, Literal, Stmt};

    #[test]
    fn prints_luau_integer_literals_with_suffix() {
        let block = Block::with_stmts(vec![Stmt::Return {
            values: vec![
                Expr::Literal(Literal::Float(42.0)),
                Expr::Literal(Literal::Integer(42)),
                Expr::Literal(Literal::Integer(-42)),
            ],
        }]);

        assert_eq!(print(&block, &[]), "return 42, 42i, -42i\n");
    }

    #[test]
    fn prints_min_luau_integer_without_overflowing_positive_literal() {
        let block = Block::with_stmts(vec![Stmt::Return {
            values: vec![Expr::Literal(Literal::Integer(i64::MIN))],
        }]);

        assert_eq!(print(&block, &[]), "return (-9223372036854775807i - 1i)\n");
    }

    #[test]
    fn escape_preserves_high_byte_values() {
        let value: String = [b'A', 0x80, 0xFF].into_iter().map(char::from).collect();
        assert_eq!(escape_string(&value), "A\\128\\255");
    }

    #[test]
    fn escaped_len_plain_ascii() {
        assert_eq!(escaped_len("hello"), 5);
    }

    #[test]
    fn escaped_len_special_chars() {
        assert_eq!(escaped_len("\n"), 2);
        assert_eq!(escaped_len("\\"), 2); // single backslash → "\\" (2 chars)
        assert_eq!(escaped_len("\""), 2);
    }

    #[test]
    fn escaped_len_high_bytes() {
        // 0x80 (128) → \128 = 4 chars, 0xFF (255) → \255 = 4 chars.
        let s: String = [0x80u8, 0xFF].into_iter().map(char::from).collect();
        assert_eq!(escaped_len(&s), 8);
    }

    #[test]
    fn long_string_level_plain() {
        assert_eq!(long_string_level("hello world"), Some(0));
    }

    #[test]
    fn long_string_level_contains_level0_close() {
        // `]]` forces level 1; `]=]` is absent so level 1 is sufficient.
        assert_eq!(long_string_level("a]]b"), Some(1));
    }

    #[test]
    fn long_string_level_rejects_cr() {
        assert_eq!(long_string_level("line1\r\nline2"), None);
    }

    #[test]
    fn long_string_level_rejects_null() {
        assert_eq!(long_string_level("has\0null"), None);
    }

    #[test]
    fn should_use_long_string_with_newline() {
        assert!(should_use_long_string("line1\nline2"));
    }

    #[test]
    fn should_use_long_string_plain_short() {
        assert!(!should_use_long_string("hello"));
    }

    #[test]
    fn should_use_long_string_rejects_cr() {
        assert!(!should_use_long_string("line1\r\nline2"));
    }

    #[test]
    fn should_use_long_string_rejects_null() {
        assert!(!should_use_long_string("has\0null"));
    }

    #[test]
    fn should_use_long_string_long_escaped() {
        // A string of 90 tab characters has an escape ratio of 2.0, well above 1.2.
        let s = "\t".repeat(90);
        assert!(should_use_long_string(&s));
    }
}
