use crate::ast::{
    Block, ElseClause, Expr, If, Literal, Parameter, Stmt, TableItem, Type, TypeLiteral, TypePack,
    TypePackTail, TypePrecedence, Typed,
};
use crate::common::{ByteString, escape_bytes, is_valid_luau_identifier};
use crate::operator::{BinOp, UnOp};

pub fn print(block: &Block) -> String {
    let mut buf = String::new();

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
            Stmt::LocalFunction {
                name,
                params,
                body,
                returns,
            } => {
                self.write("local function ");
                self.write(name.as_str());
                self.write("(");
                self.write_params(params);
                self.write(")");
                if let Some(returns) = returns {
                    self.write(": ");
                    self.write_return_type_pack(returns);
                }
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("end");
                self.newline();
            }
            Stmt::LocalDeclaration { names, values } => {
                self.write("local ");
                self.write_punctuated(names, ", ", |p, decl| {
                    p.write(decl.as_ref().as_str());
                    p.write_type_annotation(decl.ty());
                });
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
            Expr::Parenthesized(expr) => {
                self.write("(");
                self.walk_expr(expr, 0, Side::None);
                self.write(")");
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
                self.write("function");
                self.write("(");
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

    fn write_params(&mut self, params: &[Typed<Parameter>]) {
        self.write_punctuated(params, ", ", |p, param| match param.as_ref() {
            Parameter::Regular(ident) => {
                p.write(ident.as_str());
                p.write_type_annotation(param.ty());
            }
            Parameter::Vararg => {
                p.write("...");
                p.write_type_annotation(param.ty());
            }
        });
    }

    fn write_type(&mut self, ty: &Type, parent_prec: TypePrecedence) {
        let prec = ty.precedence();
        let needs_parens = prec < parent_prec;

        if needs_parens {
            self.write("(");
        }

        match ty {
            Type::Nil => self.write("nil"),
            Type::String => self.write("string"),
            Type::Number => self.write("number"),
            Type::Boolean => self.write("boolean"),
            Type::Table { fields, array } => {
                self.write("{ ");
                let mut wrote = false;
                if let Some(array) = array {
                    let (key, value) = array.as_ref();
                    self.write("[");
                    self.write_type(key, TypePrecedence::Lowest);
                    self.write("]: ");
                    self.write_type(value, TypePrecedence::Lowest);
                    wrote = true;
                }
                let mut fields: Vec<_> = fields.iter().collect();
                fields.sort_unstable_by_key(|(lhs, _)| *lhs);
                for (name, ty) in fields {
                    if wrote {
                        self.write(", ");
                    }
                    self.write_type_field_name(name.as_str());
                    self.write(": ");
                    self.write_type(ty, TypePrecedence::Lowest);
                    wrote = true;
                }
                self.write(" }");
            }
            Type::Function { params, returns } => {
                self.write("(");
                self.write_punctuated(&params.head, ", ", |p, ty| {
                    p.write_type(ty, TypePrecedence::Lowest)
                });
                if let Some(tail) = &params.tail {
                    if !params.head.is_empty() {
                        self.write(", ");
                    }
                    self.write_type_pack_tail(tail);
                }
                self.write(") -> ");
                self.write_return_type_pack(returns);
            }
            Type::Thread => self.write("thread"),
            Type::Userdata => self.write("userdata"),
            Type::Vector => self.write("vector"),
            Type::Integer => self.write("integer"),
            Type::Buffer => self.write("buffer"),
            Type::Unknown => self.write("unknown"),
            Type::Never => self.write("never"),
            Type::Any => self.write("any"),
            Type::Named(name) => self.write(name.as_str()),
            Type::Literal(literal) => self.write_type_literal(literal),
            Type::Union(types) => {
                self.write_punctuated(types, " | ", |p, ty| {
                    p.write_type(ty, TypePrecedence::Union);
                });
            }
            Type::Intersection(types) => {
                self.write_punctuated(types, " & ", |p, ty| {
                    p.write_type(ty, TypePrecedence::Intersection);
                });
            }
            Type::WithMetatable { base, .. } => {
                self.write_type(base, TypePrecedence::Lowest);
            }
        }

        if needs_parens {
            self.write(")");
        }
    }

    /// Writes one table field name in valid Luau type syntax.
    fn write_type_field_name(&mut self, name: &str) {
        if is_valid_luau_identifier(name) {
            self.write(name);
        } else {
            self.write("[\"");
            self.write(&escape_bytes(name.as_bytes()));
            self.write("\"]");
        }
    }

    /// Writes one homogeneous type-pack tail.
    fn write_type_pack_tail(&mut self, tail: &TypePackTail) {
        match tail {
            TypePackTail::Homogeneous(ty) => {
                self.write("...");
                self.write_type(ty, TypePrecedence::Lowest);
            }
        }
    }

    /// Writes a function return pack with the parentheses required by Luau.
    fn write_return_type_pack(&mut self, returns: &TypePack) {
        let return_count = returns.head.len() + usize::from(returns.tail.is_some());
        if return_count == 0 {
            self.write("()");
        } else if return_count > 1 {
            self.write("(");
            self.write_punctuated(&returns.head, ", ", |printer, ty| {
                printer.write_type(ty, TypePrecedence::Lowest);
            });
            if let Some(tail) = &returns.tail {
                if !returns.head.is_empty() {
                    self.write(", ");
                }
                self.write_type_pack_tail(tail);
            }
            self.write(")");
        } else if let Some(ty) = returns.head.first() {
            self.write_type(ty, TypePrecedence::Lowest);
        } else if let Some(tail) = &returns.tail {
            self.write_type_pack_tail(tail);
        }
    }

    fn write_type_literal(&mut self, literal: &TypeLiteral) {
        match literal {
            TypeLiteral::String(value) => {
                self.write("\"");
                self.write(&escape_bytes(value));
                self.write("\"");
            }
            TypeLiteral::Boolean(value) => self.write(if *value { "true" } else { "false" }),
        }
    }

    fn write_type_annotation(&mut self, ty: Option<&Type>) {
        if let Some(ty) = ty {
            self.write(": ");
            self.write_type(ty, TypePrecedence::Lowest);
        }
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
            Literal::String(value) => match choose_string_style(value) {
                StringStyle::Quoted => {
                    self.write("\"");
                    self.write(&escape_bytes(value.as_ref()));
                    self.write("\"");
                }
                StringStyle::Long { level } => {
                    let text = value
                        .as_utf8()
                        .expect("long string style requires valid UTF-8");
                    self.write_long_string(text, level);
                }
            },
            Literal::Bool(value) => self.write(if *value { "true" } else { "false" }),
        }
    }

    fn write_long_string(&mut self, value: &str, level: usize) {
        let eq = "=".repeat(level);
        self.write(&format!("[{eq}["));
        if value.starts_with('\n') {
            self.out.push('\n');
        }
        self.out.push_str(value);
        self.out.push_str(&format!("]{}]", eq));
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

/// Extra style cost for the brackets around a long string.
const LONG_STRING_STYLE_COST: usize = 8;

/// Extra style cost for each escaped newline in a quoted string.
const QUOTED_NEWLINE_STYLE_COST: usize = 8;

/// Source form selected for one runtime string literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringStyle {
    /// A quoted string with byte escapes.
    Quoted,
    /// A long string using the given bracket level.
    Long { level: usize },
}

/// Returns the quoted contents length without allocating the escaped string.
fn escaped_len(bytes: &[u8]) -> usize {
    bytes
        .iter()
        .map(|byte| match byte {
            b'\\' | b'\n' | b'\r' | b'\t' | b'"' => 2,
            0x20..=0x7E => 1,
            _ => 4,
        })
        .sum()
}

/// Returns text when a byte string can be emitted verbatim as a long string.
fn long_string_text(value: &ByteString) -> Option<&str> {
    let text = value.as_utf8()?;
    let safe_controls = value
        .as_ref()
        .iter()
        .all(|byte| matches!(byte, b'\n' | b'\t' | 0x20..=0x7E) || *byte >= 0x80);
    safe_controls.then_some(text)
}

/// Returns the minimum bracket level that does not occur in `text`.
fn long_string_level(text: &str) -> usize {
    for level in 0..=text.len() {
        let closing = format!("]{}]", "=".repeat(level));
        if !text.contains(&closing) {
            return level;
        }
    }

    unreachable!("a delimiter longer than the string cannot occur in it")
}

/// Returns the source length of one long string literal.
fn long_string_len(text: &str, level: usize) -> usize {
    let delimiters = 4 + level * 2;
    let leading_newline = usize::from(text.starts_with('\n'));
    delimiters + leading_newline + text.len()
}

/// Selects the clearer byte-preserving source form for one string.
fn choose_string_style(value: &ByteString) -> StringStyle {
    let Some(text) = long_string_text(value) else {
        return StringStyle::Quoted;
    };

    let level = long_string_level(text);
    let newline_count = value.as_ref().iter().filter(|byte| **byte == b'\n').count();
    let quoted_cost = 2 + escaped_len(value.as_ref()) + newline_count * QUOTED_NEWLINE_STYLE_COST;
    let long_cost = long_string_len(text, level) + LONG_STRING_STYLE_COST;

    if long_cost < quoted_cost {
        StringStyle::Long { level }
    } else {
        StringStyle::Quoted
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{
        AstPrinter, StringStyle, choose_string_style, escape_bytes, escaped_len, long_string_level,
        long_string_text, print,
    };
    use crate::ast::{Block, Expr, Literal, Stmt, Type, TypePack, TypePackTail, TypePrecedence};
    use crate::common::ByteString;

    fn render_type(ty: &Type) -> String {
        let mut printer = AstPrinter::new();
        printer.write_type(ty, TypePrecedence::Lowest);
        printer.finish()
    }

    #[test]
    fn prints_table_type_with_array_descriptor_and_named_fields() {
        let ty = Type::Table {
            fields: HashMap::from([
                ("zeta".into(), Type::Boolean),
                ("alpha".into(), Type::String),
            ]),
            array: Some(Box::new((Type::String, Type::Number))),
        };

        assert_eq!(
            render_type(&ty),
            "{ [string]: number, alpha: string, zeta: boolean }"
        );
    }

    fn unknown_function_type() -> Type {
        Type::Function {
            params: TypePack {
                head: Vec::new(),
                tail: Some(Box::new(TypePackTail::Homogeneous(Type::Unknown))),
            },
            returns: TypePack {
                head: vec![Type::Unknown],
                tail: None,
            },
        }
    }

    /// Invalid table field names use string-key syntax.
    #[test]
    fn prints_invalid_table_type_fields_as_indexed_properties() {
        let ty = Type::Table {
            fields: HashMap::from([
                ("if".into(), Type::String),
                ("1".into(), Type::Number),
                ("key.with.dots".into(), Type::Boolean),
            ]),
            array: None,
        };

        assert_eq!(
            render_type(&ty),
            "{ [\"1\"]: number, [\"if\"]: string, [\"key.with.dots\"]: boolean }"
        );
    }

    #[test]
    fn prints_luau_integer_literals_with_suffix() {
        let block = Block::with_stmts(vec![Stmt::Return {
            values: vec![
                Expr::Literal(Literal::Float(42.0)),
                Expr::Literal(Literal::Integer(42)),
                Expr::Literal(Literal::Integer(-42)),
            ],
        }]);

        assert_eq!(print(&block), "return 42, 42i, -42i\n");
    }

    #[test]
    fn prints_min_luau_integer_without_overflowing_positive_literal() {
        let block = Block::with_stmts(vec![Stmt::Return {
            values: vec![Expr::Literal(Literal::Integer(i64::MIN))],
        }]);

        assert_eq!(print(&block), "return (-9223372036854775807i - 1i)\n");
    }

    #[test]
    fn prints_optional_function_type_with_function_parenthesized() {
        let ty = Type::Union(vec![unknown_function_type(), Type::Nil]);

        assert_eq!(render_type(&ty), "((...unknown) -> unknown) | nil");
    }

    #[test]
    fn prints_function_return_union_without_changing_function_type() {
        let ty = Type::Function {
            params: TypePack::default(),
            returns: TypePack {
                head: vec![Type::Union(vec![Type::Unknown, Type::Nil])],
                tail: None,
            },
        };

        assert_eq!(render_type(&ty), "() -> unknown | nil");
    }

    /// Unions nested in intersections retain the required parentheses.
    #[test]
    fn prints_union_child_of_intersection_parenthesized() {
        let ty = Type::Intersection(vec![
            Type::Union(vec![Type::String, Type::Number]),
            Type::Boolean,
        ]);

        assert_eq!(render_type(&ty), "(string | number) & boolean");
    }

    /// Prints one byte string as a return value.
    fn render_string(value: ByteString) -> String {
        let block = Block::with_stmts(vec![Stmt::Return {
            values: vec![Expr::Literal(Literal::String(value))],
        }]);
        print(&block)
    }

    #[test]
    fn escape_preserves_high_byte_values() {
        assert_eq!(escape_bytes(&[b'A', 0x80, 0xFF]), "A\\128\\255");
    }

    /// Numeric escapes use fixed widths before literal digits.
    #[test]
    fn numeric_escapes_cannot_consume_following_digits() {
        assert_eq!(escape_bytes(&[1, b'2', 0, b'3', 0x80]), "\\0012\\0003\\128");
    }

    #[test]
    fn escaped_len_plain_ascii() {
        assert_eq!(escaped_len(b"hello"), 5);
    }

    #[test]
    fn escaped_len_special_chars() {
        assert_eq!(escaped_len(b"\n"), 2);
        assert_eq!(escaped_len(b"\\"), 2);
        assert_eq!(escaped_len(b"\""), 2);
    }

    #[test]
    fn escaped_len_high_bytes() {
        assert_eq!(escaped_len(&[0x80, 0xFF]), 8);
    }

    #[test]
    fn long_string_level_plain() {
        assert_eq!(long_string_level("hello world"), 0);
    }

    #[test]
    fn long_string_level_skips_used_delimiters() {
        assert_eq!(long_string_level("a]]b]=]c"), 2);
    }

    /// Delimiter selection does not decide whether long syntax is safe.
    #[test]
    fn long_string_level_only_selects_the_delimiter() {
        assert_eq!(long_string_level("line1\r\nline2\0"), 0);
    }

    /// Unsafe source bytes cannot use long syntax.
    #[test]
    fn long_string_text_rejects_changed_or_unsafe_bytes() {
        assert!(long_string_text(&ByteString::from("line1\r\nline2")).is_none());
        assert!(long_string_text(&ByteString::from("has\0null")).is_none());
        assert!(long_string_text(&ByteString::from(vec![0xFF])).is_none());
        assert!(long_string_text(&ByteString::from(vec![1])).is_none());
    }

    /// One short newline does not justify long syntax.
    #[test]
    fn short_single_newline_uses_quoted_style() {
        let value = ByteString::from("x\ny");

        assert_eq!(choose_string_style(&value), StringStyle::Quoted);
        assert_eq!(render_string(value), "return \"x\\ny\"\n");
    }

    /// Text describing escaped source remains quoted.
    #[test]
    fn escaped_source_text_uses_quoted_style() {
        let value = ByteString::from("\"x\\ny\"");

        assert_eq!(choose_string_style(&value), StringStyle::Quoted);
        assert_eq!(render_string(value), "return \"\\\"x\\\\ny\\\"\"\n");
    }

    /// Several lines justify long syntax.
    #[test]
    fn multiline_text_uses_long_style() {
        let value = ByteString::from("alpha\nbeta\ngamma");

        assert_eq!(choose_string_style(&value), StringStyle::Long { level: 0 });
        assert_eq!(render_string(value), "return [[alpha\nbeta\ngamma]]\n");
    }

    /// An extra source newline protects a leading value newline.
    #[test]
    fn leading_newline_is_preserved_in_long_style() {
        let value = ByteString::from("\nalpha\nbeta");

        assert_eq!(choose_string_style(&value), StringStyle::Long { level: 0 });
        assert_eq!(render_string(value), "return [[\n\nalpha\nbeta]]\n");
    }

    /// Short UTF-8 text remains byte-exact when quoted.
    #[test]
    fn short_utf8_text_uses_byte_preserving_quotes() {
        let value = ByteString::from("☺");

        assert_eq!(choose_string_style(&value), StringStyle::Quoted);
        assert_eq!(render_string(value), "return \"\\226\\152\\186\"\n");
    }

    /// Invalid UTF-8 always uses numeric byte escapes.
    #[test]
    fn invalid_utf8_uses_byte_preserving_quotes() {
        let value = ByteString::from(vec![0x80, 0xFF]);

        assert_eq!(choose_string_style(&value), StringStyle::Quoted);
        assert_eq!(render_string(value), "return \"\\128\\255\"\n");
    }

    /// Long text with many escapes benefits from long syntax.
    #[test]
    fn heavily_escaped_text_uses_long_style() {
        let value = ByteString::from("\t".repeat(90));

        assert_eq!(choose_string_style(&value), StringStyle::Long { level: 0 });
    }
}
