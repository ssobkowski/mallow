use crate::{
    ast::{BinOp, Block, Expr, Literal, Parameter, Stmt, TableItem, UnOp},
    common::escape_string,
};

pub fn print(block: &Block) -> String {
    let mut printer = AstPrinter::new();
    printer.walk_block(block);
    printer.finish()
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
                for (i, lv) in lhs.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.walk_expr(lv, 0, Side::None);
                }
                self.write(" = ");
                for (i, rv) in rhs.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.walk_expr(rv, 0, Side::None);
                }
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
            Stmt::Function {
                name,
                params,
                body,
                local,
            } => {
                self.write(if *local {
                    "local function "
                } else {
                    "function "
                });
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
            Stmt::GenericFor { vars, exprs, body } => {
                self.write("for ");
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(var.as_str());
                }
                self.write(" in ");
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.walk_expr(expr, 0, Side::None);
                }
                self.write(" do");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("end");
                self.newline();
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                self.write("if ");
                self.walk_expr(condition, 0, Side::None);
                self.write(" then");
                self.newline();
                self.indent += 1;
                self.walk_block(then_body);
                self.indent -= 1;
                if let Some(else_body) = else_body {
                    self.write("else");
                    self.newline();
                    self.indent += 1;
                    self.walk_block(else_body);
                    self.indent -= 1;
                }
                self.write("end");
                self.newline();
            }
            Stmt::LocalDeclaration { names, values } => {
                self.write("local ");
                for (i, name) in names.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(name.as_str());
                }
                if !values.is_empty() {
                    self.write(" = ");
                    for (i, value) in values.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.walk_expr(value, 0, Side::None);
                    }
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
                if let Some(step) = step {
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
            Stmt::Repeat { body, condition } => {
                self.write("repeat");
                self.newline();
                self.indent += 1;
                self.walk_block(body);
                self.indent -= 1;
                self.write("until ");
                self.walk_expr(condition, 0, Side::None);
                self.newline();
            }
            Stmt::Return { values } => {
                self.write("return");
                if !values.is_empty() {
                    self.write(" ");
                    for (i, value) in values.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.walk_expr(value, 0, Side::None);
                    }
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
                self.write(binary_symbol(op));
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
                self.write(unary_symbol(op));
                if matches!(op, UnOp::Not) {
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
                self.walk_expr(func, prec, Side::Left);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.walk_expr(arg, 0, Side::None);
                }
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
                self.walk_expr(object, prec, Side::Left);
                self.write(":");
                self.write(method.as_str());
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.walk_expr(arg, 0, Side::None);
                }
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
                self.walk_expr(base, prec, Side::Left);
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
                self.walk_expr(base, prec, Side::Left);
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
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            match param {
                Parameter::Regular(name) => self.write(name.as_str()),
                Parameter::Vararg => self.write("..."),
            }
        }
    }

    fn write_literal(&mut self, lit: &Literal) {
        match lit {
            Literal::Nil => self.write("nil"),
            Literal::Number(num) => {
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
                self.write("\"");
                self.write(&escape_string(value));
                self.write("\"");
            }
            Literal::Bool(value) => self.write(if *value { "true" } else { "false" }),
        }
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

    fn newline(&mut self) {
        self.out.push('\n');
        self.line_start = true;
    }
}

fn needs_parens(prec: u8, parent_prec: u8, assoc: Assoc, side: Side) -> bool {
    prec < parent_prec
        || (prec == parent_prec
            && matches!(
                (assoc, side),
                (Assoc::Left, Side::Right) | (Assoc::Right, Side::Left)
            ))
}

fn binary_assoc(op: &BinOp) -> Assoc {
    match op {
        BinOp::Concat | BinOp::Pow => Assoc::Right,
        _ => Assoc::Left,
    }
}

fn binary_symbol(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Pow => "^",
        BinOp::Eq => "==",
        BinOp::Ne => "~=",
        BinOp::Lt => "<",
        BinOp::Lte => "<=",
        BinOp::Gt => ">",
        BinOp::Gte => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Concat => "..",
    }
}

fn unary_symbol(op: &UnOp) -> &'static str {
    match op {
        UnOp::Minus => "-",
        UnOp::Length => "#",
        UnOp::Not => "not",
    }
}

#[cfg(test)]
mod tests {
    use super::escape_string;

    #[test]
    fn escape_preserves_high_byte_values() {
        let value: String = [b'A', 0x80, 0xFF].into_iter().map(char::from).collect();
        assert_eq!(escape_string(&value), "A\\128\\255");
    }
}
