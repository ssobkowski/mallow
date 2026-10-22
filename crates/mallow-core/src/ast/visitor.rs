use super::{
    Block, ElseClause, Expr, Identifier, If, Parameter, Stmt, TableItem, TemplatePart, Typed,
};

/// Visits and may change an AST.
///
/// Names are split by syntactic role: bindings introduce a local, references read or
/// write a variable. Field, method, and table-key names are not variables and are
/// never visited.
pub(crate) trait VisitorMut {
    /// Visits one block.
    fn visit_block(&mut self, block: &mut Block) {
        walk_block(self, block);
    }

    /// Visits one statement.
    fn visit_stmt(&mut self, stmt: &mut Stmt) {
        walk_stmt(self, stmt);
    }

    /// Visits one expression.
    fn visit_expr(&mut self, expr: &mut Expr) {
        walk_expr(self, expr);
    }

    /// Visits a name introduced by a local declaration, parameter, or loop variable.
    fn visit_binding(&mut self, _name: &mut Identifier) {}

    /// Visits a name used as a variable, which may be a local or a global.
    fn visit_reference(&mut self, _name: &mut Identifier) {}
}

/// Walks every statement of one block.
pub(crate) fn walk_block<V: VisitorMut + ?Sized>(visitor: &mut V, block: &mut Block) {
    for stmt in &mut block.stmts {
        visitor.visit_stmt(stmt);
    }
}

/// Walks the children of one statement in evaluation order.
pub(crate) fn walk_stmt<V: VisitorMut + ?Sized>(visitor: &mut V, stmt: &mut Stmt) {
    match stmt {
        Stmt::Assignment { lhs, rhs } => {
            walk_exprs(visitor, rhs);
            walk_exprs(visitor, lhs);
        }
        Stmt::Break | Stmt::Continue | Stmt::Comment { .. } => {}
        Stmt::CompoundAssignment { lhs, rhs, .. } => {
            visitor.visit_expr(rhs);
            visitor.visit_expr(lhs);
        }
        Stmt::Do { body } => visitor.visit_block(body),
        Stmt::Expression { expr } => visitor.visit_expr(expr),
        Stmt::GenericFor { vars, exprs, body } => {
            walk_exprs(visitor, exprs);
            for var in vars {
                visitor.visit_binding(var);
            }
            visitor.visit_block(body);
        }
        Stmt::If(if_stmt) => walk_if(visitor, if_stmt),
        Stmt::LocalFunction { name, params, body } => {
            visitor.visit_binding(name);
            walk_params(visitor, params);
            visitor.visit_block(body);
        }
        Stmt::LocalDeclaration { names, values } => {
            walk_exprs(visitor, values);
            for name in names {
                visitor.visit_binding(name.as_mut());
            }
        }
        Stmt::NumericFor {
            var,
            start,
            end,
            step,
            body,
        } => {
            visitor.visit_expr(start);
            visitor.visit_expr(end);
            if let Some(step) = step {
                visitor.visit_expr(step);
            }
            visitor.visit_binding(var);
            visitor.visit_block(body);
        }
        Stmt::Return { values } => walk_exprs(visitor, values),
        Stmt::While { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_block(body);
        }
        Stmt::RepeatUntil { condition, body } => {
            visitor.visit_block(body);
            visitor.visit_expr(condition);
        }
    }
}

/// Walks one if statement and its else chain.
fn walk_if<V: VisitorMut + ?Sized>(visitor: &mut V, if_stmt: &mut If) {
    visitor.visit_expr(&mut if_stmt.condition);
    visitor.visit_block(&mut if_stmt.then_body);
    match &mut if_stmt.else_clause {
        Some(ElseClause::If(nested)) => walk_if(visitor, nested),
        Some(ElseClause::Else(body)) => visitor.visit_block(body),
        None => {}
    }
}

/// Walks the children of one expression.
pub(crate) fn walk_expr<V: VisitorMut + ?Sized>(visitor: &mut V, expr: &mut Expr) {
    match expr {
        Expr::Named(name) => visitor.visit_reference(name),
        Expr::Binary { lhs, rhs, .. } => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        Expr::Unary { expr, .. } | Expr::Parenthesized(expr) => visitor.visit_expr(expr),
        Expr::FunctionCall { func, args } => {
            visitor.visit_expr(func);
            walk_exprs(visitor, args);
        }
        Expr::MethodCall { object, args, .. } => {
            visitor.visit_expr(object);
            walk_exprs(visitor, args);
        }
        Expr::IfElse {
            condition,
            then_expr,
            else_expr,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_expr(then_expr);
            visitor.visit_expr(else_expr);
        }
        Expr::AnonymousFunction { params, body } => {
            walk_params(visitor, params);
            visitor.visit_block(body);
        }
        Expr::Field { base, .. } => visitor.visit_expr(base),
        Expr::Index { base, index } => {
            visitor.visit_expr(base);
            visitor.visit_expr(index);
        }
        Expr::Table { items } => {
            for item in items {
                match item {
                    TableItem::Named { value, .. } | TableItem::Implicit { value } => {
                        visitor.visit_expr(value);
                    }
                    TableItem::Indexed { index, value } => {
                        visitor.visit_expr(index);
                        visitor.visit_expr(value);
                    }
                }
            }
        }
        Expr::Interpolation(parts) => {
            for part in parts {
                if let TemplatePart::Value(value) = part {
                    visitor.visit_expr(value);
                }
            }
        }
        Expr::Vararg | Expr::Literal(_) => {}
    }
}

/// Walks a list of expressions in order.
fn walk_exprs<V: VisitorMut + ?Sized>(visitor: &mut V, exprs: &mut [Expr]) {
    for expr in exprs {
        visitor.visit_expr(expr);
    }
}

/// Walks the named parameters of one function.
fn walk_params<V: VisitorMut + ?Sized>(visitor: &mut V, params: &mut [Typed<Parameter>]) {
    for param in params {
        if let Parameter::Regular(name) = param.as_mut() {
            visitor.visit_binding(name);
        }
    }
}
