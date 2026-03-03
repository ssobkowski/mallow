use super::walker::AstRewriter;
use crate::{
    ast::{Block, Expr, Identifier, Stmt},
    scopes::ScopeManager,
};
use std::collections::HashSet;

pub(super) struct Inliner {
    scopes: ScopeManager,
}

impl Inliner {
    pub fn new() -> Self {
        Self {
            scopes: ScopeManager::new(),
        }
    }

    fn rewrite_name(&mut self, name: Identifier) -> Expr {
        match self.scopes.get_var(&name).and_then(|var| var.value.clone()) {
            Some(Expr::Name(alias)) if alias != name => Expr::Name(alias),
            Some(expr) => expr,
            None => Expr::Name(name),
        }
    }

    fn rewrite_lvalue(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Name(name) => Expr::Name(name),
            Expr::Field { base, field } => Expr::Field {
                base: Box::new(self.rewrite_expr(*base)),
                field,
            },
            Expr::Index { base, index } => Expr::Index {
                base: Box::new(self.rewrite_expr(*base)),
                index: Box::new(self.rewrite_expr(*index)),
            },
            other => self.rewrite_expr_default(other),
        }
    }

    fn record_local_declaration(&mut self, names: &[Identifier], values: &[Expr]) {
        let scope = self
            .scopes
            .top_scope_mut()
            .expect("inliner requires an active scope");

        for (index, name) in names.iter().enumerate() {
            let value = values.get(index).cloned().filter(is_inlineable_expr);
            scope.update_var(crate::scopes::Var::new(name.clone(), value));
        }
    }

    fn record_assignment(&mut self, lhs: &Expr, _rhs: &Expr) {
        self.kill_written_names_in_expr(lhs);

        if let Expr::Name(name) = lhs {
            let value = _rhs.clone();
            if is_inlineable_expr(&value) {
                self.scopes
                    .update_var(crate::scopes::Var::new(name.clone(), Some(value)));
            }
        }
    }

    fn kill_written_names_in_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Name(name) => {
                self.scopes.kill_var(name);
                self.scopes.invalidate_references_to(name);
            }
            Expr::Field { .. } => {}
            Expr::Index { .. } => {}
            Expr::Binary { lhs, rhs, .. } => {
                self.kill_written_names_in_expr(lhs);
                self.kill_written_names_in_expr(rhs);
            }
            Expr::Unary { expr, .. } => self.kill_written_names_in_expr(expr),
            Expr::FunctionCall { .. }
            | Expr::MethodCall { .. }
            | Expr::AnonymousFunction { .. }
            | Expr::Table { .. }
            | Expr::Vararg
            | Expr::Literal(_) => {}
        }
    }

    fn remove_dead_local_declarations(&self, block: Block) -> Block {
        let local_names = collect_local_names(&block);
        let mut live_values = HashSet::new();
        let mut needed_bindings = HashSet::new();
        let mut kept_stmts = Vec::with_capacity(block.stmts.len());

        for stmt in block.stmts.into_iter().rev() {
            match stmt {
                Stmt::LocalDeclaration { names, values } => {
                    let rewritten = rewrite_local_declaration_liveness(
                        names,
                        values,
                        &mut live_values,
                        &mut needed_bindings,
                    );
                    kept_stmts.extend(rewritten.into_iter().rev());
                }
                Stmt::Assignment { lhs, rhs } => {
                    if can_drop_dead_assignment(&lhs, &rhs, &live_values, &local_names) {
                        kill_written_names(&lhs, &mut live_values);
                        continue;
                    }

                    mark_written_names(&lhs, &mut needed_bindings);
                    kill_written_names(&lhs, &mut live_values);
                    collect_lvalue_reads(&lhs, &mut live_values);
                    collect_lvalue_reads(&lhs, &mut needed_bindings);
                    collect_expr_reads(&rhs, &mut live_values);
                    collect_expr_reads(&rhs, &mut needed_bindings);
                    kept_stmts.push(Stmt::Assignment { lhs, rhs });
                }
                other => {
                    collect_stmt_reads(&other, &mut live_values);
                    collect_stmt_reads(&other, &mut needed_bindings);
                    kept_stmts.push(other);
                }
            }
        }

        kept_stmts.reverse();
        Block { stmts: kept_stmts }
    }
}

impl AstRewriter for Inliner {
    fn rewrite_block(&mut self, block: Block) -> Block {
        self.scopes.push_scope();

        let stmts = block
            .stmts
            .into_iter()
            .flat_map(|stmt| self.rewrite_stmt(stmt))
            .collect();

        self.scopes.pop_scope();

        self.remove_dead_local_declarations(Block { stmts })
    }

    fn rewrite_stmt(&mut self, stmt: Stmt) -> Vec<Stmt> {
        match stmt {
            Stmt::LocalDeclaration { names, values } => {
                let values = values
                    .into_iter()
                    .map(|value| self.rewrite_expr(value))
                    .collect::<Vec<_>>();

                self.record_local_declaration(&names, &values);

                vec![Stmt::LocalDeclaration { names, values }]
            }

            Stmt::Assignment { lhs, rhs } => {
                let lhs = self.rewrite_lvalue(lhs);
                let rhs = self.rewrite_expr(rhs);

                self.record_assignment(&lhs, &rhs);

                vec![Stmt::Assignment { lhs, rhs }]
            }

            other => self.rewrite_stmt_default(other),
        }
    }

    fn rewrite_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Name(name) => self.rewrite_name(name),
            other => self.rewrite_expr_default(other),
        }
    }
}

fn is_inlineable_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Name(_) | Expr::Literal(_))
}

fn is_dead_declaration_value(expr: &Expr) -> bool {
    is_inlineable_expr(expr)
}

fn can_drop_dead_assignment(
    lhs: &Expr,
    rhs: &Expr,
    live_values: &HashSet<Identifier>,
    local_names: &HashSet<Identifier>,
) -> bool {
    match lhs {
        Expr::Name(name) => {
            local_names.contains(name) && !live_values.contains(name) && is_inlineable_expr(rhs)
        }
        _ => false,
    }
}

fn rewrite_local_declaration_liveness(
    names: Vec<Identifier>,
    values: Vec<Expr>,
    live_values: &mut HashSet<Identifier>,
    needed_bindings: &mut HashSet<Identifier>,
) -> Vec<Stmt> {
    if values.iter().any(|expr| !is_dead_declaration_value(expr)) {
        for name in &names {
            live_values.remove(name);
            needed_bindings.remove(name);
        }
        for value in &values {
            collect_expr_reads(value, live_values);
            collect_expr_reads(value, needed_bindings);
        }
        return vec![Stmt::LocalDeclaration { names, values }];
    }

    let mut kept = Vec::new();

    for (index, name) in names.into_iter().enumerate() {
        let value_live = live_values.remove(&name);
        let binding_needed = needed_bindings.remove(&name);
        let value = values.get(index).cloned();

        if !binding_needed {
            continue;
        }

        if value_live {
            if let Some(value) = value.clone() {
                collect_expr_reads(&value, live_values);
                collect_expr_reads(&value, needed_bindings);
                kept.push(Stmt::LocalDeclaration {
                    names: vec![name],
                    values: vec![value],
                });
            } else {
                kept.push(Stmt::LocalDeclaration {
                    names: vec![name],
                    values: Vec::new(),
                });
            }
        } else {
            if let Some(value) = value {
                debug_assert!(is_dead_declaration_value(&value));
            }
            kept.push(Stmt::LocalDeclaration {
                names: vec![name],
                values: Vec::new(),
            });
        }
    }

    kept
}

fn collect_local_names(block: &Block) -> HashSet<Identifier> {
    let mut names = HashSet::new();
    for stmt in block.stmts() {
        if let Stmt::LocalDeclaration {
            names: local_names, ..
        } = stmt
        {
            names.extend(local_names.iter().cloned());
        }
    }
    names
}

fn collect_stmt_reads(stmt: &Stmt, reads: &mut HashSet<Identifier>) {
    match stmt {
        Stmt::Assignment { lhs, rhs } => {
            collect_lvalue_reads(lhs, reads);
            collect_expr_reads(rhs, reads);
        }
        Stmt::Break | Stmt::Continue => {}
        Stmt::Do { body } => collect_block_reads_into(body, reads),
        Stmt::Expression { expr } => collect_expr_reads(expr, reads),
        Stmt::Function { body, .. } => collect_block_reads_into(body, reads),
        Stmt::GenericFor { exprs, body, .. } => {
            for expr in exprs {
                collect_expr_reads(expr, reads);
            }
            collect_block_reads_into(body, reads);
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
        } => {
            collect_expr_reads(condition, reads);
            collect_block_reads_into(then_body, reads);
            if let Some(else_body) = else_body {
                collect_block_reads_into(else_body, reads);
            }
        }
        Stmt::LocalDeclaration { values, .. } => {
            for value in values {
                collect_expr_reads(value, reads);
            }
        }
        Stmt::NumericFor {
            start,
            end,
            step,
            body,
            ..
        } => {
            collect_expr_reads(start, reads);
            collect_expr_reads(end, reads);
            if let Some(step) = step {
                collect_expr_reads(step, reads);
            }
            collect_block_reads_into(body, reads);
        }
        Stmt::Repeat { body, condition } => {
            collect_block_reads_into(body, reads);
            collect_expr_reads(condition, reads);
        }
        Stmt::Return { values } => {
            for value in values {
                collect_expr_reads(value, reads);
            }
        }
        Stmt::While { condition, body } => {
            collect_expr_reads(condition, reads);
            collect_block_reads_into(body, reads);
        }
    }
}

fn collect_block_reads_into(block: &Block, reads: &mut HashSet<Identifier>) {
    for stmt in block.stmts() {
        collect_stmt_reads(stmt, reads);
    }
}

fn kill_written_names(expr: &Expr, reads: &mut HashSet<Identifier>) {
    match expr {
        Expr::Name(name) => {
            reads.remove(name);
        }
        Expr::Binary { lhs, rhs, .. } => {
            kill_written_names(lhs, reads);
            kill_written_names(rhs, reads);
        }
        Expr::Unary { expr, .. } => kill_written_names(expr, reads),
        _ => {}
    }
}

fn mark_written_names(expr: &Expr, reads: &mut HashSet<Identifier>) {
    match expr {
        Expr::Name(name) => {
            reads.insert(name.clone());
        }
        Expr::Binary { lhs, rhs, .. } => {
            mark_written_names(lhs, reads);
            mark_written_names(rhs, reads);
        }
        Expr::Unary { expr, .. } => mark_written_names(expr, reads),
        _ => {}
    }
}

fn collect_lvalue_reads(expr: &Expr, reads: &mut HashSet<Identifier>) {
    match expr {
        Expr::Name(_) => {}
        Expr::Field { base, .. } => collect_expr_reads(base, reads),
        Expr::Index { base, index } => {
            collect_expr_reads(base, reads);
            collect_expr_reads(index, reads);
        }
        other => collect_expr_reads(other, reads),
    }
}

fn collect_expr_reads(expr: &Expr, reads: &mut HashSet<Identifier>) {
    match expr {
        Expr::Name(name) => {
            reads.insert(name.clone());
        }
        Expr::Binary { lhs, rhs, .. } => {
            collect_expr_reads(lhs, reads);
            collect_expr_reads(rhs, reads);
        }
        Expr::Unary { expr, .. } => collect_expr_reads(expr, reads),
        Expr::FunctionCall { func, args } => {
            collect_expr_reads(func, reads);
            for arg in args {
                collect_expr_reads(arg, reads);
            }
        }
        Expr::MethodCall { object, args, .. } => {
            collect_expr_reads(object, reads);
            for arg in args {
                collect_expr_reads(arg, reads);
            }
        }
        Expr::AnonymousFunction { body, .. } => collect_block_reads_into(body, reads),
        Expr::Field { base, .. } => collect_expr_reads(base, reads),
        Expr::Index { base, index } => {
            collect_expr_reads(base, reads);
            collect_expr_reads(index, reads);
        }
        Expr::Table { fields } => {
            for field in fields {
                match field {
                    crate::ast::TableConstructorField::Named { value, .. } => {
                        collect_expr_reads(value, reads);
                    }
                    crate::ast::TableConstructorField::Indexed { index, value } => {
                        collect_expr_reads(index, reads);
                        collect_expr_reads(value, reads);
                    }
                    crate::ast::TableConstructorField::Implicit { value } => {
                        collect_expr_reads(value, reads);
                    }
                }
            }
        }
        Expr::Vararg | Expr::Literal(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::Inliner;
    use crate::{
        ast::{Block, Expr, Identifier, Literal, Stmt},
        passes::walker::AstRewriter,
    };

    #[test]
    fn rewrites_local_alias_uses() {
        let block = Block::with_stmts(vec![
            Stmt::LocalDeclaration {
                names: vec![Identifier::from("a")],
                values: vec![Expr::Name(Identifier::from("b"))],
            },
            Stmt::Return {
                values: vec![Expr::Name(Identifier::from("a"))],
            },
        ]);

        let rewritten = Inliner::new().rewrite_block(block);

        assert_eq!(
            rewritten,
            Block::with_stmts(vec![Stmt::Return {
                values: vec![Expr::Name(Identifier::from("b"))],
            }])
        );
    }

    #[test]
    fn assignment_invalidates_alias() {
        let block = Block::with_stmts(vec![
            Stmt::LocalDeclaration {
                names: vec![Identifier::from("a")],
                values: vec![Expr::Name(Identifier::from("b"))],
            },
            Stmt::Assignment {
                lhs: Expr::Name(Identifier::from("a")),
                rhs: Expr::Literal(Literal::Number(1.0)),
            },
            Stmt::Return {
                values: vec![Expr::Name(Identifier::from("a"))],
            },
        ]);

        let rewritten = Inliner::new().rewrite_block(block);

        assert_eq!(
            rewritten,
            Block::with_stmts(vec![Stmt::Return {
                values: vec![Expr::Literal(Literal::Number(1.0))],
            }])
        );
    }

    #[test]
    fn nested_blocks_do_not_leak_aliases() {
        let block = Block::with_stmts(vec![
            Stmt::Do {
                body: Block::with_stmts(vec![
                    Stmt::LocalDeclaration {
                        names: vec![Identifier::from("a")],
                        values: vec![Expr::Name(Identifier::from("b"))],
                    },
                    Stmt::Return {
                        values: vec![Expr::Name(Identifier::from("a"))],
                    },
                ]),
            },
            Stmt::Return {
                values: vec![Expr::Name(Identifier::from("a"))],
            },
        ]);

        let rewritten = Inliner::new().rewrite_block(block);

        assert_eq!(
            rewritten,
            Block::with_stmts(vec![
                Stmt::Do {
                    body: Block::with_stmts(vec![Stmt::Return {
                        values: vec![Expr::Name(Identifier::from("b"))],
                    },]),
                },
                Stmt::Return {
                    values: vec![Expr::Name(Identifier::from("a"))],
                },
            ])
        );
    }

    #[test]
    fn rewrites_literals_and_removes_dead_temp_locals() {
        let block = Block::with_stmts(vec![
            Stmt::LocalDeclaration {
                names: vec![Identifier::from("v1")],
                values: vec![Expr::Name(Identifier::from("print"))],
            },
            Stmt::LocalDeclaration {
                names: vec![Identifier::from("v2")],
                values: vec![Expr::Name(Identifier::from("v0"))],
            },
            Stmt::LocalDeclaration {
                names: vec![Identifier::from("v3")],
                values: vec![Expr::Literal(Literal::Number(21.0))],
            },
            Stmt::Expression {
                expr: Expr::FunctionCall {
                    func: Box::new(Expr::Name(Identifier::from("print"))),
                    args: vec![Expr::FunctionCall {
                        func: Box::new(Expr::Name(Identifier::from("v2"))),
                        args: vec![Expr::Name(Identifier::from("v3"))],
                    }],
                },
            },
        ]);

        let rewritten = Inliner::new().rewrite_block(block);

        assert_eq!(
            rewritten,
            Block::with_stmts(vec![Stmt::Expression {
                expr: Expr::FunctionCall {
                    func: Box::new(Expr::Name(Identifier::from("print"))),
                    args: vec![Expr::FunctionCall {
                        func: Box::new(Expr::Name(Identifier::from("v0"))),
                        args: vec![Expr::Literal(Literal::Number(21.0))],
                    }],
                },
            }])
        );
    }

    #[test]
    fn source_assignment_invalidates_alias_uses() {
        let block = Block::with_stmts(vec![
            Stmt::LocalDeclaration {
                names: vec![Identifier::from("a")],
                values: vec![Expr::Name(Identifier::from("b"))],
            },
            Stmt::Assignment {
                lhs: Expr::Name(Identifier::from("b")),
                rhs: Expr::Literal(Literal::Number(1.0)),
            },
            Stmt::Return {
                values: vec![Expr::Name(Identifier::from("a"))],
            },
        ]);

        let rewritten = Inliner::new().rewrite_block(block);

        assert_eq!(
            rewritten,
            Block::with_stmts(vec![
                Stmt::LocalDeclaration {
                    names: vec![Identifier::from("a")],
                    values: vec![Expr::Name(Identifier::from("b"))],
                },
                Stmt::Assignment {
                    lhs: Expr::Name(Identifier::from("b")),
                    rhs: Expr::Literal(Literal::Number(1.0)),
                },
                Stmt::Return {
                    values: vec![Expr::Name(Identifier::from("a"))],
                },
            ])
        );
    }

    #[test]
    fn keeps_local_binding_when_initializer_is_dead_but_assignment_remains() {
        let block = Block::with_stmts(vec![
            Stmt::LocalDeclaration {
                names: vec![Identifier::from("v2")],
                values: vec![Expr::Name(Identifier::from("v0"))],
            },
            Stmt::Assignment {
                lhs: Expr::Name(Identifier::from("v2")),
                rhs: Expr::FunctionCall {
                    func: Box::new(Expr::Name(Identifier::from("v0"))),
                    args: vec![Expr::Literal(Literal::Number(1.0))],
                },
            },
            Stmt::Return {
                values: vec![Expr::Name(Identifier::from("v2"))],
            },
        ]);

        let rewritten = Inliner::new().rewrite_block(block);

        assert_eq!(
            rewritten,
            Block::with_stmts(vec![
                Stmt::LocalDeclaration {
                    names: vec![Identifier::from("v2")],
                    values: Vec::new(),
                },
                Stmt::Assignment {
                    lhs: Expr::Name(Identifier::from("v2")),
                    rhs: Expr::FunctionCall {
                        func: Box::new(Expr::Name(Identifier::from("v0"))),
                        args: vec![Expr::Literal(Literal::Number(1.0))],
                    },
                },
                Stmt::Return {
                    values: vec![Expr::Name(Identifier::from("v2"))],
                },
            ])
        );
    }

    #[test]
    fn assignment_aliases_are_rewritten_and_dead_store_is_removed() {
        let block = Block::with_stmts(vec![
            Stmt::LocalDeclaration {
                names: vec![Identifier::from("v3")],
                values: vec![Expr::Literal(Literal::Number(1.0))],
            },
            Stmt::Assignment {
                lhs: Expr::Name(Identifier::from("v3")),
                rhs: Expr::Name(Identifier::from("v0")),
            },
            Stmt::Expression {
                expr: Expr::FunctionCall {
                    func: Box::new(Expr::Name(Identifier::from("v3"))),
                    args: vec![Expr::Literal(Literal::Number(2.0))],
                },
            },
        ]);

        let rewritten = Inliner::new().rewrite_block(block);

        assert_eq!(
            rewritten,
            Block::with_stmts(vec![Stmt::Expression {
                expr: Expr::FunctionCall {
                    func: Box::new(Expr::Name(Identifier::from("v0"))),
                    args: vec![Expr::Literal(Literal::Number(2.0))],
                },
            }])
        );
    }
}
