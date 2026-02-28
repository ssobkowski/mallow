use crate::ast::{
    BinOp, Block, Expr, Identifier, Literal, Parameter, Stmt, TableConstructorField, UnOp,
};

/// A mutable AST rewriter.
///
/// Override the node-specific methods you care about and call the corresponding
/// `*_default` method to reuse the built-in recursive rewrite for that node.
pub trait AstRewriter {
    fn rewrite_block(&mut self, block: Block) -> Block {
        self.rewrite_block_default(block)
    }

    fn rewrite_stmt(&mut self, stmt: Stmt) -> Vec<Stmt> {
        self.rewrite_stmt_default(stmt)
    }

    fn rewrite_expr(&mut self, expr: Expr) -> Expr {
        self.rewrite_expr_default(expr)
    }

    fn rewrite_table_constructor_field(
        &mut self,
        field: TableConstructorField,
    ) -> TableConstructorField {
        self.rewrite_table_constructor_field_default(field)
    }

    fn rewrite_parameter(&mut self, parameter: Parameter) -> Parameter {
        self.rewrite_parameter_default(parameter)
    }

    fn rewrite_identifier(&mut self, identifier: Identifier) -> Identifier {
        identifier
    }

    fn rewrite_literal(&mut self, literal: Literal) -> Literal {
        literal
    }

    fn rewrite_bin_op(&mut self, op: BinOp) -> BinOp {
        op
    }

    fn rewrite_un_op(&mut self, op: UnOp) -> UnOp {
        op
    }

    fn rewrite_block_default(&mut self, block: Block) -> Block {
        default::rewrite_block(self, block)
    }

    fn rewrite_stmt_default(&mut self, stmt: Stmt) -> Vec<Stmt> {
        default::rewrite_stmt(self, stmt)
    }

    fn rewrite_expr_default(&mut self, expr: Expr) -> Expr {
        default::rewrite_expr(self, expr)
    }

    fn rewrite_table_constructor_field_default(
        &mut self,
        field: TableConstructorField,
    ) -> TableConstructorField {
        default::rewrite_table_constructor_field(self, field)
    }

    fn rewrite_parameter_default(&mut self, parameter: Parameter) -> Parameter {
        default::rewrite_parameter(self, parameter)
    }
}

mod default {
    use crate::ast::{Block, Expr, Parameter, Stmt, TableConstructorField};

    use super::AstRewriter;

    pub(super) fn rewrite_block<R>(rewriter: &mut R, block: Block) -> Block
    where
        R: AstRewriter + ?Sized,
    {
        Block {
            stmts: block
                .stmts
                .into_iter()
                .flat_map(|stmt| rewriter.rewrite_stmt(stmt))
                .collect(),
        }
    }

    pub(super) fn rewrite_stmt<R>(rewriter: &mut R, stmt: Stmt) -> Vec<Stmt>
    where
        R: AstRewriter + ?Sized,
    {
        let stmt = match stmt {
            Stmt::Assignment { lhs, rhs } => Stmt::Assignment {
                lhs: rewriter.rewrite_expr(lhs),
                rhs: rewriter.rewrite_expr(rhs),
            },
            Stmt::Break => Stmt::Break,
            Stmt::Continue => Stmt::Continue,
            Stmt::Do { body } => Stmt::Do {
                body: rewriter.rewrite_block(body),
            },
            Stmt::Expression { expr } => Stmt::Expression {
                expr: rewriter.rewrite_expr(expr),
            },
            Stmt::Function {
                name,
                params,
                body,
                local,
            } => Stmt::Function {
                name: rewriter.rewrite_identifier(name),
                params: params
                    .into_iter()
                    .map(|parameter| rewriter.rewrite_parameter(parameter))
                    .collect(),
                body: rewriter.rewrite_block(body),
                local,
            },
            Stmt::GenericFor { vars, exprs, body } => Stmt::GenericFor {
                vars: vars
                    .into_iter()
                    .map(|identifier| rewriter.rewrite_identifier(identifier))
                    .collect(),
                exprs: exprs
                    .into_iter()
                    .map(|expr| rewriter.rewrite_expr(expr))
                    .collect(),
                body: rewriter.rewrite_block(body),
            },
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => Stmt::If {
                condition: rewriter.rewrite_expr(condition),
                then_body: rewriter.rewrite_block(then_body),
                else_body: else_body.map(|body| rewriter.rewrite_block(body)),
            },
            Stmt::LocalDeclaration { names, values } => Stmt::LocalDeclaration {
                names: names
                    .into_iter()
                    .map(|identifier| rewriter.rewrite_identifier(identifier))
                    .collect(),
                values: values
                    .into_iter()
                    .map(|expr| rewriter.rewrite_expr(expr))
                    .collect(),
            },
            Stmt::NumericFor {
                var,
                start,
                end,
                step,
                body,
            } => Stmt::NumericFor {
                var: rewriter.rewrite_identifier(var),
                start: rewriter.rewrite_expr(start),
                end: rewriter.rewrite_expr(end),
                step: step.map(|expr| rewriter.rewrite_expr(expr)),
                body: rewriter.rewrite_block(body),
            },
            Stmt::Repeat { body, condition } => Stmt::Repeat {
                body: rewriter.rewrite_block(body),
                condition: rewriter.rewrite_expr(condition),
            },
            Stmt::Return { values } => Stmt::Return {
                values: values
                    .into_iter()
                    .map(|expr| rewriter.rewrite_expr(expr))
                    .collect(),
            },
            Stmt::While { condition, body } => Stmt::While {
                condition: rewriter.rewrite_expr(condition),
                body: rewriter.rewrite_block(body),
            },
        };

        vec![stmt]
    }

    pub(super) fn rewrite_expr<R>(rewriter: &mut R, expr: Expr) -> Expr
    where
        R: AstRewriter + ?Sized,
    {
        match expr {
            Expr::Name(identifier) => Expr::Name(rewriter.rewrite_identifier(identifier)),
            Expr::Binary { lhs, op, rhs } => Expr::Binary {
                lhs: Box::new(rewriter.rewrite_expr(*lhs)),
                op: rewriter.rewrite_bin_op(op),
                rhs: Box::new(rewriter.rewrite_expr(*rhs)),
            },
            Expr::Unary { op, expr } => Expr::Unary {
                op: rewriter.rewrite_un_op(op),
                expr: Box::new(rewriter.rewrite_expr(*expr)),
            },
            Expr::FunctionCall { func, args } => Expr::FunctionCall {
                func: Box::new(rewriter.rewrite_expr(*func)),
                args: args
                    .into_iter()
                    .map(|arg| rewriter.rewrite_expr(arg))
                    .collect(),
            },
            Expr::MethodCall {
                object,
                method,
                args,
            } => Expr::MethodCall {
                object: Box::new(rewriter.rewrite_expr(*object)),
                method: rewriter.rewrite_identifier(method),
                args: args
                    .into_iter()
                    .map(|arg| rewriter.rewrite_expr(arg))
                    .collect(),
            },
            Expr::AnonymousFunction { params, body } => Expr::AnonymousFunction {
                params: params
                    .into_iter()
                    .map(|parameter| rewriter.rewrite_parameter(parameter))
                    .collect(),
                body: rewriter.rewrite_block(body),
            },
            Expr::Field { base, field } => Expr::Field {
                base: Box::new(rewriter.rewrite_expr(*base)),
                field: rewriter.rewrite_identifier(field),
            },
            Expr::Index { base, index } => Expr::Index {
                base: Box::new(rewriter.rewrite_expr(*base)),
                index: Box::new(rewriter.rewrite_expr(*index)),
            },
            Expr::Table { fields } => Expr::Table {
                fields: fields
                    .into_iter()
                    .map(|field| rewriter.rewrite_table_constructor_field(field))
                    .collect(),
            },
            Expr::Vararg => Expr::Vararg,
            Expr::Literal(literal) => Expr::Literal(rewriter.rewrite_literal(literal)),
        }
    }

    pub(super) fn rewrite_table_constructor_field<R>(
        rewriter: &mut R,
        field: TableConstructorField,
    ) -> TableConstructorField
    where
        R: AstRewriter + ?Sized,
    {
        match field {
            TableConstructorField::Named { name, value } => TableConstructorField::Named {
                name: rewriter.rewrite_identifier(name),
                value: rewriter.rewrite_expr(value),
            },
            TableConstructorField::Indexed { index, value } => TableConstructorField::Indexed {
                index: rewriter.rewrite_expr(index),
                value: rewriter.rewrite_expr(value),
            },
            TableConstructorField::Implicit { value } => TableConstructorField::Implicit {
                value: rewriter.rewrite_expr(value),
            },
        }
    }

    pub(super) fn rewrite_parameter<R>(rewriter: &mut R, parameter: Parameter) -> Parameter
    where
        R: AstRewriter + ?Sized,
    {
        match parameter {
            Parameter::Regular(identifier) => {
                Parameter::Regular(rewriter.rewrite_identifier(identifier))
            }
            Parameter::Vararg => Parameter::Vararg,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::AstRewriter;
    use crate::ast::{
        BinOp, Block, Expr, Identifier, Literal, Parameter, Stmt, TableConstructorField,
    };

    struct RenameFoo;

    impl AstRewriter for RenameFoo {
        fn rewrite_identifier(&mut self, identifier: Identifier) -> Identifier {
            if identifier.as_str() == "foo" {
                Identifier::from("bar")
            } else {
                identifier
            }
        }
    }

    #[test]
    fn rewrites_identifiers_through_default_recursion() {
        let block = Block::with_stmts(vec![
            Stmt::Function {
                name: Identifier::from("foo"),
                params: vec![Parameter::Regular(Identifier::from("foo"))],
                body: Block::with_stmts(vec![
                    Stmt::LocalDeclaration {
                        names: vec![Identifier::from("foo")],
                        values: vec![Expr::Name(Identifier::from("foo"))],
                    },
                    Stmt::Expression {
                        expr: Expr::Table {
                            fields: vec![
                                TableConstructorField::Named {
                                    name: Identifier::from("foo"),
                                    value: Expr::Name(Identifier::from("foo")),
                                },
                                TableConstructorField::Indexed {
                                    index: Expr::Name(Identifier::from("foo")),
                                    value: Expr::Binary {
                                        lhs: Box::new(Expr::Name(Identifier::from("foo"))),
                                        op: BinOp::Add,
                                        rhs: Box::new(Expr::Literal(Literal::Number(1.0))),
                                    },
                                },
                            ],
                        },
                    },
                ]),
                local: true,
            },
            Stmt::Return {
                values: vec![Expr::AnonymousFunction {
                    params: vec![Parameter::Regular(Identifier::from("foo"))],
                    body: Block::with_stmts(vec![Stmt::Return {
                        values: vec![Expr::Name(Identifier::from("foo"))],
                    }]),
                }],
            },
        ]);

        let block = RenameFoo.rewrite_block(block);

        let debug = format!("{block:#?}");
        assert!(!debug.contains("foo"));
        assert!(debug.contains("bar"));
    }

    #[test]
    fn statements_can_be_removed_or_expanded() {
        struct StripReturns;

        impl AstRewriter for StripReturns {
            fn rewrite_stmt(&mut self, stmt: Stmt) -> Vec<Stmt> {
                match stmt {
                    Stmt::Return { .. } => Vec::new(),
                    other => self.rewrite_stmt_default(other),
                }
            }
        }

        let block = Block::with_stmts(vec![
            Stmt::Expression {
                expr: Expr::Literal(Literal::Bool(true)),
            },
            Stmt::Return {
                values: vec![Expr::Literal(Literal::Number(1.0))],
            },
        ]);

        let block = StripReturns.rewrite_block(block);

        assert_eq!(block.stmts.len(), 1);
        assert!(matches!(block.stmts[0], Stmt::Expression { .. }));
    }

    #[test]
    fn overrides_can_delegate_to_default_expr_rewrite() {
        struct WrapAdds;

        impl AstRewriter for WrapAdds {
            fn rewrite_expr(&mut self, expr: Expr) -> Expr {
                match expr {
                    Expr::Binary {
                        lhs,
                        op: BinOp::Add,
                        rhs,
                    } => Expr::FunctionCall {
                        func: Box::new(Expr::Name(Identifier::from("sum"))),
                        args: vec![self.rewrite_expr(*lhs), self.rewrite_expr(*rhs)],
                    },
                    other => self.rewrite_expr_default(other),
                }
            }
        }

        let expr = Expr::Binary {
            lhs: Box::new(Expr::Name(Identifier::from("a"))),
            op: BinOp::Mul,
            rhs: Box::new(Expr::Binary {
                lhs: Box::new(Expr::Name(Identifier::from("b"))),
                op: BinOp::Add,
                rhs: Box::new(Expr::Name(Identifier::from("c"))),
            }),
        };

        let expr = WrapAdds.rewrite_expr(expr);

        assert_eq!(
            expr,
            Expr::Binary {
                lhs: Box::new(Expr::Name(Identifier::from("a"))),
                op: BinOp::Mul,
                rhs: Box::new(Expr::FunctionCall {
                    func: Box::new(Expr::Name(Identifier::from("sum"))),
                    args: vec![
                        Expr::Name(Identifier::from("b")),
                        Expr::Name(Identifier::from("c")),
                    ],
                }),
            }
        );
    }
}
