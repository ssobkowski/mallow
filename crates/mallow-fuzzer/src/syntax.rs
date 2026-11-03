//! Constructors for AST shapes that span several nodes.

use mallow_core::ast::{Block, Expr, Identifier, If, Parameter, Stmt, Typed};

/// Calls a dotted global path such as `["math", "min"]`.
pub fn library_call(path: &[&str], args: Vec<Expr>) -> Expr {
    let (first, rest) = path.split_first().expect("a path has at least one part");
    let func = rest
        .iter()
        .fold(Expr::named(*first), |base, part| Expr::Field {
            base: Box::new(base),
            field: Identifier::new(*part),
        });
    Expr::call(func, args)
}

pub fn print(args: Vec<Expr>) -> Stmt {
    Stmt::Expression {
        expr: Expr::call(Expr::named("print"), args),
    }
}

/// `local names = values` without type annotations.
pub fn local(names: Vec<Identifier>, values: Vec<Expr>) -> Stmt {
    Stmt::LocalDeclaration {
        names: names.into_iter().map(Typed::untyped).collect(),
        values,
    }
}

/// `target += 1`.
pub fn increment(target: Expr) -> Stmt {
    Stmt::CompoundAssignment {
        lhs: target,
        op: mallow_core::operator::CompoundBinOp::Add,
        rhs: Expr::float(1.0),
    }
}

/// `if condition then body end`.
pub fn if_then(condition: Expr, body: Vec<Stmt>) -> Stmt {
    Stmt::If(If {
        condition,
        then_body: Block::with_stmts(body),
        else_clause: None,
    })
}

/// A parameter without a type annotation.
pub fn param(name: Identifier) -> Typed<Parameter> {
    Typed::untyped(Parameter::Regular(name))
}

/// Returns whether `stmts` ends in a statement that must be last in its block.
pub fn ends_in_terminator(stmts: &[Stmt]) -> bool {
    matches!(
        stmts.last(),
        Some(Stmt::Break | Stmt::Continue | Stmt::Return { .. })
    )
}
