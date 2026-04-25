use crate::{
    ast::{BinOp, UnOp},
    hil::ir::HilExpr,
};

#[must_use]
pub fn invert_condition(expr: HilExpr) -> HilExpr {
    match expr {
        HilExpr::Bool(b) => HilExpr::Bool(!b),
        // TODO: https://github.com/rust-lang/rust/issues/51114
        // will be stable in two tweeks from now
        HilExpr::Binary { lhs, op, rhs } => {
            if let Some(inverted) = invert_binop(op) {
                HilExpr::Binary {
                    lhs: Box::new(*lhs),
                    op: inverted,
                    rhs: Box::new(*rhs),
                }
            } else {
                HilExpr::Unary {
                    op: UnOp::Not,
                    expr: Box::new(HilExpr::Binary { lhs, op, rhs }),
                }
            }
        }
        HilExpr::Unary {
            op: UnOp::Not,
            expr: inner,
        } => *inner,
        _ => HilExpr::Unary {
            op: UnOp::Not,
            expr: Box::new(expr),
        },
    }
}

fn invert_binop(op: BinOp) -> Option<BinOp> {
    match op {
        BinOp::Eq => Some(BinOp::Ne),
        BinOp::Ne => Some(BinOp::Eq),
        BinOp::Lt => Some(BinOp::Gte),
        BinOp::Lte => Some(BinOp::Gt),
        BinOp::Gt => Some(BinOp::Lte),
        BinOp::Gte => Some(BinOp::Lt),
        _ => None,
    }
}

// pub trait GraphView {
//     fn successors(&self, node: usize) -> &[usize];
//     fn predecessors(&self, node: usize) -> &[usize];
//     fn contains_node(&self, node: usize) -> bool;
// }

// pub trait GraphRewrite: GraphView {
//     fn redirect_predecessors(&mut self, from: usize, to: usize);
//     fn redirect_successors(&mut self, from: usize, to: usize);
//     fn remove_node(&mut self, node: usize);
// }
