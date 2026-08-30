//! Normalizes regions using the following rules:
//!
//! 1. If the *then* branch is empty and the *else* branch is not, swap the branches and invert the condition.
//! 2. Canonicalize binary comparison expressions of the form `[literal] op [!literal]` to `[!literal] op [literal]`.
//! 3. Simplify pattern `not (a [op @ ==|~=] b)` into `a [invert(op)] b`.

use crate::ir::nir::visitor::{VisitorMut, walk_expr_mut, walk_region_mut};
use crate::ir::nir::{Expr, Function, Region};
use crate::operator::{BinOp, UnOp};

pub fn run(function: &mut Function) -> bool {
    let mut normalizer = Normalizer::default();
    normalizer.visit_function(function);
    normalizer.changed
}

#[derive(Default)]
struct Normalizer {
    changed: bool,
}

impl VisitorMut for Normalizer {
    fn visit_region(&mut self, region: &mut Region) {
        if let Region::If {
            condition,
            then_branch,
            else_branch,
        } = region
            && then_branch.is_empty()
            && else_branch.as_ref().is_some_and(|b| !b.is_empty())
        {
            *then_branch = else_branch.take().expect("checked above");
            *condition = condition.clone().invert();
            self.changed = true;
        }

        walk_region_mut(self, region);
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if let Expr::Binary { lhs, op, rhs } = expr
            && let Some(flipped) = op.flip()
            && matches!(lhs.as_ref(), Expr::Constant(_))
            && !matches!(rhs.as_ref(), Expr::Constant(_))
        {
            *op = flipped;
            std::mem::swap(lhs, rhs);
            self.changed = true;
        }

        if let Expr::Unary {
            op: UnOp::Not,
            value,
        } = expr
            && let Expr::Binary {
                op: bin_op @ (BinOp::Eq | BinOp::Ne),
                lhs,
                rhs,
            } = value.as_mut()
        {
            *expr = Expr::Binary {
                lhs: Box::new(lhs.as_ref().clone()),
                op: bin_op.invert().expect("equality operators are invertible"),
                rhs: Box::new(rhs.as_ref().clone()),
            };
            self.changed = true;
        }

        walk_expr_mut(self, expr);
    }
}
