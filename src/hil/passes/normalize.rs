//! Normalizes the HIL tree using the following rules:
//!
//! 1. If the *then* branch is empty and the *else* branch is not, swap the branches and invert the condition.
//! 2. Canonicalize binary comparison expressions of the form `[literal] op [expr]` to `[expr] op [literal]`.
//! 3. Simplify pattern `not (a == b)` into `a ~= b`.

use crate::{
    ast::{BinOp, UnOp},
    hil::{
        StructuredFunction,
        cflow::region::RegionNode,
        ir::HilExpr,
        visitor::{VisitorMut, walk_region_mut},
    },
};

#[derive(Default)]
struct Normalizer {
    changed: bool,
}

impl VisitorMut for Normalizer {
    fn visit_region(&mut self, region: &mut RegionNode) {
        if let RegionNode::If {
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

    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Binary { lhs, op, rhs } = expr
            && let Some(flipped) = op.flip()
            && lhs.is_literal()
            && !rhs.is_literal()
        {
            *op = flipped;
            std::mem::swap(lhs, rhs);
            self.changed = true;
        }

        if let HilExpr::Unary {
            op: un_op,
            expr: inner,
        } = expr
            && *un_op == UnOp::Not
            && let HilExpr::Binary {
                op: bin_op,
                lhs,
                rhs,
            } = inner.as_mut()
            && *bin_op == BinOp::Eq
        {
            *expr = HilExpr::Binary {
                lhs: Box::new(lhs.as_ref().clone()),
                op: BinOp::Ne,
                rhs: Box::new(rhs.as_ref().clone()),
            };
            self.changed = true;
        }
    }
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut normalizer = Normalizer::default();
    normalizer.visit_function(fun);
    normalizer.changed
}
