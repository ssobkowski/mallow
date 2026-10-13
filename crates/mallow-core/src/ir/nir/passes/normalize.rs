//! Normalizes regions using the following rules:
//!
//! 1. If the *then* branch is empty and the *else* branch is not, swap the branches and invert the condition.
//! 2. Remove empty sequence children and unwrap singleton sequences.
//! 3. Canonicalize binary comparison expressions of the form `[literal] op [!literal]` to `[!literal] op [literal]`.
//! 4. Simplify pattern `not (a [op @ ==|~=] b)` into `a [invert(op)] b`.
//! 5. Simplify `if c then true else false` into `not not c`, and `if c then false else true` into `not c`.
//! 6. Simplify `not not c` into `c` when `c` always evaluates to a boolean.
//! 7. In a condition, rewrite `not (a and b)` into `not a or not b`, and `not (a or b)` into
//!    `not a and not b`, when that leaves fewer `not`s. This applies only where
//!    truthiness is all that matters, because `not (not a or b)` is `false` where `a and not b`
//!    can be `nil`.

use crate::ir::nir::visitor::{VisitorMut, walk_expr_mut, walk_region_mut};
use crate::ir::nir::{Constant, Expr, Function, Region};
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
        if let Region::If { condition, .. }
        | Region::While { condition, .. }
        | Region::RepeatUntil { condition, .. } = region
        {
            self.changed |= apply_de_morgan(condition);
        }

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

        if let Region::Sequence(nodes) = region {
            let previous_len = nodes.len();
            nodes.retain(|node| !node.is_empty());
            self.changed |= nodes.len() != previous_len;

            if nodes.len() == 1 {
                *region = nodes.pop().expect("nodes is not empty");
                self.changed = true;
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if let Expr::Select {
            condition,
            then_value,
            else_value,
        } = expr
            && let (
                Expr::Constant(Constant::Bool(then_bool)),
                Expr::Constant(Constant::Bool(else_bool)),
            ) = (then_value.as_ref(), else_value.as_ref())
            && then_bool != else_bool
        {
            let negated = Expr::not(condition.as_ref().clone());
            *expr = if *then_bool {
                Expr::not(negated)
            } else {
                negated
            };
            self.changed = true;
        }

        if let Expr::Unary {
            op: UnOp::Not,
            value,
        } = expr
            && let Expr::Unary {
                op: UnOp::Not,
                value: inner,
            } = value.as_ref()
            && inner.is_boolean()
        {
            *expr = inner.as_ref().clone();
            self.changed = true;
        }

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

/// Applies rule 7 to the condition `expr` and to every operand whose
/// truthiness is all that matters. Returns whether anything changed.
fn apply_de_morgan(expr: &mut Expr) -> bool {
    let mut changed = false;
    if let Expr::Unary {
        op: UnOp::Not,
        value,
    } = expr
        && let Expr::Binary {
            op: op @ (BinOp::And | BinOp::Or),
            lhs,
            rhs,
        } = value.as_ref()
        // The rewrite drops the outer `not`, so it leaves fewer `not`s when
        // inverting both operands adds at most one back.
        && not_count_change(lhs) + not_count_change(rhs) <= 0
    {
        let op = if *op == BinOp::And {
            BinOp::Or
        } else {
            BinOp::And
        };
        *expr = Expr::Binary {
            lhs: Box::new(lhs.as_ref().clone().invert()),
            op,
            rhs: Box::new(rhs.as_ref().clone().invert()),
        };
        changed = true;
    }

    match expr {
        Expr::Unary {
            op: UnOp::Not,
            value,
        } => changed | apply_de_morgan(value),
        Expr::Binary {
            op: BinOp::And | BinOp::Or,
            lhs,
            rhs,
        } => changed | apply_de_morgan(lhs) | apply_de_morgan(rhs),
        _ => changed,
    }
}

/// Returns how many `not`s [`Expr::invert`] adds to `expr`. It is `-1` when
/// the inversion removes a `not`, and `0` when it flips the expression in place.
fn not_count_change(expr: &Expr) -> i32 {
    match expr {
        Expr::Unary { op: UnOp::Not, .. } => -1,
        Expr::Binary {
            op: BinOp::Eq | BinOp::Ne,
            ..
        }
        | Expr::Constant(Constant::Bool(_)) => 0,
        _ => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Returns a global read, an operand that has no special inverse.
    fn name(index: u32) -> Expr {
        Expr::GetGlobal(format!("g{index}").into())
    }

    fn eq(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            lhs: Box::new(lhs),
            op: BinOp::Eq,
            rhs: Box::new(rhs),
        }
    }

    fn ne(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            lhs: Box::new(lhs),
            op: BinOp::Ne,
            rhs: Box::new(rhs),
        }
    }

    /// `not (a == 1 or a == 2)` becomes `a ~= 1 and a ~= 2`.
    #[test]
    fn de_morgan_removes_not() {
        let mut condition = Expr::not(Expr::or(eq(name(0), name(1)), eq(name(0), name(2))));
        assert!(apply_de_morgan(&mut condition));
        assert_eq!(
            condition,
            Expr::and(ne(name(0), name(1)), ne(name(0), name(2)))
        );
    }

    /// `not (a or not b)` becomes `not a and b`.
    #[test]
    fn de_morgan_moves_not() {
        let mut condition = Expr::not(Expr::or(name(0), Expr::not(name(1))));
        assert!(apply_de_morgan(&mut condition));
        assert_eq!(condition, Expr::and(Expr::not(name(0)), name(1)));
    }

    /// `not (a == 1 or b)` stays, because `a ~= 1 and not b` has as many `not`s.
    #[test]
    fn de_morgan_skips_same_not_count() {
        let mut condition = Expr::not(Expr::or(eq(name(0), name(1)), name(2)));
        assert!(!apply_de_morgan(&mut condition));
    }

    /// `not (a or b)` stays, because the rewrite would add a `not`.
    #[test]
    fn de_morgan_skips_extra_not() {
        let mut condition = Expr::not(Expr::or(name(0), name(1)));
        assert!(!apply_de_morgan(&mut condition));
    }
}
