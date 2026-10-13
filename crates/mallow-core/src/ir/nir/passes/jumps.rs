//! Simplifies `break`, `continue` and `return` statements using the following rules:
//!
//! 1. A `continue` that ends a loop body is removed, because the loop starts
//!    its next iteration there anyway.
//! 2. An `if` where one branch always ends in a `break`, `continue` or
//!    `return` and the other branch can fall through becomes a guard clause.
//!    The `if` keeps the jumping branch and the other branch moves after it.
//!
//! Together they turn the following loop body:
//!
//! ```text
//! if c then
//!     A
//!     continue
//! else
//!     break
//! end
//! ```
//!
//! into:
//!
//! ```text
//! if not c then
//!     break
//! end
//! A
//! ```

use crate::ir::nir::visitor::{VisitorMut, walk_region_mut};
use crate::ir::nir::{Function, Region};

pub(super) fn run(function: &mut Function) -> bool {
    let mut simplifier = Simplifier::default();
    simplifier.visit_function(function);
    simplifier.changed
}

#[derive(Default)]
struct Simplifier {
    changed: bool,
}

impl VisitorMut for Simplifier {
    fn visit_region(&mut self, region: &mut Region) {
        walk_region_mut(self, region);

        match region {
            Region::While { body, .. }
            | Region::RepeatUntil { body, .. }
            | Region::NumericFor { body, .. }
            | Region::GenericFor { body, .. } => {
                self.changed |= drop_trailing_continue(body);
            }
            Region::If { .. } => self.changed |= split_guard(region),
            Region::Sequence(nodes) => self.changed |= flatten(nodes),
            _ => {}
        }
    }
}

/// Returns whether every path through `region` ends in a `break`,
/// `continue` or `return`.
fn always_jumps(region: &Region) -> bool {
    match region {
        Region::Break | Region::Continue | Region::Return(_) => true,
        Region::Sequence(nodes) => nodes.last().is_some_and(always_jumps),
        Region::If {
            then_branch,
            else_branch: Some(else_branch),
            ..
        } => always_jumps(then_branch) && always_jumps(else_branch),
        _ => false,
    }
}

/// Removes the `continue` that ends the loop body `region`. Returns whether
/// one was removed.
///
/// See rule 1 of the [module documentation](self).
fn drop_trailing_continue(region: &mut Region) -> bool {
    match region {
        Region::Continue => {
            *region = Region::Sequence(Vec::new());
            true
        }
        Region::Sequence(nodes) => nodes.last_mut().is_some_and(drop_trailing_continue),
        Region::If {
            then_branch,
            else_branch: Some(else_branch),
            ..
        } => {
            let changed = match (then_branch.as_ref(), else_branch.as_ref()) {
                (Region::Continue, Region::Continue) => {
                    drop_trailing_continue(then_branch) | drop_trailing_continue(else_branch)
                }
                (Region::Continue, _) => drop_guarded_continue(else_branch, then_branch),
                (_, Region::Continue) => drop_guarded_continue(then_branch, else_branch),
                _ => drop_trailing_continue(then_branch) | drop_trailing_continue(else_branch),
            };
            if let Region::If { else_branch, .. } = region
                && else_branch.as_ref().is_some_and(|branch| branch.is_empty())
            {
                *else_branch = None;
            }
            changed
        }
        Region::If {
            then_branch,
            else_branch: None,
            ..
        } => drop_trailing_continue(then_branch),
        _ => false,
    }
}

/// Drops the trailing `continue` of `branch`, where `other` is a branch that
/// is only a `continue`. The `continue` of `other` is dropped too, unless
/// `branch` still falls through afterwards.
fn drop_guarded_continue(branch: &mut Region, other: &mut Region) -> bool {
    let changed = drop_trailing_continue(branch);
    if !branch.is_empty() && !always_jumps(branch) {
        return changed;
    }
    drop_trailing_continue(other) | changed
}

/// Turns the `if` in `region` into a guard clause followed by its other
/// branch. Returns whether it changed.
///
/// See rule 2 of the [module documentation](self).
fn split_guard(region: &mut Region) -> bool {
    let Region::If {
        then_branch,
        else_branch: Some(else_branch),
        ..
    } = region
    else {
        return false;
    };
    let jump_in_then = match (always_jumps(then_branch), always_jumps(else_branch)) {
        (true, false) => true,
        (false, true) => false,
        _ => return false,
    };

    let Region::If {
        condition,
        then_branch,
        else_branch: Some(else_branch),
    } = std::mem::replace(region, Region::Sequence(Vec::new()))
    else {
        unreachable!("checked above");
    };
    let (condition, jump, rest) = if jump_in_then {
        (condition, then_branch, else_branch)
    } else {
        (condition.invert(), else_branch, then_branch)
    };
    let guard = Region::If {
        condition,
        then_branch: jump,
        else_branch: None,
    };
    *region = Region::Sequence(vec![guard, *rest]);
    true
}

/// Moves the children of nested sequences into `nodes`. Returns whether any
/// were moved.
fn flatten(nodes: &mut Vec<Region>) -> bool {
    if !nodes.iter().any(|node| matches!(node, Region::Sequence(_))) {
        return false;
    }

    let input = std::mem::take(nodes);
    for node in input {
        match node {
            Region::Sequence(children) => nodes.extend(children),
            other => nodes.push(other),
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::nir::Expr;

    fn block(origin: usize) -> Region {
        Region::Block {
            origin,
            stmts: Vec::new(),
        }
    }

    fn condition() -> Expr {
        Expr::boolean(true)
    }

    fn if_then(condition: Expr, then_branch: Region) -> Region {
        Region::If {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: None,
        }
    }

    fn if_then_else(then_branch: Region, else_branch: Region) -> Region {
        Region::If {
            condition: condition(),
            then_branch: Box::new(then_branch),
            else_branch: Some(Box::new(else_branch)),
        }
    }

    fn simplify(body: Region) -> Region {
        let mut region = Region::While {
            condition: condition(),
            body: Box::new(body),
        };
        loop {
            let mut simplifier = Simplifier::default();
            simplifier.visit_region(&mut region);
            if !simplifier.changed {
                break;
            }
        }
        let Region::While { body, .. } = region else {
            unreachable!("the loop stays a loop");
        };
        *body
    }

    /// `if c then A continue else break end` becomes `if not c then break end A`.
    #[test]
    fn tail_branch_becomes_guard() {
        let body = if_then_else(
            Region::Sequence(vec![block(1), Region::Continue]),
            Region::Break,
        );
        assert_eq!(
            simplify(body),
            Region::Sequence(vec![if_then(condition().invert(), Region::Break), block(1)])
        );
    }

    /// `if c then continue else A end` becomes `if c then continue end A`.
    #[test]
    fn continue_branch_becomes_guard() {
        let body = Region::Sequence(vec![if_then_else(Region::Continue, block(1)), block(2)]);
        assert_eq!(
            simplify(body),
            Region::Sequence(vec![
                if_then(condition(), Region::Continue),
                block(1),
                block(2)
            ])
        );
    }

    /// `if c then A break else continue end` at the end of a loop becomes
    /// `if c then A break end`.
    #[test]
    fn breaking_branch_stays_inside() {
        let body = if_then_else(
            Region::Sequence(vec![block(1), Region::Break]),
            Region::Continue,
        );
        assert_eq!(
            simplify(body),
            if_then(condition(), Region::Sequence(vec![block(1), Region::Break]))
        );
    }

    /// `if c then continue else A continue end` at the end of a loop body
    /// becomes `if c then continue end A`.
    #[test]
    fn trailing_continue_branch_becomes_guard() {
        let body = if_then_else(
            Region::Continue,
            Region::Sequence(vec![block(1), Region::Continue]),
        );
        assert_eq!(
            simplify(body),
            Region::Sequence(vec![if_then(condition(), Region::Continue), block(1)])
        );
    }

    /// A `continue` that is not at the end of the loop body stays as is.
    #[test]
    fn inner_continue_stays() {
        let body = Region::Sequence(vec![
            if_then(
                condition(),
                Region::Sequence(vec![block(1), Region::Continue]),
            ),
            block(2),
        ]);
        assert_eq!(simplify(body.clone()), body);
    }
}
