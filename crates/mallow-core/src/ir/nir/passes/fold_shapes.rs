//! Folds short-circuit-like NIR shapes that share a common block into binary expressions.
//!
//! This runs as a separate pass because the region structurer can't detect these shapes
//! on its own if the relevant if-conditions span multiple statements, so they only collapse
//! into a single NIR expression after inlining has run. Only then can they be folded.

use crate::ir::nir::visitor::{VisitorMut, walk_region_mut};
use crate::ir::nir::{Expr, Function, Region};

pub(super) fn run(function: &mut Function) -> bool {
    let mut folder = Folder::default();
    folder.visit_function(function);
    folder.changed
}

/// Detects two consecutive [`Region::If`] nodes that share the same body and merges
/// their conditions into a single if-region using a [`BinOp::Or`] expression.
///
/// The input has this shape:
///
/// ```text
/// if A then
///     X
/// end
///
/// if B then
///     X
/// else
///     Y
/// end
/// ```
///
/// The folded region has this shape:
///
/// ```text
/// if A or B then
///     X
/// else
///     Y
/// end
/// ```
///
/// Returns `Some(region)` with the folded `if cond1 or cond2 then ... end` when
/// the merge applies. Returns `None` if `first` has an else branch, or if the
/// two then-branches aren't [flatly equal](flat_eq).
#[must_use]
fn consecutive_or(first: &Region, second: &Region) -> Option<Region> {
    if let (
        Region::If {
            condition: cond_first,
            then_branch: then_first,
            else_branch: None,
        },
        Region::If {
            condition: cond_second,
            then_branch: then_second,
            else_branch: else_second,
        },
    ) = (first, second)
        && flat_eq(then_first, then_second)
    {
        Some(Region::If {
            condition: Expr::or(cond_first.clone(), cond_second.clone()),
            then_branch: then_first.clone(),
            else_branch: else_second.clone(),
        })
    } else {
        None
    }
}

/// One nested if-region and the setup regions which precede it.
struct NestedIf<'a> {
    /// Regions evaluated before the nested condition.
    prefix: &'a [Region],
    /// Nested condition.
    condition: &'a Expr,
    /// Nested branch selected by a true condition.
    then_branch: &'a Region,
    /// Optional nested branch selected by a false condition.
    else_branch: Option<&'a Region>,
}

impl<'a> NestedIf<'a> {
    /// Finds an if-region directly or at the end of a sequence.
    fn at_end(region: &'a Region) -> Option<Self> {
        let (prefix, nested) = match region {
            Region::If { .. } => (&[][..], region),
            Region::Sequence(nodes) => {
                let (nested, prefix) = nodes.split_last()?;
                (prefix, nested)
            }
            _ => return None,
        };
        let Region::If {
            condition,
            then_branch,
            else_branch,
        } = nested
        else {
            return None;
        };

        Some(Self {
            prefix,
            condition,
            then_branch,
            else_branch: else_branch.as_deref(),
        })
    }
}

/// Detects a [`Region::If`] whose else branch ends in another [`Region::If`] with the
/// same then branch, and merges their conditions into one OR shape.
///
/// The input has this shape:
///
/// ```text
/// if A then
///     X
/// else
///     P
///     if B then
///         X
///     else
///         Y
///     end
/// end
/// ```
///
/// Condition setup in `P` stays on the false path of `A`:
///
/// ```text
/// if not A then
///     P
/// end
///
/// if A or B then
///     X
/// else
///     Y
/// end
/// ```
#[must_use]
fn nested_or(parent: &Region) -> Option<Region> {
    let Region::If {
        condition: cond_parent,
        then_branch: then_parent,
        else_branch: Some(else_parent),
    } = parent
    else {
        return None;
    };
    let nested = NestedIf::at_end(else_parent)?;
    if then_parent.as_ref() != nested.then_branch {
        return None;
    }

    let folded = Region::If {
        condition: Expr::or(cond_parent.clone(), nested.condition.clone()),
        then_branch: then_parent.clone(),
        else_branch: nested.else_branch.cloned().map(Box::new),
    };
    with_guarded_setup(cond_parent, nested.prefix, folded)
}

/// Detects a [`Region::If`] whose then branch equals the else branch of an if-region
/// nested in its else branch, and merges the conditions using OR and NOT expressions.
///
/// The input has this shape:
///
/// ```text
/// if A then
///     X
/// else
///     P
///     if B then
///         Y
///     else
///         X
///     end
/// end
/// ```
///
/// Condition setup in `P` stays on the false path of `A`:
///
/// ```text
/// if not A then
///     P
/// end
///
/// if A or not B then
///     X
/// else
///     Y
/// end
/// ```
#[must_use]
fn nested_or_not(parent: &Region) -> Option<Region> {
    let Region::If {
        condition: cond_parent,
        then_branch: then_parent,
        else_branch: Some(else_parent),
    } = parent
    else {
        return None;
    };
    let nested = NestedIf::at_end(else_parent)?;
    if Some(then_parent.as_ref()) != nested.else_branch {
        return None;
    }

    let folded = Region::If {
        condition: Expr::or(cond_parent.clone(), Expr::not(nested.condition.clone())),
        then_branch: then_parent.clone(),
        else_branch: Some(Box::new(nested.then_branch.clone())),
    };
    with_guarded_setup(cond_parent, nested.prefix, folded)
}

/// Keeps nested condition setup behind the parent condition's false path.
fn with_guarded_setup(
    parent_condition: &Expr,
    prefix: &[Region],
    folded: Region,
) -> Option<Region> {
    if prefix.is_empty() {
        return Some(folded);
    }

    // Only pure conditions can be repeated.
    if !matches!(parent_condition, Expr::Constant(_) | Expr::Local(_)) {
        return None;
    }

    Some(Region::Sequence(vec![
        Region::If {
            condition: Expr::not(parent_condition.clone()),
            then_branch: Box::new(Region::Sequence(prefix.to_vec())),
            else_branch: None,
        },
        folded,
    ]))
}

/// Detects a [`Region::If`] whose 'then branch' is itself a [`Region::If`], where both
/// have the same 'else branch', and merges their conditions into a single if-region using
/// a [`BinOp::And`] expression.
///
/// The input has this shape:
///
/// ```text
/// if A then
///     if B then
///         X
///     else
///         Y
///     end
/// else
///     Y
/// end
/// ```
///
/// The folded region has this shape:
///
/// ```text
/// if A and B then
///     X
/// else
///     Y
/// end
/// ```
///
/// `Y` may be absent from both places.
///
/// Returns `Some(region)` with the folded `if cond1 and cond2 then ... end` when the
/// nested shape matches, or `None` if `parent`'s then-branch isn't itself an `if`.
#[must_use]
fn nested_and(parent: &Region) -> Option<Region> {
    if let Region::If {
        condition: cond_parent,
        then_branch: then_parent,
        else_branch: else_parent,
    } = parent
        && let Region::If {
            condition: cond_child,
            then_branch: then_child,
            else_branch: else_child,
        } = then_parent.as_ref()
        && match (else_parent.as_ref(), else_child.as_ref()) {
            (None, None) => true,
            (Some(a), Some(b)) => flat_eq(a, b),
            _ => false,
        }
    {
        Some(Region::If {
            condition: Expr::and(cond_parent.clone(), cond_child.clone()),
            then_branch: then_child.clone(),
            else_branch: else_parent.clone(),
        })
    } else {
        None
    }
}

fn fold_consecutive_ors(nodes: &mut Vec<Region>) -> bool {
    let input = std::mem::take(nodes);
    let mut output = Vec::with_capacity(input.len());
    let mut changed = false;

    for node in input {
        let folded = output
            .last()
            .and_then(|previous| consecutive_or(previous, &node));

        if let Some(folded) = folded {
            *output.last_mut().expect("a previous region exists") = folded;
            changed = true;
        } else {
            output.push(node);
        }
    }

    *nodes = output;
    changed
}

/// Returns whether two regions are flatly equal - identical blocks, or sequences
/// with the same shape where every element is flatly equal in turn.
///
/// This is intentionally *not* a full structural `Eq`. Regions with actual nested
/// control flow ([`Region::If`], [`Region::While`], [`Region::RepeatUntil`]) are
/// never flatly equal, even to themselves. [`Region::Continue`] and [`Region::Break`]
/// are flat (single-statement, no nesting) and compare equal to themselves.
fn flat_eq(a: &Region, b: &Region) -> bool {
    match (a, b) {
        (Region::Block { origin: og_a, .. }, Region::Block { origin: og_b, .. }) => og_a == og_b,
        (Region::Break, Region::Break) | (Region::Continue, Region::Continue) => true,
        (Region::Sequence(seq_a), Region::Sequence(seq_b)) => {
            seq_a.len() == seq_b.len() && seq_a.iter().zip(seq_b.iter()).all(|(a, b)| flat_eq(a, b))
        }
        _ => false,
    }
}

#[derive(Default)]
struct Folder {
    changed: bool,
}

impl VisitorMut for Folder {
    fn visit_region(&mut self, region: &mut Region) {
        // Fold children before examining their parent shape.
        walk_region_mut(self, region);

        if let Some(folded) = nested_and(region) {
            *region = folded;
            self.changed = true;
        }

        if let Some(folded) = nested_or(region) {
            *region = folded;
            self.changed = true;
        }

        if let Some(folded) = nested_or_not(region) {
            *region = folded;
            self.changed = true;
        }

        if let Region::Sequence(nodes) = region {
            self.changed |= fold_consecutive_ors(nodes);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::operator::UnOp;

    use super::*;

    /// Creates an empty flat block for shape tests.
    fn block(origin: usize) -> Region {
        Region::Block {
            origin,
            stmts: Vec::new(),
        }
    }

    /// Verifies that equal branches in an if-else-if chain are merged.
    #[test]
    fn nested_or_merges_equal_then_branches() {
        let body = block(1);
        let fallback = block(2);
        let parent = Region::If {
            condition: Expr::boolean(true),
            then_branch: Box::new(body.clone()),
            else_branch: Some(Box::new(Region::If {
                condition: Expr::boolean(false),
                then_branch: Box::new(body.clone()),
                else_branch: Some(Box::new(fallback.clone())),
            })),
        };

        assert_eq!(
            nested_or(&parent),
            Some(Region::If {
                condition: Expr::or(Expr::boolean(true), Expr::boolean(false)),
                then_branch: Box::new(body),
                else_branch: Some(Box::new(fallback)),
            })
        );
    }

    /// Verifies that a condition setup stays conditional when nested branches are merged.
    #[test]
    fn nested_or_keeps_condition_setup_guarded() {
        let body = Region::While {
            condition: Expr::boolean(true),
            body: Box::new(block(1)),
        };
        let setup = block(2);
        let fallback = block(3);
        let parent = Region::If {
            condition: Expr::boolean(true),
            then_branch: Box::new(body.clone()),
            else_branch: Some(Box::new(Region::Sequence(vec![
                setup.clone(),
                Region::If {
                    condition: Expr::boolean(false),
                    then_branch: Box::new(body.clone()),
                    else_branch: Some(Box::new(fallback.clone())),
                },
            ]))),
        };

        assert_eq!(
            nested_or(&parent),
            Some(Region::Sequence(vec![
                Region::If {
                    condition: Expr::Unary {
                        op: UnOp::Not,
                        value: Box::new(Expr::boolean(true)),
                    },
                    then_branch: Box::new(Region::Sequence(vec![setup])),
                    else_branch: None,
                },
                Region::If {
                    condition: Expr::or(Expr::boolean(true), Expr::boolean(false)),
                    then_branch: Box::new(body),
                    else_branch: Some(Box::new(fallback)),
                },
            ]))
        );
    }

    /// Verifies that matching outer and nested else branches are merged.
    #[test]
    fn nested_or_not_merges_equal_else_branch() {
        let body = Region::While {
            condition: Expr::boolean(true),
            body: Box::new(block(1)),
        };
        let setup = block(2);
        let fallback = block(3);
        let parent = Region::If {
            condition: Expr::boolean(true),
            then_branch: Box::new(body.clone()),
            else_branch: Some(Box::new(Region::Sequence(vec![
                setup.clone(),
                Region::If {
                    condition: Expr::boolean(false),
                    then_branch: Box::new(fallback.clone()),
                    else_branch: Some(Box::new(body.clone())),
                },
            ]))),
        };

        assert_eq!(
            nested_or_not(&parent),
            Some(Region::Sequence(vec![
                Region::If {
                    condition: Expr::not(Expr::boolean(true)),
                    then_branch: Box::new(Region::Sequence(vec![setup])),
                    else_branch: None,
                },
                Region::If {
                    condition: Expr::or(Expr::boolean(true), Expr::not(Expr::boolean(false))),
                    then_branch: Box::new(body),
                    else_branch: Some(Box::new(fallback)),
                },
            ]))
        );
    }

    /// Verifies that setup is not moved across a condition which cannot be repeated.
    #[test]
    fn nested_or_keeps_setup_behind_unstable_condition() {
        let body = block(1);
        let parent = Region::If {
            condition: Expr::GetGlobal("condition".into()),
            then_branch: Box::new(body.clone()),
            else_branch: Some(Box::new(Region::Sequence(vec![
                block(2),
                Region::If {
                    condition: Expr::boolean(false),
                    then_branch: Box::new(body),
                    else_branch: Some(Box::new(block(3))),
                },
            ]))),
        };

        assert_eq!(nested_or(&parent), None);
    }

    /// Verifies that different branches in an if-else-if chain stay separate.
    #[test]
    fn nested_or_keeps_different_then_branches() {
        let parent = Region::If {
            condition: Expr::boolean(true),
            then_branch: Box::new(block(1)),
            else_branch: Some(Box::new(Region::If {
                condition: Expr::boolean(false),
                then_branch: Box::new(block(2)),
                else_branch: Some(Box::new(block(3))),
            })),
        };

        assert_eq!(nested_or(&parent), None);
    }
}
