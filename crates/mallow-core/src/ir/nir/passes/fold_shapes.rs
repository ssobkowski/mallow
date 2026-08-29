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

/// Detects a [`Region::If`] whose 'then branch' is itself a [`Region::If`], where both
/// have the same 'else branch', and merges their conditions into a single if-region using
/// a [`BinOp::And`] expression.
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

        if let Region::Sequence(nodes) = region {
            self.changed |= fold_consecutive_ors(nodes);
        }
    }
}
