//! Folds pack projections into scalar or multibindings.
//!
//! A `BindPack` with one direct projection becomes one `Bind` containing the projected
//! pack. Multiple direct projections become one `BindMany`, so the emitter can emit
//! `local a, b, c = f()` mechanically. Subsequent projections don't need to cover
//! every index from 0 to N, and unused slots become [`Place::Discard`].
//!
//! A multibinding followed by direct table writes can also forward its temporary
//! locals into those writes. This recovers assignments such as `t[1], t[2] = f()`
//! without changing the bounded result count of the original assignment.

use std::collections::{HashMap, HashSet};

use crate::ir::nir::visitor::{Visitor, VisitorMut, walk_pack_expr, walk_stmt, walk_stmts_mut};
use crate::ir::nir::{Expr, Function, LocalId, PackExpr, PackLocalId, Place, Stmt};

/// Folds one function's pack bindings. Returns whether anything changed.
pub(super) fn run(function: &mut Function) -> bool {
    let facts = UseFacts::collect(function);
    let mut folder = Folder {
        facts,
        changed: false,
    };
    folder.visit_function(function);
    folder.changed
}

/// Returns one direct projection performed by this statement.
///
/// A direct projection writes one scalar result into one local without any
/// enclosing effect, so it can participate in one binding.
#[inline]
fn direct_projection(stmt: &Stmt) -> Option<(Place, PackLocalId, usize)> {
    let Stmt::Bind { target, value } = stmt else {
        return None;
    };
    if !matches!(target, Place::Local(_) | Place::Discard) {
        return None;
    }
    let Expr::Project { pack, index } = value else {
        return None;
    };
    let PackExpr::Local(pack) = pack.as_ref() else {
        return None;
    };
    Some((target.clone(), *pack, *index))
}

/// Use facts collected for every pack local.
#[derive(Default)]
struct PackFacts {
    /// Number of reads outside direct top-level projections.
    reads: usize,
    /// Direct projections in statement order as `(index, target local)` pairs.
    projections: Vec<(usize, LocalId)>,
}

impl PackFacts {
    /// Returns whether this pack can be folded into one binding.
    #[inline]
    fn foldable(&self) -> bool {
        self.reads == 0
            && self.slots().len() == self.projections.len()
            && self.locals().len() == self.projections.len()
    }

    /// Returns the distinct projected slots.
    #[inline]
    #[must_use]
    fn slots(&self) -> HashSet<usize> {
        self.projections.iter().map(|(index, _)| *index).collect()
    }

    /// Returns the distinct projected target locals.
    #[inline]
    #[must_use]
    fn locals(&self) -> HashSet<LocalId> {
        self.projections.iter().map(|(_, local)| *local).collect()
    }
}

/// Collects use facts for every pack local in one function.
#[derive(Default)]
struct UseFacts {
    /// Facts keyed by pack local identity.
    packs: HashMap<PackLocalId, PackFacts>,
    /// Number of mentions for every scalar local.
    local_mentions: HashMap<LocalId, usize>,
}

impl UseFacts {
    /// Collects facts across one complete function.
    fn collect(function: &Function) -> Self {
        let mut collector = Self::default();
        collector.visit_function(function);
        collector
    }

    /// Returns the facts for one pack local, creating them when missing.
    fn entry(&mut self, pack: PackLocalId) -> &mut PackFacts {
        self.packs.entry(pack).or_default()
    }
}

impl Visitor for UseFacts {
    fn visit_stmt(&mut self, stmt: &Stmt) {
        if let Some((target, pack, index)) = direct_projection(stmt) {
            match target {
                Place::Local(local) => {
                    self.entry(pack).projections.push((index, local));
                    *self.local_mentions.entry(local).or_default() += 1;
                }
                // A discard projection consumes its slot without binding a local.
                Place::Discard => self.entry(pack).reads += 1,
                _ => unreachable!("direct projections only target locals and discards"),
            }
            return;
        }
        walk_stmt(self, stmt);
    }

    fn visit_local(&mut self, local: LocalId) {
        *self.local_mentions.entry(local).or_default() += 1;
    }

    fn visit_pack_expr(&mut self, pack: &PackExpr) {
        if let PackExpr::Local(local) = pack {
            self.entry(*local).reads += 1;
            return;
        }
        walk_pack_expr(self, pack);
    }
}

/// Returns whether one expression is stable and independent of projected locals.
#[inline]
fn is_stable_forward_expr(expr: &Expr, projected: &HashSet<LocalId>) -> bool {
    match expr {
        Expr::Local(local) => !projected.contains(local),
        Expr::Constant(_) => true,
        _ => false,
    }
}

/// Returns whether one table target can move into a multibinding.
#[inline]
fn is_safe_forward_target(target: &Place, projected: &HashSet<LocalId>) -> bool {
    let Place::Table { table, key } = target else {
        return false;
    };
    is_stable_forward_expr(table, projected) && is_stable_forward_expr(key, projected)
}

/// Rewrites pack bindings into scalar bindings or multibindings.
struct Folder {
    /// Use facts collected before rewriting.
    facts: UseFacts,
    /// Whether any statement was rewritten.
    changed: bool,
}

impl Folder {
    /// Forwards temporary multibinding locals into adjacent table writes.
    fn forward_multibinding(&mut self, stmts: &mut Vec<Stmt>, index: usize) {
        let Stmt::BindMany { targets, .. } = &stmts[index] else {
            return;
        };

        let projected: HashSet<_> = targets
            .iter()
            .filter_map(|target| match target {
                Place::Local(local) => Some(*local),
                _ => None,
            })
            .collect();
        let mut next = index + 1;
        let mut forwarded = Vec::new();
        for (target_index, target) in targets.iter().enumerate() {
            let Place::Local(local) = target else {
                if matches!(target, Place::Discard) {
                    continue;
                }
                break;
            };
            let Some(Stmt::Bind {
                target: destination,
                value: Expr::Local(source),
            }) = stmts.get(next)
            else {
                break;
            };
            if source != local || !is_safe_forward_target(destination, &projected) {
                break;
            }

            forwarded.push((target_index, *local, destination.clone()));
            next += 1;
        }

        if forwarded.is_empty()
            || forwarded
                .iter()
                .any(|(_, local, _)| self.facts.local_mentions.get(local) != Some(&2))
        {
            return;
        }

        let Stmt::BindMany { targets, .. } = &mut stmts[index] else {
            unreachable!("the checked statement stayed a multibinding");
        };
        for (target_index, _, destination) in forwarded {
            targets[target_index] = destination;
        }
        stmts.drain(index + 1..next);
        self.changed = true;
    }

    /// Folds one pack binding and its adjacent scalar projections.
    fn fold_projections(&mut self, stmts: &mut Vec<Stmt>, index: usize) {
        let Stmt::BindPack { local, value } = &stmts[index] else {
            return;
        };
        let local = *local;
        let value = value.clone();

        // A pack without facts has no consumers, but its value may have effects.
        let Some(facts) = self.facts.packs.get(&local) else {
            stmts[index] = Stmt::Eval { value };
            self.changed = true;
            return;
        };
        if !facts.foldable() {
            return;
        }
        let projection_count = facts.projections.len();

        let consumed: Vec<_> = stmts[index + 1..]
            .iter()
            .map_while(|stmt| {
                let (target, pack, slot) = direct_projection(stmt)?;
                (pack == local).then_some((slot, target))
            })
            .collect();

        if consumed.len() != projection_count {
            // Non-adjacent projections exist. Leave everything unfolded so no
            // projection is left referencing a removed pack binding.
            return;
        }

        if consumed.len() == 1 {
            let (slot, target) = consumed.into_iter().next().expect("one projection");
            stmts[index] = Stmt::Bind {
                target,
                value: Expr::Project {
                    pack: Box::new(value.clone()),
                    index: slot,
                },
            };
        } else {
            let last_slot = consumed
                .iter()
                .map(|(index, _)| index)
                .max()
                .expect("non-empty");
            let mut targets = vec![Place::Discard; last_slot + 1];
            for (index, target) in consumed {
                targets[index] = target;
            }
            stmts[index] = Stmt::BindMany {
                targets,
                values: Box::new(value),
            };
        }

        stmts.drain(index + 1..=index + projection_count);
        self.changed = true;
        self.forward_multibinding(stmts, index);
    }
}

impl VisitorMut for Folder {
    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        let mut index = 0;
        while index < stmts.len() {
            match &stmts[index] {
                Stmt::BindMany { .. } => self.forward_multibinding(stmts, index),
                Stmt::BindPack { .. } => self.fold_projections(stmts, index),
                _ => {}
            }
            index += 1;
        }

        walk_stmts_mut(self, stmts);
    }
}
