//! Folds pack bindings and their direct projections into scalar or multibindings.
//!
//! A `BindPack` with one direct projection becomes one `Bind` containing the projected
//! pack. Multiple direct projections become one `BindMany`, so the emitter can emit
//! `local a, b, c = f()` mechanically. Subsequent projections don't need to cover
//! every index from 0 to N, and unused slots become [`Place::Discard`].

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
    /// Returns whether this pack can be folded into one binding or dropped.
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
            let facts = self.entry(pack);
            match target {
                Place::Local(local) => facts.projections.push((index, local)),
                // A discard projection consumes its slot without binding a local.
                Place::Discard => facts.reads += 1,
                _ => unreachable!("direct projections only target locals and discards"),
            }
            return;
        }
        walk_stmt(self, stmt);
    }

    fn visit_pack_expr(&mut self, pack: &PackExpr) {
        if let PackExpr::Local(local) = pack {
            self.entry(*local).reads += 1;
            return;
        }
        walk_pack_expr(self, pack);
    }
}

/// Rewrites pack bindings into scalar bindings, multibindings, or evaluation.
struct Folder {
    /// Use facts collected before rewriting.
    facts: UseFacts,
    /// Whether any statement was rewritten.
    changed: bool,
}

impl VisitorMut for Folder {
    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        let mut index = 0;
        while index < stmts.len() {
            let (local, value) = match &stmts[index] {
                Stmt::BindPack { local, value } => (*local, value),
                _ => {
                    index += 1;
                    continue;
                }
            };

            // Packs without collected facts have no consumers at all.
            let empty = PackFacts::default();
            let facts = self.facts.packs.get(&local).unwrap_or(&empty);
            if !facts.foldable() {
                index += 1;
                continue;
            }

            // Consume the projections that directly follow the pack binding.
            let consumed: Vec<_> = stmts[index + 1..]
                .iter()
                .map_while(|stmt| {
                    let (target, pack, slot) = direct_projection(stmt)?;
                    (pack == local).then_some((slot, target))
                })
                .collect();

            if consumed.is_empty() {
                stmts[index] = Stmt::Eval {
                    value: value.clone(),
                };
                self.changed = true;
                index += 1;
                continue;
            }

            if consumed.len() != facts.projections.len() {
                // Non-adjacent projections exist; leave everything unfolded so no
                // projection is left referencing a removed pack binding.
                index += 1;
                continue;
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
                    values: Box::new(value.clone()),
                };
            }
            stmts.drain(index + 1..=index + facts.projections.len());
            self.changed = true;
            index += 1;
        }

        walk_stmts_mut(self, stmts);
    }
}

#[cfg(test)]
mod tests {
    use id_arena::Arena;

    use super::*;
    use crate::ir::fir::{Constant, Pack, Value};
    use crate::ir::nir::{Expr, Function, Local, PackLocal, Region};

    /// Allocates unique identities for test statements.
    #[derive(Default)]
    struct Ids {
        values: Arena<Value>,
        packs: Arena<Pack>,
        locals: Arena<Local>,
        pack_locals: Arena<PackLocal>,
    }

    impl Ids {
        /// Allocates one local identity.
        fn local(&mut self) -> LocalId {
            let source = self.values.alloc(Value);
            self.locals.alloc(Local { source })
        }

        /// Allocates one pack local identity.
        fn pack(&mut self) -> PackLocalId {
            let source = self.packs.alloc(Pack);
            self.pack_locals.alloc(PackLocal { source })
        }
    }

    /// Builds one nil literal expression.
    fn nil_expr() -> Expr {
        Expr::Constant(Constant::Nil)
    }

    /// Builds one projection of one pack local at one index.
    fn project(pack: PackLocalId, index: usize) -> Expr {
        Expr::Project {
            pack: Box::new(PackExpr::Local(pack)),
            index,
        }
    }

    /// Builds one bind of one place from one value.
    fn bind(target: Place, value: Expr) -> Stmt {
        Stmt::Bind { target, value }
    }

    /// Builds one pack binding holding one empty value list.
    fn bind_pack(pack: PackLocalId) -> Stmt {
        Stmt::BindPack {
            local: pack,
            value: PackExpr::Values {
                head: Vec::new(),
                tail: None,
            },
        }
    }

    /// Wraps one statement list in a function body and folds it.
    fn fold(stmts: Vec<Stmt>) -> Vec<Stmt> {
        let function = Function {
            id: crate::il::ProtoId(0),
            locals: Arena::new(),
            packs: Arena::new(),
            params: Vec::new(),
            is_vararg: false,
            upvalues: Vec::new(),
            prologue: Vec::new(),
            body: Region::Block { origin: 0, stmts },
        };
        let mut function = function;
        run(&mut function);
        match function.body {
            Region::Block { stmts, .. } => stmts,
            _ => unreachable!("the body stayed a block"),
        }
    }

    /// Folds consecutive projections into one multibinding.
    #[test]
    fn folds_contiguous_projections() {
        let mut ids = Ids::default();
        let (pack, first, second) = (ids.pack(), ids.local(), ids.local());
        let folded = fold(vec![
            bind_pack(pack),
            bind(Place::Local(first), project(pack, 0)),
            bind(Place::Local(second), project(pack, 1)),
        ]);

        let [Stmt::BindMany { targets, .. }] = &folded[..] else {
            panic!("the pack should fold into one multibinding");
        };
        assert_eq!(targets, &[Place::Local(first), Place::Local(second)]);
    }

    /// Folds one projection into one scalar binding.
    #[test]
    fn folds_one_projection_into_scalar_binding() {
        let mut ids = Ids::default();
        let (pack, third) = (ids.pack(), ids.local());
        let folded = fold(vec![
            bind_pack(pack),
            bind(Place::Local(third), project(pack, 2)),
        ]);

        let [
            Stmt::Bind {
                target: Place::Local(target),
                value:
                    Expr::Project {
                        pack: source,
                        index: 2,
                    },
            },
        ] = &folded[..]
        else {
            panic!("one projection should fold into one scalar binding");
        };
        assert_eq!(*target, third);
        assert!(matches!(**source, PackExpr::Values { .. }));
    }

    /// Fills unused projection slots with discard places.
    #[test]
    fn fills_projection_gaps_with_discards() {
        let mut ids = Ids::default();
        let (pack, first, third) = (ids.pack(), ids.local(), ids.local());
        let folded = fold(vec![
            bind_pack(pack),
            bind(Place::Local(first), project(pack, 0)),
            bind(Place::Local(third), project(pack, 2)),
        ]);

        let [Stmt::BindMany { targets, .. }] = &folded[..] else {
            panic!("the gapped projections should still fold");
        };
        assert_eq!(
            targets,
            &[Place::Local(first), Place::Discard, Place::Local(third)]
        );
    }

    /// Leaves packs folded when one projection is not directly adjacent.
    #[test]
    fn keeps_nonadjacent_projections_unfolded() {
        let mut ids = Ids::default();
        let (pack, first, second) = (ids.pack(), ids.local(), ids.local());
        let statements = vec![
            bind_pack(pack),
            bind(Place::Local(first), project(pack, 0)),
            bind(Place::Local(second), nil_expr()),
            bind(Place::Local(second), project(pack, 1)),
        ];
        // Run on a copy so the input stays comparable.
        let folded = fold(statements.clone());

        assert_eq!(folded, statements);
    }

    /// Replaces consumer-free pack bindings with effect-only evaluation.
    #[test]
    fn evaluates_consumer_free_packs_for_effect() {
        let mut ids = Ids::default();
        let pack = ids.pack();
        let folded = fold(vec![bind_pack(pack)]);

        eprintln!("{:?}", folded);
        assert!(matches!(&folded[..], [Stmt::Eval { .. }]));
    }

    /// Keeps packs with reads outside direct projections unfolded.
    #[test]
    fn keeps_read_packs_unfolded() {
        let mut ids = Ids::default();
        let (pack, reader, first) = (ids.pack(), ids.local(), ids.local());
        // One nested projection inside a binary expression counts as a read.
        let read = bind(
            Place::Local(reader),
            Expr::Binary {
                lhs: Box::new(project(pack, 0)),
                op: crate::operator::BinOp::Add,
                rhs: Box::new(nil_expr()),
            },
        );
        let statements = vec![
            bind_pack(pack),
            bind(Place::Local(first), project(pack, 0)),
            read,
        ];
        let folded = fold(statements.clone());

        assert_eq!(folded, statements);
    }
}
