//! Compound condition recovery.
//!
//! Luau compiles `a and b or c` into a chain of branch blocks, one per
//! operand. [`Reducer::build`] merges such a chain back into one
//! [`Predicate`] by repeatedly merging a branch block with the next one.
//! This follows the compound condition reduction of Cifuentes (1994).
//!
//! Two blocks `x` and `y` merge when `x` jumps to `y`, `y` is
//! condition-only, `x` is the only way into `y`, and both share one target.
//! The shared target decides the operator.
//!
//! ```text
//! x ──true──► y ──true──► T        x and y
//! │           │
//! false     false
//! ▼           ▼
//! F ◄─────────┘
//!
//! x ──false─► y ──false─► F        x or y
//! │           │
//! true       true
//! ▼           ▼
//! T ◄─────────┘
//! ```
//!
//! The other two patterns are the same with the edges of `y` swapped,
//! which gives `x and not y` and `x or not y`. The rule "`x` is the only way
//! into `y`" keeps code that other paths share out of the condition.

use super::{Predicate, RegionGraph};
use crate::collections::IndexSet;
use crate::ir::fir::BlockExit;
use crate::ir::fir::folding::Folding;
use crate::ir::graph::GraphView;

/// One or more blocks that together choose between two blocks.
///
/// Every block except `head` is condition-only, so the whole decision is
/// one source condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Decision {
    /// The first block. Its statements run before the condition.
    pub(super) head: usize,
    /// Every block of the decision, including `head`.
    pub(super) blocks: IndexSet<usize>,
    /// True when control goes to `then_target`.
    pub(super) predicate: Predicate,
    /// The block control goes to when `predicate` holds.
    pub(super) then_target: usize,
    /// The block control goes to when `predicate` fails.
    pub(super) else_target: usize,
}

impl Decision {
    /// Returns the decision made by the branch of `block` alone, or `None`
    /// if `block` has no branch exit.
    fn leaf(graph: &RegionGraph, block: usize) -> Option<Self> {
        let BlockExit::Branch {
            condition,
            then_edge,
            else_edge,
        } = &graph[block].exit
        else {
            return None;
        };

        Some(Self {
            head: block,
            blocks: [block].into_iter().collect(),
            predicate: Predicate::Value {
                value: *condition,
                block,
            },
            then_target: then_edge.target,
            else_target: else_edge.target,
        })
    }

    /// Returns the same decision with its targets swapped and its predicate
    /// negated.
    #[must_use]
    pub(super) fn inverted(self) -> Self {
        Self {
            predicate: self.predicate.invert(),
            then_target: self.else_target,
            else_target: self.then_target,
            ..self
        }
    }

    /// Merges `next`, which starts at one of the targets, using the target
    /// the two share. Returns `false` and leaves this decision unchanged when
    /// they share none.
    fn merge(&mut self, next: Self) -> bool {
        if next.then_target == next.else_target || next.blocks.contains(self.head) {
            return false;
        }

        // `next` joins with `and` when it starts at the then target and with
        // `or` when it starts at the else target. It is negated when its
        // edges are swapped relative to the shared target.
        let (is_and, negated) = if next.head == self.then_target {
            if next.else_target == self.else_target {
                (true, false)
            } else if next.then_target == self.else_target {
                (true, true)
            } else {
                return false;
            }
        } else if next.head == self.else_target {
            if next.then_target == self.then_target {
                (false, false)
            } else if next.else_target == self.then_target {
                (false, true)
            } else {
                return false;
            }
        } else {
            return false;
        };

        let next = if negated { next.inverted() } else { next };
        let lhs = std::mem::replace(&mut self.predicate, Predicate::True);
        if is_and {
            self.predicate = Predicate::and(lhs, next.predicate);
            self.then_target = next.then_target;
        } else {
            self.predicate = Predicate::or(lhs, next.predicate);
            self.else_target = next.else_target;
        }
        self.blocks.extend(next.blocks);
        true
    }
}

/// Builds [`Decision`]s within the rules of one caller.
pub(super) struct Reducer<'a, F> {
    pub(super) graph: &'a RegionGraph<'a>,
    pub(super) folding: &'a Folding,
    /// The caller's own rule for which condition-only blocks may merge, such
    /// as "inside the loop and not a loop header".
    pub(super) can_merge: F,
}

impl<F: Fn(usize) -> bool> Reducer<'_, F> {
    /// Builds the largest decision that starts at `head`.
    ///
    /// The head only needs a branch exit. Every other block must be
    /// condition-only and accepted by `can_merge`.
    ///
    /// Returns `None` if `head` has no branch exit.
    pub(super) fn build(&self, head: usize) -> Option<Decision> {
        let mut decision = Decision::leaf(self.graph, head)?;
        while self.merge_next(&mut decision) {}
        Some(decision)
    }

    /// Merges the decision that starts at one of the targets, if it shares a
    /// target with `decision`. Returns whether anything merged.
    ///
    /// The target's own branch is tried first, which groups chains from the
    /// left like Luau does, so `a or b or c` is `(a or b) or c`. When that
    /// fails, the whole chain that the target starts is reduced and tried.
    /// That is what turns `a and (b or c)` into one decision.
    fn merge_next(&self, decision: &mut Decision) -> bool {
        // TODO: This is not written very well. Failed merge throws away the
        // full chain, and every later merge builds it again. Real conditions
        // are short enough that this has not mattered yet.

        for target in [decision.then_target, decision.else_target] {
            if !self.can_enter(decision, target) {
                continue;
            }
            let Some(leaf) = Decision::leaf(self.graph, target) else {
                continue;
            };
            if decision.merge(leaf) {
                return true;
            }
            if let Some(chain) = self.build(target)
                && chain.blocks.len() > 1
                && decision.merge(chain)
            {
                return true;
            }
        }

        false
    }

    /// Returns whether the decision at `target` may become part of `decision`.
    ///
    /// This holds when `target` is condition-only, `can_merge` accepts it, and
    /// every edge into it comes from `decision`.
    fn can_enter(&self, decision: &Decision, target: usize) -> bool {
        !decision.blocks.contains(target)
            && self.folding.is_condition_only(target)
            && (self.can_merge)(target)
            && self
                .graph
                .predecessors(target)
                .all(|pred| decision.blocks.contains(pred))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::OnceLock;

    use id_arena::{ArenaBehavior, DefaultArenaBehavior};

    use super::*;
    use crate::ir::fir::{Block, ControlFlowGraph, Edge, Pack, PackId, Value, ValueId};

    /// How one test block leaves.
    enum Exit {
        /// Branches to the first target when the condition holds.
        Branch(usize, usize),
        Jump(usize),
        Return,
    }

    /// Builds a graph where block `i` has `exits[i]`.
    ///
    /// The condition of block `i` is value `i`, so the predicate of a
    /// decision can be checked with [`v`].
    fn graph(exits: &[Exit]) -> ControlFlowGraph<Block> {
        let nodes: Vec<_> = exits
            .iter()
            .enumerate()
            .map(|(index, exit)| {
                let (exit, targets) = match *exit {
                    Exit::Branch(then_target, else_target) => (
                        BlockExit::Branch {
                            condition: value(index),
                            then_edge: Edge::empty(then_target),
                            else_edge: Edge::empty(else_target),
                        },
                        vec![then_target, else_target],
                    ),
                    Exit::Jump(target) => (BlockExit::Jump(Edge::empty(target)), vec![target]),
                    Exit::Return => (BlockExit::Return(pack()), Vec::new()),
                };
                let block = Block {
                    params: Vec::new(),
                    outputs: Vec::new(),
                    instrs: Vec::new(),
                    exit,
                };
                (block, targets)
            })
            .collect();
        ControlFlowGraph::from_nodes_and_exits(nodes)
    }

    /// Returns value `index` of one shared arena, so equal indices compare equal.
    fn value(index: usize) -> ValueId {
        static ARENA: OnceLock<u32> = OnceLock::new();
        let arena = *ARENA.get_or_init(DefaultArenaBehavior::<Value>::new_arena_id);
        DefaultArenaBehavior::<Value>::new_id(arena, index)
    }

    fn pack() -> PackId {
        let arena = DefaultArenaBehavior::<Pack>::new_arena_id();
        DefaultArenaBehavior::<Pack>::new_id(arena, 0)
    }

    /// Returns the predicate that tests the branch of `block`.
    fn v(block: usize) -> Predicate {
        Predicate::Value {
            value: value(block),
            block,
        }
    }

    fn not(predicate: Predicate) -> Predicate {
        predicate.invert()
    }

    fn and(lhs: Predicate, rhs: Predicate) -> Predicate {
        Predicate::and(lhs, rhs)
    }

    fn or(lhs: Predicate, rhs: Predicate) -> Predicate {
        Predicate::or(lhs, rhs)
    }

    /// Builds the decision at block 0, where every branch block is
    /// condition-only and `can_merge` accepts every block.
    fn build(exits: &[Exit]) -> Decision {
        let condition_only = exits
            .iter()
            .enumerate()
            .filter(|(_, exit)| matches!(exit, Exit::Branch(..)))
            .map(|(block, _)| block);
        reduce(exits, condition_only, |_| true).expect("block 0 branches")
    }

    /// Builds the decision at block 0 with the given condition-only blocks
    /// and `can_merge` rule.
    fn reduce(
        exits: &[Exit],
        condition_only: impl IntoIterator<Item = usize>,
        can_merge: impl Fn(usize) -> bool,
    ) -> Option<Decision> {
        let cfg = graph(exits);
        let folding = Folding::with_condition_only(condition_only);
        let reducer = Reducer {
            graph: &RegionGraph::new(&cfg),
            folding: &folding,
            can_merge,
        };
        reducer.build(0)
    }

    fn decision(
        blocks: &[usize],
        predicate: Predicate,
        then_target: usize,
        else_target: usize,
    ) -> Decision {
        Decision {
            head: 0,
            blocks: blocks.iter().copied().collect(),
            predicate,
            then_target,
            else_target,
        }
    }

    /// `a and b` with T = 2 and F = 3.
    #[test]
    fn merges_and() {
        let actual = build(&[
            Exit::Branch(1, 3),
            Exit::Branch(2, 3),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(actual, decision(&[0, 1], and(v(0), v(1)), 2, 3));
    }

    /// `a or b` with T = 2 and F = 3.
    #[test]
    fn merges_or() {
        let actual = build(&[
            Exit::Branch(2, 1),
            Exit::Branch(2, 3),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(actual, decision(&[0, 1], or(v(0), v(1)), 2, 3));
    }

    /// `a and not b` with T = 2 and F = 3.
    #[test]
    fn merges_and_not() {
        let actual = build(&[
            Exit::Branch(1, 3),
            Exit::Branch(3, 2),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(actual, decision(&[0, 1], and(v(0), not(v(1))), 2, 3));
    }

    /// `a or not b` with T = 2 and F = 3.
    #[test]
    fn merges_or_not() {
        let actual = build(&[
            Exit::Branch(2, 1),
            Exit::Branch(3, 2),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(actual, decision(&[0, 1], or(v(0), not(v(1))), 2, 3));
    }

    /// `a and b or c` with T = 3 and F = 4.
    ///
    /// Block 2 has two predecessors, 0 and 1. It merges only after they
    /// became one decision.
    #[test]
    fn merges_and_then_or() {
        let actual = build(&[
            Exit::Branch(1, 2),
            Exit::Branch(3, 2),
            Exit::Branch(3, 4),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(
            actual,
            decision(&[0, 1, 2], or(and(v(0), v(1)), v(2)), 3, 4)
        );
    }

    /// `a and (b or c)` with T = 3 and F = 4.
    ///
    /// `b or c` is reduced first and then merged with `a`.
    #[test]
    fn merges_nested_or() {
        let actual = build(&[
            Exit::Branch(1, 4),
            Exit::Branch(3, 2),
            Exit::Branch(3, 4),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(
            actual,
            decision(&[0, 1, 2], and(v(0), or(v(1), v(2))), 3, 4)
        );
    }

    /// `(a or b) and c` with T = 3 and F = 4.
    #[test]
    fn merges_or_then_and() {
        let actual = build(&[
            Exit::Branch(2, 1),
            Exit::Branch(2, 4),
            Exit::Branch(3, 4),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(
            actual,
            decision(&[0, 1, 2], and(or(v(0), v(1)), v(2)), 3, 4)
        );
    }

    /// `a or b or c` with T = 3 and F = 4.
    #[test]
    fn merges_three_terms() {
        let actual = build(&[
            Exit::Branch(3, 1),
            Exit::Branch(3, 2),
            Exit::Branch(3, 4),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(actual, decision(&[0, 1, 2], or(or(v(0), v(1)), v(2)), 3, 4));
    }

    /// `a and b or c and d` with T = 4 and F = 5.
    #[test]
    fn merges_two_and_terms() {
        let actual = build(&[
            Exit::Branch(1, 2),
            Exit::Branch(4, 2),
            Exit::Branch(3, 5),
            Exit::Branch(4, 5),
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(
            actual,
            decision(&[0, 1, 2, 3], or(and(v(0), v(1)), and(v(2), v(3))), 4, 5)
        );
    }

    /// Block 1 is also reached from block 4, so it is shared code and stays
    /// out of the decision.
    #[test]
    fn stops_at_shared_block() {
        let actual = build(&[
            Exit::Branch(1, 3),
            Exit::Branch(2, 3),
            Exit::Return,
            Exit::Jump(4),
            Exit::Jump(1),
        ]);
        assert_eq!(actual, decision(&[0], v(0), 1, 3));
    }

    /// Block 1 has statements, so it stays out of the decision.
    #[test]
    fn stops_at_block_with_statements() {
        let exits = [
            Exit::Branch(1, 3),
            Exit::Branch(2, 3),
            Exit::Return,
            Exit::Return,
        ];
        let actual = reduce(&exits, [0], |_| true);
        assert_eq!(actual, Some(decision(&[0], v(0), 1, 3)));
    }

    /// Block 1 is condition-only but rejected by `can_merge`, as a loop
    /// header would be.
    #[test]
    fn stops_at_rejected_block() {
        let exits = [
            Exit::Branch(1, 3),
            Exit::Branch(2, 3),
            Exit::Return,
            Exit::Return,
        ];
        let actual = reduce(&exits, [0, 1], |block| block != 1);
        assert_eq!(actual, Some(decision(&[0], v(0), 1, 3)));
    }

    /// Blocks 0 and 1 share no target, so they stay separate.
    #[test]
    fn stops_without_shared_target() {
        let actual = build(&[
            Exit::Branch(1, 4),
            Exit::Branch(2, 3),
            Exit::Return,
            Exit::Return,
            Exit::Return,
        ]);
        assert_eq!(actual, decision(&[0], v(0), 1, 4));
    }

    /// A block without a branch exit starts no decision.
    #[test]
    fn needs_branch_head() {
        assert_eq!(reduce(&[Exit::Jump(1), Exit::Return], [], |_| true), None);
    }
}
