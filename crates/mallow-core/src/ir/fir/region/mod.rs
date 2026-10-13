//! Control-flow structuring.
//!
//! Recovers source-level control flow (`if`, `while`, `repeat`, `for`,
//! `break`, `continue`, `return`) from the [control-flow graph](ControlFlowGraph)
//! of one function. The result is a [`Shape`] tree. Its inner nodes are
//! sequences, conditionals and loops. Its leaves are flat, linear blocks and
//! the `break`, `continue` and `return` jumps.
//!
//! # Overview
//!
//! 1. The CFG is viewed as a single-exit graph by tying every returning
//!    block to one virtual exit, which makes post-dominators well defined.
//! 2. Natural loops are discovered from dominator backedges and merged per
//!    header into [`Loops`]. Each loop is then classified once. This fixes
//!    its kind, lexical body, exits and tails before structuring starts.
//!    See [`loops`] for how each kind is recognized.
//! 3. The graph is walked recursively, one [scope](#scopes) at a time. At each block
//!    the structurer first tries to recognize a loop headed there, then a
//!    conditional, and otherwise emits the block and follows its single
//!    in-scope successor. Loop bodies and conditional branches are
//!    structured as nested scopes.
//!
//! Blocks whose instructions all fold into their branch condition (see
//! [`Folding`]) count as having no statements. A chain of such blocks forms
//! one [decision](#conditions), which becomes the `and`/`or` condition of a
//! loop or conditional.
//!
//! Some short-circuit shapes only become visible after NIR inlining and
//! are folded later by `nir::passes::fold_shapes`.
//!
//! # Anatomy of a Loop
//!
//! Prerequisite: a **backedge** is an edge whose target dominates its source.
//!
//! ```text
//! A────►B────►C────►D
//!       ▲     │
//!       └─────┘
//! ```
//!
//! All ways to C go through B. One can easily see how this is equivalent
//! to 'jumping back'.
//!
//! There are a few kinds of loops:
//!
//! | Kind        | Name               | Condition tested at | Latches               |
//! |-------------|--------------------|---------------------|-----------------------|
//! | Pre-test    | While              | header              | body end, `continue`  |
//! | Post-test   | Repeat Until       | latch               | one                   |
//! | Post-test   | Numeric For        | latch (loop instr)  | one                   |
//! | Post-test   | Generic For        | latch (loop instr)  | one                   |
//!
//! **Pre-test loops.** In a normal while loop, the header block is a "guard" that
//! conditionally jumps to the body, or the exit. An infinite loop (`while true`) is a
//! pre-test loop with no guard. The Luau compiler drops the guard because `if not true`
//! can never jump. Because the header owns the condition, there can be multiple latches.
//! One comes from the end of the body, and every other one comes from a `continue`.
//!
//! **Post-test loops.** Post-test loops use headers as regular body blocks, as the condition
//! is owned by the latch. Unlike pre-test loops, there is only one latch. Every `continue` in
//! the loop jumps to the latch on the body's end. For-loops have dedicated instructions that
//! make their discovery very explicit and easy. Specific single block post test loops _can_ have
//! headers that are also the latches.
//!
//! A `repeat` loop needs care, because Luau rejects some of them that read correctly.
//! The `until` condition can see the locals of the body, so the compiler refuses a loop
//! where a `continue` jumps over a local that the condition uses:
//!
//! ```luau
//! repeat
//!     if exits() then continue end
//!     local x = 3
//! until x <= 3
//! -- CompileError: Local x used in the repeat..until condition is undefined
//! -- because continue statement on line 2 jumps over it
//! ```
//!
//! A `for` loop is post-test in the shape of its graph, because its latch tests the
//! condition and every `continue` jumps there. Its body can still run zero times, because
//! the prep block tests the condition once before the first iteration.
//!
//! Both pre and post-test loops can be emitted as infinite loops with an explicit break
//! as a fallback:
//!
//! ```luau
//! -- Pre-test loop
//! while true do
//!     if not {cond} then
//!         break
//!     end
//!     {body}
//! end
//! ```
//!
//! ```luau
//! -- Post-test loop
//! while true do
//!     {body}
//!     if {cond} then
//!         break
//!     end
//! end
//! ```
//!
//! A loop is modeled in two layers:
//!
//! - **Natural**: it's the raw cycle found from a graph alone. It holds the header, the
//!   latches and the body blocks. It's computed by walking "up" through the predecessors
//!   from each latch to the header. See: [NaturalLoop](loops::NaturalLoop), `natural_loop_body`.
//! - **Lexical**: often referred to simply as "loop", it's the loop as written in source,
//!   together with its [kind](loops::LoopKind). Its body is the natural body plus every
//!   block that the loop runs before control leaves it.
//!
//! The natural body can be left in several places, but source code continues after a
//! loop in only one place. The two layers together sort every block around the loop:
//!
//! - A **natural exit** is a block outside the natural body that the body jumps to.
//! - A **lexical exit** is the first block after the loop in the source.
//! - A **break path** is a natural exit that is not a lexical exit. It belongs to the
//!   lexical body and ends with a `break`.
//! - A **tail** is a block that ends an iteration and still holds body statements. Its
//!   final jump back is the loop's implicit continue.
//! - The **continue point** is the block a `continue` jumps to.
//!
//! Consider the following case:
//!
//! ```text
//!       E───────────┐
//!       ▲           │
//!       │           ▼
//! A────►B────►C────►D
//!       ▲     │
//!       └─────┘
//! ```
//!
//! Here B holds statements and then tests `{cond2}`, and the latch C tests `{cond1}`.
//! The graph above _roughly_ resembles such case:
//!
//! ```luau
//! A
//! repeat
//!     B
//!     if {cond2} then
//!         E
//!         break
//!     end
//!     C
//! until not {cond1}
//! D
//! ```
//!
//! The natural body of the loop is {B, C}, because those are the only blocks on
//! the cycle. E never jumps back to B, but in the source it still sits inside the
//! loop, because it runs before the `break`. So the lexical body is {B, C, E}.
//!
//! The loop has two natural exits, E and D. D is the lexical exit, because it is
//! the first block after the loop in the source. E is a break path.
//!
//! # Scopes
//!
//! A [`Scope`] is a part of the graph with one entry block. It owns a set of
//! blocks and stops at a set of exit blocks. The structurer starts at the entry
//! and emits blocks in order until it reaches an exit or a block the scope does
//! not own.
//!
//! The whole function is the first scope. Its only exit is the virtual exit.
//! Nested scopes come from loops and conditionals:
//!
//! - A loop opens one scope for its body. The body scope owns the lexical body
//!   and stops at the lexical exits. The body of a `while` loop also stops at the
//!   header, because a jump back to the guard ends the iteration.
//! - A conditional opens one scope per branch. A branch owns the blocks it
//!   reaches before it meets the follow of the conditional, an exit of the
//!   enclosing scope, or a boundary of the current loop. Those boundaries are the
//!   continue point, the lexical exits and the `until` latch.
//!
//! When a nested scope is done, the enclosing scope goes on at the block after
//! it. That is the lexical exit of a loop, or the follow of a conditional. A loop
//! with several lexical exits, or a conditional with no follow, ends the
//! enclosing scope.
//!
//! # Follows
//!
//! The **follow** of a conditional is the block where its two branches meet
//! again. The code after the `if` starts there. The structurer looks for it in
//! two steps:
//!
//! 1. It takes the nearest post-dominator of the head that lies outside the
//!    decision. Every path from the head to the end of the function passes
//!    through this block, so both branches reach it. It is the follow when the
//!    scope owns it, or when it is the follow of an enclosing conditional.
//! 2. Otherwise it searches the scope for the block that both branches reach
//!    soonest. See [`Structurer::scoped_follow`].
//!
//! The second step matters inside loops. Every path in a loop body goes back to
//! the header or leaves the loop, so the nearest post-dominator of a conditional
//! in the body often lies at the end of the loop or after it. The search inside
//! the scope finds the earlier block where the branches really meet.
//!
//! # Jumps
//!
//! Luau has no `goto`, so every edge in the graph becomes one of four things: the
//! next statement, a `break`, a `continue` or a `return`. Edges inside a scope
//! lead to the next statement. A block that returns becomes a `return`. An edge
//! that leaves the scope takes the first rule that fits:
//!
//! 1. An edge to a follow leads to the next statement, which the enclosing scope
//!    emits.
//! 2. An edge to the continue point becomes a `continue`. A tail at the end of
//!    the loop body is the exception. Its jump back is the implicit continue,
//!    which the loop syntax already expresses. An edge into the `until` latch
//!    also leads to the next statement, because the latch is emitted last in the
//!    body.
//! 3. An edge to a lexical exit of the current loop becomes a `break`.
//! 4. Any other edge leads to the next statement of an enclosing scope.
//!
//! See [`Structurer::structure_block`] and [`Structurer::structure_conditional`].
//!
//! # Glossary
//!
//! ## Loops
//!
//! - **Header**: the target of every backedge of the loop
//! - **Latch**: the source of a backedge. Every loop has at least
//!   one latch. A post-test loop has exactly one.
//! - **Guard**: the [decision](#conditions) at the header of a pre-test
//!   loop. It enters the body or leaves the loop.
//! - **Prep block**: the block just before a `for` loop that sets up variables
//!   for the loop itself.
//! - **Continue point**: the block that a `continue` jumps to. For pre-test loops
//!   it is the header and for post-test loops it is the latch.
//! - **Implicit continue**: the jump at the end of the body.
//! - **Natural body**: a set of blocks reachable by walking from each latch
//!   up to the header.
//! - **Natural exits**: a set of blocks outside the natural body that an edge
//!   from inside the natural body reaches.
//! - **Lexical body**: a set of blocks _included_ in the loop syntactically.
//!   For a `while` loop it leaves out the guard.
//! - **Lexical exits**: a set of blocks that appear right after the loop
//!   syntactically.
//!
//! ## Conditions
//!
//! - **Predicate**: a boolean formula over the branch conditions of blocks,
//!   such as `a and (b or c)`.
//! - **Decision**: one or more condition-only blocks that together choose
//!   between two blocks. Its predicate is true when control goes to the
//!   then target. See [`decision`].
//! - **Follow**: the block where the two branches of a conditional meet again.
//!   See [Follows](#follows).

mod decision;
mod loops;

use std::collections::VecDeque;
use std::fmt;

use anyhow::{Result, ensure};
use either::Either;

use super::folding::Folding;
use super::{Block, BlockExit, ControlFlowGraph, PackId, ValueId};
use crate::collections::{HashMap, IndexSet};
use crate::ir::graph::{DominatorTree, GraphView, Reversed, SeseGraphView};
use crate::logging::{Diagnostics, LogLevel, LogTarget};
use decision::{Decision, Reducer};
use loops::{Loop, LoopKind, Loops};

/// A source condition recovered from control-flow decisions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Predicate {
    /// Tests the branch condition of one block.
    Value {
        /// Condition value tested by the branch.
        value: ValueId,
        /// Block whose exit branches on `value`.
        block: usize,
    },
    /// Always succeeds.
    True,
    /// Always fails.
    False,
    /// Negates one condition.
    Not(Box<Predicate>),
    /// Requires both conditions in source evaluation order.
    And(Box<Predicate>, Box<Predicate>),
    /// Requires either condition in source evaluation order.
    Or(Box<Predicate>, Box<Predicate>),
}

impl Predicate {
    /// Returns the semantic negation of this condition.
    #[must_use]
    fn invert(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Not(inner) => *inner,
            other => Self::Not(Box::new(other)),
        }
    }

    /// Combines two conditions with source-level short-circuit `and`.
    #[must_use]
    fn and(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (Self::False, _) => Self::False,
            (Self::True, rhs) => rhs,
            (lhs, Self::True) => lhs,
            (lhs, rhs) => Self::And(Box::new(lhs), Box::new(rhs)),
        }
    }

    /// Combines two conditions with source-level short-circuit `or`.
    #[must_use]
    fn or(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (Self::True, _) => Self::True,
            (Self::False, rhs) => rhs,
            (lhs, Self::False) => lhs,
            (lhs, rhs) => Self::Or(Box::new(lhs), Box::new(rhs)),
        }
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value { value, .. } => write!(f, "%v{}", value.index()),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Not(inner) => write!(f, "not ({inner})"),
            Self::And(lhs, rhs) => write!(f, "({lhs}) and ({rhs})"),
            Self::Or(lhs, rhs) => write!(f, "({lhs}) or ({rhs})"),
        }
    }
}

/// Structured control flow over blocks in one flat IR function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Shape {
    /// Executes the residual instructions in one basic block.
    Block { block: usize },
    /// Executes child regions in lexical order.
    Sequence { nodes: Vec<Shape> },
    /// Selects one of two lexical branches.
    If {
        /// Condition that selects the branch.
        condition: Predicate,
        /// Shape executed when the condition succeeds.
        then_branch: Box<Shape>,
        /// Shape executed when the condition fails.
        else_branch: Option<Box<Shape>>,
    },
    /// Executes a pre-test loop.
    While {
        /// Loop continuation condition.
        condition: Predicate,
        /// Lexical loop body.
        body: Box<Shape>,
    },
    /// Executes a post-test loop.
    RepeatUntil {
        /// Loop termination condition.
        condition: Predicate,
        /// Lexical loop body.
        body: Box<Shape>,
    },
    /// Executes a numeric `for` loop.
    NumericFor {
        /// Value produced for the loop variable.
        variable: ValueId,
        /// Initial loop value.
        start: ValueId,
        /// Final loop value.
        end: ValueId,
        /// Loop step value.
        step: ValueId,
        /// Lexical loop body.
        body: Box<Shape>,
    },
    /// Executes a generic `for` loop.
    GenericFor {
        /// Values produced for source loop variables.
        variables: Vec<ValueId>,
        /// Iterator, state, and initial control values.
        values: [ValueId; 3],
        /// Lexical loop body.
        body: Box<Shape>,
    },
    /// Starts the next loop iteration.
    Continue,
    /// Leaves the current loop.
    Break,
    /// Returns one IR value pack.
    Return { values: PackId },
}

impl Shape {
    /// Returns a flattened [`Self::Sequence`] from the given iterator.
    fn sequence(nodes: impl IntoIterator<Item = Self>) -> Self {
        let nodes = nodes
            .into_iter()
            .flat_map(|node| match node {
                Self::Sequence { nodes } => Either::Left(nodes.into_iter()),
                other => Either::Right(std::iter::once(other)),
            })
            .collect();
        Self::Sequence { nodes }
    }

    /// Returns `true` if this shape is an empty sequence.
    const fn is_empty(&self) -> bool {
        matches!(self, Self::Sequence { nodes } if nodes.is_empty())
    }
}

/// The CFG boundary currently being structured.
#[derive(Debug, Clone)]
struct Scope<'l> {
    /// First block to emit in this recursive structuring call.
    entry: usize,
    /// Blocks owned by this scope.
    ///
    /// Traversal stays inside this set. A branch entry that is also an exit
    /// target is the one exception, so that its payload still gets structured.
    blocks: IndexSet<usize>,
    /// Blocks where sequencing stops.
    exits: IndexSet<usize>,
    /// Exits that the scope reaches by falling through, such as the follow
    /// of the conditional that this scope is a branch of.
    follows: IndexSet<usize>,
    /// Whether the end of this scope is the tail of its loop.
    ///
    /// This holds for a loop body itself. There, the jump back to the
    /// header is the loop's implicit continue. The loop syntax expresses it,
    /// so it emits no statement. A conditional branch inside the body ends
    /// at the branch follow instead, so the same jump there becomes an
    /// explicit `continue`. Otherwise the other branch would silently inherit
    /// it.
    at_loop_tail: bool,
    /// The loop whose body this scope is part of, if any.
    current_loop: Option<&'l Loop>,
}

impl Scope<'_> {
    /// Returns the latch whose test is the `until` condition of the current loop.
    ///
    /// The latch's statements belong to the body, but its conditional jump is
    /// expressed by the loop syntax, so structuring stops after the latch.
    fn until_latch(&self) -> Option<usize> {
        self.current_loop.and_then(Loop::until_latch)
    }

    /// Returns the blocks where a branch of a conditional in this scope stops.
    ///
    /// These are the scope exits, the conditional's `follow`, the `until`
    /// latch, and the continue point and lexical exits of the current loop.
    fn branch_exits(&self, follow: Option<usize>) -> IndexSet<usize> {
        let mut branch_exits = self.exits.clone();
        if let Some(follow) = follow {
            branch_exits.insert(follow);
        }
        if let Some(block) = self.until_latch() {
            branch_exits.insert(block);
        }
        if let Some(lp) = self.current_loop {
            // Tails other than the continue point stay inside the branch.
            // Their statements are structured there, and only their final
            // jump back is implicit. A `for` latch with statements is both
            // the continue point and a tail, and the branch still owns it as
            // loop payload (see `is_follow_candidate`).
            branch_exits.insert(lp.continue_point());
            branch_exits.extend(lp.lexical_exits.iter());
        }

        branch_exits
    }

    /// Returns whether a decision in this scope may use up `block`.
    ///
    /// The block must belong to this scope and have no other role in it. A
    /// scope exit, a follow, the `until` latch, and the continue point and
    /// break paths of the current loop all stay out.
    fn can_merge(&self, block: usize) -> bool {
        self.blocks.contains(block)
            && !self.exits.contains(block)
            && !self.follows.contains(block)
            && self.until_latch() != Some(block)
            && self
                .current_loop
                .is_none_or(|lp| lp.continue_point() != block && !lp.break_paths.contains(block))
    }

    /// Returns whether `node` can be the follow of a conditional in this scope.
    ///
    /// A follow candidate is a tail or break path of the current loop, or a
    /// block this scope owns that is either the `until` latch or not a branch exit.
    fn is_follow_candidate(&self, node: usize, branch_exits: &IndexSet<usize>) -> bool {
        let is_loop_payload = self
            .current_loop
            .is_some_and(|lp| lp.tails.contains(node) || lp.break_paths.contains(node));

        (self.blocks.contains(node) || is_loop_payload)
            && (!branch_exits.contains(node) || self.until_latch() == Some(node) || is_loop_payload)
    }
}

/// An `if` recognized at one block.
#[derive(Debug, Clone)]
struct Conditional {
    /// Chooses the branch. Its then and else targets are the branch entries.
    decision: Decision,
    /// Block where both branches rejoin, if the scope has one.
    follow: Option<usize>,
}

/// A SESE region graph. Built on top of the control flow graph with its exit
/// nodes tied to a single virtual exit.
struct RegionGraph<'cfg> {
    cfg: &'cfg ControlFlowGraph<Block>,
    leaves: IndexSet<usize>,
}

impl<'cfg> RegionGraph<'cfg> {
    fn new(cfg: &'cfg ControlFlowGraph<Block>) -> Self {
        let leaves = cfg
            .nodes()
            .filter(|&u| cfg.successors(u).next().is_none())
            .collect();
        Self { cfg, leaves }
    }
}

impl GraphView for RegionGraph<'_> {
    type Item = Block;
    type Node = usize;

    fn entry(&self) -> Self::Node {
        self.cfg.entry()
    }

    fn get(&self, node: Self::Node) -> Option<&Self::Item> {
        self.cfg.get(node)
    }

    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        let exit = self.exit();
        if node < exit {
            // real node: its real successors, plus the exit if it's a leaf
            let to_exit = self.leaves.contains(node).then_some(exit);
            Either::Left(self.cfg.successors(node).chain(to_exit))
        } else {
            // exit node: nothing
            Either::Right(std::iter::empty())
        }
    }

    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        let exit = self.exit();
        if node < exit {
            // real node: its real predecessors
            Either::Left(self.cfg.predecessors(node))
        } else {
            // exit node: every leaf
            Either::Right(self.leaves.iter())
        }
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        0..self.len()
    }

    fn items(&self) -> impl Iterator<Item = &Self::Item> {
        self.cfg.items()
    }

    fn contains_node(&self, node: Self::Node) -> bool {
        node < self.len()
    }

    fn len(&self) -> usize {
        self.cfg.len() + 1
    }
}

impl SeseGraphView for RegionGraph<'_> {
    fn exit(&self) -> usize {
        self.cfg.len() // not a real block
    }
}

impl std::ops::Index<usize> for RegionGraph<'_> {
    type Output = Block;
    fn index(&self, index: usize) -> &Self::Output {
        self.cfg.index(index)
    }
}

/// State shared by recursive region recognition.
struct Structurer<'f, 'd> {
    /// SESE graph with one synthetic exit.
    graph: RegionGraph<'f>,
    /// Immediate post-dominators computed through the reversed SESE graph.
    ipdoms: DominatorTree<usize>,
    /// Every loop, classified.
    loops: Loops,
    /// Variable folding analysis.
    folding: &'f Folding,
    /// Diagnostic destination for recognition traces and warnings.
    diagnostics: &'d Diagnostics,
}

impl<'f, 'd> Structurer<'f, 'd> {
    /// Builds all graph analyses required by region recognition.
    fn new(
        cfg: &'f ControlFlowGraph<Block>,
        folding: &'f Folding,
        diagnostics: &'d Diagnostics,
    ) -> Self {
        let graph = RegionGraph::new(cfg);
        let ipdoms = Reversed::new(&graph).build_idoms();
        let loops = Loops::analyze(&graph, &ipdoms, folding, diagnostics);

        Self {
            graph,
            ipdoms,
            loops,
            folding,
            diagnostics,
        }
    }

    /// Recursively structures the region graph into a [`Shape`] tree.
    fn structure(&self) -> Shape {
        let blocks = self.graph.reverse_post_order().collect();
        let exits = [self.graph.exit()].into_iter().collect();
        let scope = Scope {
            entry: self.graph.entry(),
            blocks,
            exits,
            follows: IndexSet::default(),
            at_loop_tail: false,
            current_loop: None,
        };

        self.structure_scope(&scope)
    }

    /// Recursively structures the given scope into a [`Shape`] tree.
    fn structure_scope(&self, scope: &Scope) -> Shape {
        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.block("scope:", |trace| {
            trace.line(1, format_args!("entry = {}", scope.entry));
            trace.line(1, format_args!("blocks = {:?}", scope.blocks));
            trace.line(1, format_args!("exits = {:?}", scope.exits));
            trace.line(1, format_args!("follows = {:?}", scope.follows));
            trace.line(1, format_args!("at_loop_tail = {}", scope.at_loop_tail));
            trace.line(
                1,
                format_args!("current_loop = {:?}", scope.current_loop.map(Loop::header)),
            );
        });

        let mut shapes = Vec::new();
        let mut visited = IndexSet::default();
        let mut current = scope.entry;

        visited.insert(self.graph.exit()); // virtual exit

        while scope.blocks.contains(current)
            && !scope.exits.contains(current)
            && visited.insert(current)
        {
            trace.line(1, format_args!("visit block {}", current));

            if scope.until_latch() == Some(current) {
                trace.line(2, format_args!("block is an `until` latch"));
                shapes.push(Shape::Block { block: current });
                break;
            }

            if let Some(lp) = self.recognize_loop(current, scope) {
                let next = single_target(&lp.lexical_exits);
                trace.line(
                    2,
                    format_args!("recognized loop {:?}, next = {:?}", lp.header(), next),
                );
                shapes.push(self.structure_loop(lp));

                let Some(next) = next else {
                    break;
                };
                if scope.exits.contains(next) {
                    if !scope.at_loop_tail
                        && scope.current_loop.is_some_and(|lp| lp.is_continue(next))
                    {
                        trace.line(
                            2,
                            format_args!("nested loop exits to outer continuation -> continue"),
                        );
                        shapes.push(Shape::Continue);
                    } else if scope
                        .current_loop
                        .is_some_and(|lp| lp.lexical_exits.contains(next))
                    {
                        trace.line(2, format_args!("nested loop exits outer loop -> break"));
                        shapes.push(Shape::Break);
                    }
                    break;
                }
                current = next;
                continue;
            }

            if let Some(conditional) = self.recognize_conditional(current, scope) {
                let follow = conditional.follow;
                let decision = &conditional.decision;
                trace.line(
                    2,
                    format_args!(
                        "recognized conditional: cond = ({}), blocks = {:?}, then = {}, else = {}, follow = {:?}",
                        decision.predicate,
                        decision.blocks,
                        decision.then_target,
                        decision.else_target,
                        follow
                    ),
                );
                if !self.folding.is_condition_only(current) {
                    shapes.push(Shape::Block { block: current });
                }

                shapes.push(self.structure_conditional(conditional, scope));

                let Some(follow) = follow else {
                    break;
                };
                current = follow;
                continue;
            }

            shapes.push(self.structure_block(current, scope));

            let next = self
                .graph
                .successors(current)
                .find(|succ| scope.blocks.contains(succ) || scope.exits.contains(succ));

            let Some(next) = next else {
                trace.line(2, format_args!("no in-scope successor"));
                break;
            };

            if scope.exits.contains(next) {
                trace.line(2, format_args!("next block {} is a scope exit", next));
                break;
            }

            trace.line(2, format_args!("next block = {}", next));
            current = next;
        }

        if scope.blocks.contains(current) && !scope.exits.contains(current) {
            trace.line(
                1,
                format_args!(
                    "stopped at block {} after revisit or terminal stop",
                    current
                ),
            );
        } else {
            trace.line(1, format_args!("stopped before block {}", current));
        }

        Shape::sequence(shapes)
    }

    /// Structures a loop that the enclosing scope contains.
    ///
    /// See: [`Structurer::recognize_loop`]
    fn structure_loop(&self, lp: &Loop) -> Shape {
        let mut exits = lp.lexical_exits.clone();
        if matches!(lp.kind, LoopKind::While { .. }) {
            // The guard is not part of the body, so jumping back to it ends
            // the body and starts the next iteration.
            exits.insert(lp.header());
        }
        let body = Scope {
            entry: lp.body_entry(),
            blocks: lp.lexical_body.clone(),
            exits,
            follows: IndexSet::default(),
            at_loop_tail: true,
            current_loop: Some(lp),
        };
        let body = Box::new(self.structure_scope(&body));

        match &lp.kind {
            LoopKind::While { guard } => Shape::While {
                condition: guard.predicate.clone(),
                body,
            },
            LoopKind::RepeatUntil { condition, .. } => Shape::RepeatUntil {
                condition: condition.clone(),
                body,
            },
            LoopKind::NumericFor {
                variable,
                start,
                end,
                step,
                ..
            } => Shape::NumericFor {
                variable: *variable,
                start: *start,
                end: *end,
                step: *step,
                body,
            },
            LoopKind::GenericFor {
                variables, values, ..
            } => Shape::GenericFor {
                variables: variables.clone(),
                values: *values,
                body,
            },
            LoopKind::Infinite => Shape::While {
                condition: Predicate::True,
                body,
            },
        }
    }

    /// Returns the loop headed at `header` if `scope` contains its whole
    /// natural body.
    ///
    /// The loop the scope is part of is never returned. For some loop kinds
    /// its body starts at the header, which must not start the same loop again.
    fn recognize_loop(&self, header: usize, scope: &Scope) -> Option<&Loop> {
        if scope
            .current_loop
            .is_some_and(|current| current.header() == header)
        {
            return None;
        }
        let lp = self.loops.get(header)?;
        lp.natural.body.is_subset(&scope.blocks).then_some(lp)
    }

    /// Attempts to recognize a conditional at `head` in the given scope.
    ///
    /// This runs after loop recognition. The head only needs a branch exit.
    /// The [`Decision`] at the head may use up further condition-only blocks
    /// that the scope owns, as long as none of them is a loop header.
    fn recognize_conditional(&self, head: usize, scope: &Scope) -> Option<Conditional> {
        let reducer = Reducer {
            graph: &self.graph,
            folding: self.folding,
            can_merge: |block| scope.can_merge(block) && self.loops.get(block).is_none(),
        };
        let decision = reducer.build(head)?;
        let follow = self.find_follow(&decision, scope);

        Some(Conditional { decision, follow })
    }

    /// Finds the follow of the conditional that `decision` chooses.
    ///
    /// The follow is usually the nearest post-dominator of the head outside
    /// the decision. It counts when the scope owns it, or when it is the
    /// follow of an enclosing conditional, because nested conditionals may
    /// rejoin there.
    ///
    /// Otherwise [`Structurer::scoped_follow`] searches for one inside the scope.
    fn find_follow(&self, decision: &Decision, scope: &Scope) -> Option<usize> {
        let mut ipdom = self.ipdoms.idom(decision.head);
        while let Some(block) = ipdom
            && decision.blocks.contains(block)
        {
            ipdom = self.ipdoms.idom(block);
        }

        ipdom
            .filter(|&ipdom| {
                (scope.blocks.contains(ipdom) && !scope.exits.contains(ipdom))
                    || scope.follows.contains(ipdom)
            })
            .or_else(|| self.scoped_follow(decision.then_target, decision.else_target, scope))
    }

    /// Finds the first block inside the scope that both branches reach.
    ///
    /// Infinite loop bodies often post-dominate through the loop latch or
    /// header, so the immediate post-dominator of a conditional can lie past
    /// its lexical end. Searching only within the scope finds the first
    /// common continuation and keeps later sibling statements out of both
    /// branches.
    ///
    /// See [`Structurer::branch_reachable_distances`].
    fn scoped_follow(&self, then_entry: usize, else_entry: usize, scope: &Scope) -> Option<usize> {
        let branch_exits = scope.branch_exits(None);
        let then_reachable = self.branch_reachable_distances(then_entry, scope, &branch_exits);
        let else_reachable = self.branch_reachable_distances(else_entry, scope, &branch_exits);

        then_reachable
            .iter()
            .filter_map(|(&node, &then_distance)| {
                let else_distance = else_reachable.get(&node).copied()?;
                Some((node, then_distance, else_distance))
            })
            .min_by_key(|&(node, then_distance, else_distance)| {
                // Prefer the first layer where both branches can have joined,
                // then the shortest total path through that layer.
                (
                    then_distance.max(else_distance),
                    then_distance + else_distance,
                    node,
                )
            })
            .map(|(node, _, _)| node)
    }

    /// Returns every follow candidate reachable from one conditional branch.
    ///
    /// The search is a scope-bounded breadth-first walk. The returned value maps
    /// each accepted node to the shortest edge distance from `entry`, which lets
    /// [`Structurer::scoped_follow`] choose the earliest common continuation of
    /// the then and else branches.
    fn branch_reachable_distances(
        &self,
        entry: usize,
        scope: &Scope,
        branch_exits: &IndexSet<usize>,
    ) -> HashMap<usize, usize> {
        let mut distances = HashMap::default();
        let mut queue = VecDeque::from([(entry, 0)]);

        while let Some((node, distance)) = queue.pop_front() {
            if distances.contains_key(&node) {
                continue;
            }

            if !scope.is_follow_candidate(node, branch_exits) {
                continue;
            }

            distances.insert(node, distance);

            if branch_exits.contains(node) {
                continue;
            }

            queue.extend(
                self.graph
                    .successors(node)
                    .map(|successor| (successor, distance + 1)),
            );
        }

        distances
    }

    /// Structures a [`Conditional`] into a [`Shape::If`] by recursively
    /// structuring its then and else branches.
    fn structure_conditional(&self, conditional: Conditional, scope: &Scope) -> Shape {
        let branch_exits = scope.branch_exits(conditional.follow);
        let decision = &conditional.decision;

        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.block("conditional:", |trace| {
            trace.line(1, format_args!("head = {}", decision.head));
            trace.line(1, format_args!("then_target = {}", decision.then_target));
            trace.line(1, format_args!("else_target = {}", decision.else_target));
            trace.line(1, format_args!("follow = {:?}", conditional.follow));
            trace.line(1, format_args!("branch_exits = {:?}", branch_exits));
        });

        let owned_boundary_entry = |entry: usize| {
            Some(entry) != conditional.follow
                && scope.until_latch() != Some(entry)
                && !scope.follows.contains(entry)
                && scope
                    .current_loop
                    .is_some_and(|lp| lp.tails.contains(entry) || lp.break_paths.contains(entry))
        };

        let then_blocks = self.collect_reachable_until(
            decision.then_target,
            scope,
            &branch_exits,
            owned_boundary_entry(decision.then_target),
        );
        let else_blocks = self.collect_reachable_until(
            decision.else_target,
            scope,
            &branch_exits,
            owned_boundary_entry(decision.else_target),
        );

        trace.line(1, format_args!("then_blocks = {:?}", then_blocks));
        trace.line(1, format_args!("else_blocks = {:?}", else_blocks));

        let build_branch = |entry: usize, mut blocks: IndexSet<usize>| {
            trace.line(
                1,
                format_args!("build_branch entry = {}, blocks = {:?}", entry, blocks),
            );

            if blocks.is_empty() {
                // If the branch naturally falls through to the follow, it's just empty.
                if Some(entry) == conditional.follow {
                    trace.line(2, format_args!("empty branch falls through to follow"));
                    return Shape::sequence(Vec::new());
                }
                if Some(entry) == scope.until_latch() {
                    trace.line(2, format_args!("empty branch reaches `until` latch"));
                    return Shape::sequence(Vec::new());
                }
                if scope.follows.contains(entry) {
                    trace.line(2, format_args!("empty branch reaches outer follow"));
                    return Shape::sequence(Vec::new());
                }

                // If the branch jumps out of the region entirely, map it to the correct exit instruction.
                if let Some(lp) = scope.current_loop {
                    if lp.is_continue(entry) {
                        trace.line(
                            2,
                            format_args!("empty branch reaches loop continuation -> continue"),
                        );
                        return Shape::Continue;
                    }
                    if lp.lexical_exits.contains(entry) {
                        trace.line(2, format_args!("empty branch exits loop -> break"));
                        return Shape::Break;
                    }
                }

                // An empty branch means the target is a boundary owned by an
                // outer scope.
                //
                // A shared continuation may itself end in Return, but the edge
                // is still an ordinary fallthrough from this branch.
                trace.line(2, format_args!("empty branch reaches outer boundary"));
                return Shape::sequence(Vec::new());
            }

            let owned_payload_exit = scope.current_loop.and_then(|lp| {
                lp.tails
                    .iter()
                    .filter(|payload| {
                        !scope.follows.contains(payload)
                            && (Some(*payload) != conditional.follow
                                || scope.exits.contains(payload))
                    })
                    .find(|payload| {
                        entry == *payload
                            || single_target(self.graph.successors(entry)) == Some(*payload)
                    })
            });
            if let Some(payload) = owned_payload_exit {
                blocks.insert(payload);
            }

            let branch_scope = Scope {
                entry,
                blocks,
                exits: branch_exits
                    .iter()
                    .filter(|exit| *exit != entry && Some(*exit) != owned_payload_exit)
                    .collect(),
                follows: conditional
                    .follow
                    .into_iter()
                    .chain(owned_payload_exit)
                    .collect(),
                at_loop_tail: false,
                current_loop: scope.current_loop,
            };
            self.structure_scope(&branch_scope)
        };

        let then_shape = build_branch(decision.then_target, then_blocks);
        let else_shape = build_branch(decision.else_target, else_blocks);

        Shape::If {
            condition: decision.predicate.clone(),
            then_branch: Box::new(then_shape),
            else_branch: (!else_shape.is_empty()).then(|| Box::new(else_shape)),
        }
    }

    /// Emits one block together with any explicit loop or return transfer.
    fn structure_block(&self, block: usize, scope: &Scope) -> Shape {
        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        let block_shape = Shape::Block { block };

        match &self.graph[block].exit {
            BlockExit::Jump(edge) | BlockExit::Fallthrough(edge)
                if scope.follows.contains(edge.target) =>
            {
                trace.line(
                    2,
                    format_args!("block {} exits to implicit target {}", block, edge.target),
                );
                block_shape
            }
            BlockExit::Jump(edge) | BlockExit::Fallthrough(edge)
                if scope
                    .current_loop
                    .is_some_and(|lp| lp.is_continue(edge.target)) =>
            {
                if scope.until_latch() == Some(edge.target)
                    && self.ipdoms.idom(block) == Some(edge.target)
                {
                    trace.line(
                        2,
                        format_args!("block {} reaches `until` latch {}", block, edge.target),
                    );
                    return block_shape;
                }

                if scope.at_loop_tail
                    && scope
                        .current_loop
                        .is_some_and(|lp| lp.tails.contains(block))
                {
                    trace.line(
                        2,
                        format_args!(
                            "block {} exits through implicit loop tail to {}",
                            block, edge.target
                        ),
                    );
                    return block_shape;
                }

                trace.line(
                    2,
                    format_args!("block {} exits to continue target {}", block, edge.target),
                );
                Shape::sequence([block_shape, Shape::Continue])
            }
            BlockExit::Jump(edge) | BlockExit::Fallthrough(edge)
                if scope
                    .current_loop
                    .is_some_and(|lp| lp.lexical_exits.contains(edge.target)) =>
            {
                trace.line(
                    2,
                    format_args!("block {} exits to break target {}", block, edge.target),
                );
                Shape::sequence([block_shape, Shape::Break])
            }
            BlockExit::Return(values) => {
                Shape::sequence([block_shape, Shape::Return { values: *values }])
            }
            _ => block_shape,
        }
    }

    /// Collects scope-owned blocks reachable before any boundary block.
    fn collect_reachable_until(
        &self,
        entry: usize,
        scope: &Scope,
        exits: &IndexSet<usize>,
        include_boundary_entry: bool,
    ) -> IndexSet<usize> {
        let mut blocks = IndexSet::default();
        let mut stack = vec![entry];

        while let Some(node) = stack.pop() {
            let owns_boundary_entry = include_boundary_entry && node == entry;
            if !scope.blocks.contains(node) && !owns_boundary_entry {
                continue;
            }
            if exits.contains(node) && !owns_boundary_entry {
                continue;
            }
            if !blocks.insert(node) {
                continue;
            }
            if exits.contains(node) {
                continue;
            }

            stack.extend(
                self.graph
                    .successors(node)
                    .filter(|succ| !exits.contains(succ)),
            );
        }

        blocks
    }
}

/// Returns `Some(target)` if `targets` contains exactly one target, otherwise `None`.
fn single_target<T, I: IntoIterator<Item = T>>(targets: I) -> Option<T> {
    let mut targets = targets.into_iter();
    let target = targets.next()?;
    targets.next().is_none().then_some(target)
}

/// Structures one flat IR function without changing its blocks or instructions.
pub(crate) fn structure(
    cfg: &ControlFlowGraph<Block>,
    folding: &Folding,
    diagnostics: &Diagnostics,
) -> Result<Shape> {
    ensure!(cfg.len() > 0, "cannot structure an empty function");

    Ok(Structurer::new(cfg, folding, diagnostics).structure())
}
