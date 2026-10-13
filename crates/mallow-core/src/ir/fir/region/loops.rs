//! Loop discovery and classification.
//!
//! [`Loops::analyze`] finds every natural loop of the region graph and
//! classifies it once, before structuring starts.
//!
//! # Discovery
//!
//! Every backedge adds its latch and the blocks of its cycle to the
//! [`NaturalLoop`] of its header. Two backedges to the same header give one
//! loop, so directly nested `repeat` loops that share a header become a
//! single loop. See [`natural_loops`].
//!
//! Discovery expects a reducible graph, where any two natural loops are
//! either nested or disjoint. Luau source always compiles to such a graph,
//! because the language has no `goto`.
//!
//! # Classification
//!
//! A loop can fit more than one [`LoopKind`], so the checks run in a fixed
//! order and the first match wins:
//!
//! 1. **Numeric `for`**: the single latch ends in a
//!    [`BlockExit::NumericForLoop`] (`FORNLOOP`) back to the header, and a
//!    predecessor of the header is the matching prep block with a
//!    [`BlockExit::NumericFor`] (`FORNPREP`).
//! 2. **Generic `for`**: the same evidence with
//!    [`BlockExit::GenericForLoop`] (`FORGLOOP`) and
//!    [`BlockExit::GenericFor`] (`FORGPREP`).
//! 3. **`repeat`**: the single latch branches back to the header on one side
//!    and leaves the loop on the other, and
//!    [`Classifier::can_represent_as_repeat_until`] accepts the loop. The
//!    latch's test becomes the `until` condition.
//! 4. **`while`**: the header is condition-only, and its [`Decision`] enters
//!    the body on one side and leaves the loop on the other. That decision is
//!    the guard. See [`Classifier::guard`].
//! 5. **Infinite**: every loop that fits none of the kinds above.
//!
//! The kind fixes the rest of the loop:
//!
//! - The lexical exits. See [`Classifier::lexical_exits`].
//! - The lexical body. It grows from the natural body along every edge until
//!   it reaches a lexical exit. The guard of a `while` loop is then taken out
//!   of it. See [`Classifier::lexical_body`].
//! - The break paths. These are the natural exits that are not lexical exits.
//! - The tails. See [`Classifier::tails`].

use super::decision::{Decision, Reducer};
use super::{Predicate, RegionGraph, single_target};
use crate::collections::{IndexMap, IndexSet};
use crate::ir::fir::folding::Folding;
use crate::ir::fir::{Block, BlockExit, Instr, ValueId};
use crate::ir::graph::{DominatorTree, GraphView};
use crate::logging::{Diagnostics, LogLevel, LogTarget};

/// The cycle of a loop, found from the graph alone.
#[derive(Debug, Clone)]
pub(super) struct NaturalLoop {
    /// The block every backedge jumps to.
    header: usize,
    /// The blocks that jump back to the header.
    latches: IndexSet<usize>,
    /// The header and every block that can reach a latch without passing
    /// through the header.
    pub(super) body: IndexSet<usize>,
    /// Blocks outside the body reached by an edge from inside it.
    exits: IndexSet<usize>,
}

impl NaturalLoop {
    /// Returns the latch if the loop has exactly one.
    fn single_latch(&self) -> Option<usize> {
        single_target(&self.latches)
    }
}

/// A loop as written in the source: its natural loop, its kind, and the
/// blocks the loop syntax covers.
#[derive(Debug, Clone)]
pub(super) struct Loop {
    /// The cycle that proves the loop exists.
    pub(super) natural: NaturalLoop,
    /// Which source loop it is, and where its condition lives.
    pub(super) kind: LoopKind,
    /// Blocks emitted inside the loop: the natural body and every block
    /// reachable from it without crossing a lexical exit, minus the guard of
    /// a `while` loop.
    pub(super) lexical_body: IndexSet<usize>,
    /// Where the source loop ends.
    pub(super) lexical_exits: IndexSet<usize>,
    /// Natural exits that are not lexical exits. They are emitted inside the
    /// loop, followed by a `break`.
    pub(super) break_paths: IndexSet<usize>,
    /// Blocks that end an iteration and still hold body statements.
    ///
    /// See [`Classifier::tails`].
    pub(super) tails: IndexSet<usize>,
}

impl Loop {
    /// Returns the block every backedge jumps to.
    pub(super) const fn header(&self) -> usize {
        self.natural.header
    }

    /// Returns the first block of the body: the guard's then target for
    /// `while`, the header otherwise.
    pub(super) const fn body_entry(&self) -> usize {
        match &self.kind {
            LoopKind::While { guard } => guard.then_target,
            _ => self.header(),
        }
    }

    /// Returns the block that a `continue` jumps to.
    ///
    /// This is the header of a pre-test loop and the latch of a post-test loop.
    pub(super) fn continue_point(&self) -> usize {
        match self.kind {
            LoopKind::While { .. } | LoopKind::Infinite => self.header(),
            LoopKind::RepeatUntil { .. }
            | LoopKind::NumericFor { .. }
            | LoopKind::GenericFor { .. } => self
                .natural
                .single_latch()
                .expect("post-test loops have a single latch"),
        }
    }

    /// Returns whether an edge to `target` is a `continue`.
    ///
    /// That is the case when `target` is the continue point and holds no body
    /// statements. A continue point that is also a tail is reached by falling
    /// through, because its statements still have to run.
    pub(super) fn is_continue(&self, target: usize) -> bool {
        target == self.continue_point() && !self.tails.contains(target)
    }

    /// Returns the latch whose test is the `until` condition, for `repeat` loops.
    pub(super) fn until_latch(&self) -> Option<usize> {
        match self.kind {
            LoopKind::RepeatUntil { .. } => self.natural.single_latch(),
            _ => None,
        }
    }
}

/// Which source loop a natural loop is, and what its syntax needs.
#[derive(Debug, Clone)]
pub(super) enum LoopKind {
    /// `while condition do`: the guard at the header tests the condition.
    While {
        /// The decision at the header. Its then target is the first body
        /// block and its else target is the loop exit.
        guard: Decision,
    },
    /// `repeat ... until condition`: the single latch tests the condition.
    RepeatUntil { condition: Predicate },
    /// `for variable = start, end, step do`
    NumericFor {
        variable: ValueId,
        start: ValueId,
        end: ValueId,
        step: ValueId,
        /// Exit target of the prep block. It can differ from the latch's when
        /// Luau duplicates a return-only exit block (see `Classifier::loop_kind`).
        exit: usize,
    },
    /// `for variables in values do`
    GenericFor {
        variables: Vec<ValueId>,
        values: [ValueId; 3],
    },
    /// `while true do`
    Infinite,
}

/// Every loop of a graph.
#[derive(Debug)]
pub(super) struct Loops(IndexMap<usize, Loop>);

impl Loops {
    /// Finds and classifies every loop of the graph.
    pub(super) fn analyze(
        graph: &RegionGraph,
        ipdoms: &DominatorTree<usize>,
        folding: &Folding,
        diagnostics: &Diagnostics,
    ) -> Self {
        let idoms = graph.build_idoms();
        let naturals = natural_loops(graph, &idoms);
        let classifier = Classifier {
            graph,
            ipdoms,
            folding,
            diagnostics,
            headers: naturals.keys().copied().collect(),
        };
        let loops = naturals
            .into_iter()
            .map(|(header, natural)| (header, classifier.classify(natural)))
            .collect();
        Self(loops)
    }

    /// Returns the loop headed at `header`, if there is one.
    pub(super) fn get(&self, header: usize) -> Option<&Loop> {
        self.0.get(header)
    }
}

/// Finds every natural loop from the backedges of the graph, keyed by header.
///
/// All backedges to one header form a single loop, so loops that share a
/// header, such as directly nested `repeat` loops, are merged into one.
///
/// The loops of a reducible graph are either disjoint or nested, so the
/// natural body of an outer loop already contains every inner loop body.
fn natural_loops(
    graph: &RegionGraph,
    idoms: &DominatorTree<usize>,
) -> IndexMap<usize, NaturalLoop> {
    let reachable: IndexSet<usize> = graph.reverse_post_order().collect();
    let mut loops: IndexMap<usize, NaturalLoop> = IndexMap::default();

    for latch in &reachable {
        for header in graph.successors(latch) {
            if !reachable.contains(header) || !idoms.dominates(header, latch) {
                continue;
            }
            let natural = loops.entry(header).or_insert_with(|| NaturalLoop {
                header,
                latches: IndexSet::default(),
                body: IndexSet::default(),
                exits: IndexSet::default(),
            });
            natural.latches.insert(latch);
            natural
                .body
                .extend(natural_loop_body(graph, header, latch, &reachable));
        }
    }

    for natural in loops.values_mut() {
        natural.exits = natural
            .body
            .iter()
            .flat_map(|block| graph.successors(block))
            .filter(|target| !natural.body.contains(*target))
            .collect();
    }

    debug_assert!(
        loops.values().all(|a| loops.values().all(|b| {
            a.body.is_disjoint(&b.body) || a.body.is_subset(&b.body) || b.body.is_subset(&a.body)
        })),
        "loops must be nested or disjoint. is the CFG reducible?"
    );

    loops
}

/// Read-only view over the analyses that loop classification needs.
struct Classifier<'a> {
    graph: &'a RegionGraph<'a>,
    ipdoms: &'a DominatorTree<usize>,
    folding: &'a Folding,
    diagnostics: &'a Diagnostics,
    /// The header of every loop in the graph.
    headers: IndexSet<usize>,
}

impl Classifier<'_> {
    /// Classifies a natural loop and works out what its source syntax covers.
    fn classify(&self, natural: NaturalLoop) -> Loop {
        let kind = self.loop_kind(&natural);
        let lexical_exits = self.lexical_exits(&natural, &kind);
        let mut lexical_body = self.lexical_body(&natural, &lexical_exits);
        if let LoopKind::While { guard } = &kind {
            for block in &guard.blocks {
                lexical_body.remove(block);
            }
        }

        let lp = Loop {
            break_paths: natural.exits.difference(&lexical_exits),
            tails: self.tails(&natural, &kind),
            natural,
            kind,
            lexical_body,
            lexical_exits,
        };

        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.block("loop:", |trace| {
            trace.line(1, format_args!("header = {}", lp.header()));
            trace.line(1, format_args!("natural_body = {:?}", lp.natural.body));
            trace.line(1, format_args!("lexical_body = {:?}", lp.lexical_body));
            trace.line(1, format_args!("lexical_exits = {:?}", lp.lexical_exits));
            trace.line(1, format_args!("break_paths = {:?}", lp.break_paths));
            trace.line(1, format_args!("continue_point = {}", lp.continue_point()));
            trace.line(1, format_args!("tails = {:?}", lp.tails));
            trace.line(1, format_args!("body_entry = {}", lp.body_entry()));
            trace.line(1, format_args!("until_latch = {:?}", lp.until_latch()));
        });

        lp
    }

    /// Returns the lexical loop body, given the lexical exits.
    ///
    /// The _natural_ body (from [`natural_loop_body`]) proves the cycle exists.
    /// The _lexical_ body is what the source loop actually owns. It starts from
    /// the natural body and expands to include any block reachable from inside
    /// without crossing a lexical exit. This matters when a branch inside the
    /// loop jumps forward to a block that is not part of the cycle but still
    /// executes before the loop exits.
    fn lexical_body(&self, natural: &NaturalLoop, exits: &IndexSet<usize>) -> IndexSet<usize> {
        let mut body = natural.body.clone();
        let mut stack: Vec<_> = body
            .iter()
            .flat_map(|block| self.graph.successors(block))
            .filter(|target| !body.contains(target) && !exits.contains(target))
            .collect();

        while let Some(node) = stack.pop() {
            if exits.contains(node) || !body.insert(node) {
                continue;
            }

            stack.extend(
                self.graph
                    .successors(node)
                    .filter(|target| !body.contains(target) && !exits.contains(target)),
            );
        }

        body
    }

    /// Returns the canonical exit targets for a loop kind.
    ///
    /// These are the first blocks _outside_ the loop that post-loop code lands on.
    /// - For `NumericFor` it is the exit of the prep block.
    /// - For `RepeatUntil` and `GenericFor` it is the non-header successor of
    ///   the single latch.
    /// - For `While` it is the else target of the guard.
    /// - For `Infinite`, it is the common post-dominator of all natural exits if one
    ///   exists, otherwise all natural exits.
    fn lexical_exits(&self, natural: &NaturalLoop, kind: &LoopKind) -> IndexSet<usize> {
        match kind {
            LoopKind::NumericFor { exit, .. } => [*exit].into_iter().collect(),
            LoopKind::RepeatUntil { .. } | LoopKind::GenericFor { .. } => {
                let latch = natural
                    .single_latch()
                    .expect("post-test loops have a single latch");
                self.graph
                    .successors(latch)
                    .filter(|target| *target != natural.header)
                    .collect()
            }
            LoopKind::While { guard } => [guard.else_target].into_iter().collect(),
            LoopKind::Infinite => self.common_loop_follow(natural).map_or_else(
                || natural.exits.clone(),
                |follow| [follow].into_iter().collect(),
            ),
        }
    }

    /// Returns the tails of the loop.
    ///
    /// A tail ends an iteration and still holds body statements, so it is
    /// emitted as part of the body. The tails of a `while` or infinite loop
    /// are its latches other than the header. A `for` loop has its latch as a
    /// tail when the latch has statements. A `repeat` loop has none, because
    /// its latch is the `until` latch.
    fn tails(&self, natural: &NaturalLoop, kind: &LoopKind) -> IndexSet<usize> {
        match kind {
            LoopKind::While { .. } | LoopKind::Infinite => natural
                .latches
                .iter()
                .filter(|latch| *latch != natural.header)
                .collect(),
            LoopKind::NumericFor { .. } | LoopKind::GenericFor { .. }
                if let Some(latch) = natural.single_latch()
                    && !self.graph[latch].instrs.is_empty() =>
            {
                [latch].into_iter().collect()
            }
            _ => IndexSet::default(),
        }
    }

    /// Returns the source syntax of a natural loop, judged by its typed exits
    /// and branch placement.
    fn loop_kind(&self, natural: &NaturalLoop) -> LoopKind {
        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.line(0, format_args!("loop_kind: natural = {:?}", natural));

        if let Some(latch) = natural.single_latch()
            && let BlockExit::NumericForLoop {
                body_edge,
                exit_edge,
            } = &self.graph[latch].exit
            && body_edge.target == natural.header
        {
            let prep_block = self.graph.predecessors(natural.header).find(|&pred| {
                matches!(
                    &self.graph[pred].exit,
                    BlockExit::NumericFor {
                        body_edge: prep_body,
                        exit_edge: prep_exit,
                        ..
                    } if prep_body.target == body_edge.target
                       && (prep_exit.target == exit_edge.target
                           // Luau can duplicate a return-only bytecode block after one
                           // branch on O1 and O2. FORNPREP skips to the shared return
                           // while FORNLOOP falls through to the duplicate return block.
                           //
                           // Dedicated test case: controlflow37.luau
                           || blocks_return_same_values(&self.graph[prep_exit.target], &self.graph[exit_edge.target]))
                )
            });

            if let Some(prep_block) = prep_block
                && let BlockExit::NumericFor {
                    variable,
                    start,
                    end,
                    step,
                    exit_edge,
                    ..
                } = &self.graph[prep_block].exit
            {
                trace.line(1, format_args!("kind = NumericFor"));

                return LoopKind::NumericFor {
                    variable: *variable,
                    start: *start,
                    end: *end,
                    step: *step,
                    exit: exit_edge.target,
                };
            }
        }

        if let Some(latch) = natural.single_latch()
            && let BlockExit::GenericForLoop { body_edge, .. } = &self.graph[latch].exit
            && body_edge.target == natural.header
        {
            let prep_block = self.graph.predecessors(natural.header).find(|&pred| {
                matches!(
                    &self.graph[pred].exit,
                    BlockExit::GenericFor {
                        body_edge: prep_body,
                        loop_block,
                        ..
                    } if prep_body.target == body_edge.target && *loop_block == latch
                )
            });

            if let Some(prep_block) = prep_block
                && let BlockExit::GenericFor {
                    variables, values, ..
                } = &self.graph[prep_block].exit
            {
                trace.line(1, format_args!("kind = GenericFor"));

                return LoopKind::GenericFor {
                    variables: variables.to_vec(),
                    values: *values,
                };
            }
        }

        // If the latch condition has one edge back to the header and one edge out,
        // this is a post-test loop. The latch owns the condition.
        if let Some(latch) = natural.single_latch()
            && let BlockExit::Branch {
                condition,
                then_edge,
                else_edge,
            } = &self.graph[latch].exit
            && (then_edge.target == natural.header) ^ (else_edge.target == natural.header)
        {
            let condition = Predicate::Value {
                value: *condition,
                block: latch,
            };
            let condition = if then_edge.target == natural.header {
                condition.invert()
            } else {
                condition
            };

            let loop_exit = if then_edge.target == natural.header {
                else_edge.target
            } else {
                then_edge.target
            };

            if self.can_represent_as_repeat_until(natural, loop_exit) {
                trace.line(1, format_args!("kind = RepeatUntil({})", condition));
                return LoopKind::RepeatUntil { condition };
            }
        }

        if let Some(guard) = self.guard(natural) {
            trace.line(1, format_args!("kind = While({})", guard.predicate));
            return LoopKind::While { guard };
        }

        trace.line(1, format_args!("kind = Infinite"));
        LoopKind::Infinite
    }

    /// Returns the guard of a `while` loop, if the loop has one.
    ///
    /// The guard is the [`Decision`] at the header when the header is
    /// condition-only and the decision enters the body on one side and leaves
    /// the loop on the other. It may only hold blocks of the natural body
    /// that are neither a loop header nor a latch. The returned guard enters
    /// the body at its then target.
    fn guard(&self, natural: &NaturalLoop) -> Option<Decision> {
        if !self.folding.is_condition_only(natural.header) {
            return None;
        }

        let reducer = Reducer {
            graph: self.graph,
            folding: self.folding,
            can_merge: |block| {
                natural.body.contains(block)
                    && !self.headers.contains(block)
                    && !natural.latches.contains(block)
            },
        };
        let guard = reducer.build(natural.header)?;

        match (
            natural.body.contains(guard.then_target),
            natural.body.contains(guard.else_target),
        ) {
            (true, false) => Some(guard),
            (false, true) => Some(guard.inverted()),
            _ => None,
        }
    }

    /// Returns whether the loop can be represented as a `repeat until` loop.
    ///
    /// `loop_exit` is the target of the latch that leaves the loop. The loop
    /// can be a `repeat` loop when all of these hold:
    /// 1. It has exactly one latch.
    /// 2. Every successor of the header lies in the natural body. A header
    ///    that is also the latch skips this check, because its exit is the
    ///    `until` test itself.
    /// 3. It has exactly one natural exit, or `loop_exit` holds no
    ///    instructions.
    fn can_represent_as_repeat_until(&self, natural: &NaturalLoop, loop_exit: usize) -> bool {
        let Some(latch) = natural.single_latch() else {
            return false;
        };

        if natural.header != latch
            && self
                .graph
                .successors(natural.header)
                .any(|target| !natural.body.contains(target))
        {
            return false;
        }

        if natural.exits.len() == 1 {
            return true;
        }

        self.graph[loop_exit].instrs.is_empty()
    }

    /// Returns the one block where every natural exit of the loop leads, if
    /// there is one.
    ///
    /// An infinite loop has no condition that names its exit, so this block
    /// becomes its lexical exit. The three numbered checks below run in order.
    fn common_loop_follow(&self, natural: &NaturalLoop) -> Option<usize> {
        // 1. The immediate post-dominator of the header, if it lies outside
        // the loop.
        if let Some(follow) = self.ipdoms.idom(natural.header)
            && !natural.body.contains(follow)
        {
            return Some(follow);
        }

        // 2. The nearest block that post-dominates every exit, if it is one
        // of the exits itself.
        if let Some(common) = self.ipdoms.lowest_common_dominator(natural.exits.iter())
            && natural.exits.contains(common)
        {
            return Some(common);
        }

        // 3. The one block outside the loop that every exit jumps to.
        let mut follow = None;
        for exit in &natural.exits {
            let target = single_target(self.graph.successors(exit))?;
            if natural.body.contains(target) {
                return None;
            }

            match follow {
                Some(existing) if existing != target => return None,
                Some(_) => {}
                None => follow = Some(target),
            }
        }

        follow
    }
}

/// Returns the natural loop body of one backedge, including `header`.
///
/// The body is found by walking predecessors back from `latch` until
/// `header` is reached.
fn natural_loop_body(
    graph: &RegionGraph,
    header: usize,
    latch: usize,
    reachable: &IndexSet<usize>,
) -> IndexSet<usize> {
    let mut body = IndexSet::default();
    body.insert(header);

    let mut stack = vec![latch];
    while let Some(node) = stack.pop() {
        if !reachable.contains(node) {
            continue;
        }

        if body.insert(node) {
            for pred in graph.predecessors(node) {
                if reachable.contains(pred) {
                    stack.push(pred);
                }
            }
        }
    }

    body
}

/// Returns whether two blocks only construct and return the same value pack.
fn blocks_return_same_values(left: &Block, right: &Block) -> bool {
    let (
        Block {
            instrs: left_instrs,
            exit: BlockExit::Return(left_return),
            ..
        },
        Block {
            instrs: right_instrs,
            exit: BlockExit::Return(right_return),
            ..
        },
    ) = (left, right)
    else {
        return false;
    };
    let (
        [
            Instr::MakePack {
                out: left_pack,
                head: left_head,
                tail: left_tail,
            },
        ],
        [
            Instr::MakePack {
                out: right_pack,
                head: right_head,
                tail: right_tail,
            },
        ],
    ) = (left_instrs.as_slice(), right_instrs.as_slice())
    else {
        return false;
    };

    left_return == left_pack
        && right_return == right_pack
        && left_head == right_head
        && left_tail == right_tail
}
