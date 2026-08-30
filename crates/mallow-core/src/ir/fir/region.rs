use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use anyhow::{Result, ensure};
use either::Either;

use crate::ir::graph::{DominatorTree, GraphView, Reversed, SeseGraphView, build_graph};
use crate::logging::{Diagnostics, LogLevel, LogTarget};

use super::{Block, BlockExit, Function, Instr, PackId, ValueId};

/// A source condition recovered from control-flow decisions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Predicate {
    /// Tests one immutable IR value.
    Value(ValueId),
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
    /// Continues with one condition selected by another condition.
    Select {
        /// Condition that selects the next decision.
        condition: Box<Predicate>,
        /// Decision used when `condition` succeeds.
        then_predicate: Box<Predicate>,
        /// Decision used when `condition` fails.
        else_predicate: Box<Predicate>,
    },
}

impl Predicate {
    /// Returns the semantic negation of this condition.
    #[inline]
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
    #[inline]
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
    #[inline]
    #[must_use]
    fn or(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (Self::True, _) => Self::True,
            (Self::False, rhs) => rhs,
            (lhs, Self::False) => lhs,
            (lhs, rhs) => Self::Or(Box::new(lhs), Box::new(rhs)),
        }
    }

    /// Preserves one complete conditional decision without duplicating its condition.
    #[inline]
    #[must_use]
    fn select(condition: Self, then_predicate: Self, else_predicate: Self) -> Self {
        match (then_predicate, else_predicate) {
            (Self::True, Self::False) => condition,
            (Self::False, Self::True) => condition.invert(),
            (Self::True, else_predicate) => Self::or(condition, else_predicate),
            (then_predicate, Self::False) => Self::and(condition, then_predicate),
            (Self::False, else_predicate) => Self::and(condition.invert(), else_predicate),
            (then_predicate, Self::True) => Self::or(condition.invert(), then_predicate),
            (then_predicate, else_predicate) => Self::Select {
                condition: Box::new(condition),
                then_predicate: Box::new(then_predicate),
                else_predicate: Box::new(else_predicate),
            },
        }
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(value) => write!(f, "%v{}", value.index()),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Not(inner) => write!(f, "not ({inner})"),
            Self::And(lhs, rhs) => write!(f, "({lhs}) and ({rhs})"),
            Self::Or(lhs, rhs) => write!(f, "({lhs}) or ({rhs})"),
            Self::Select {
                condition,
                then_predicate,
                else_predicate,
            } => write!(
                f,
                "if ({condition}) then ({then_predicate}) else ({else_predicate})"
            ),
        }
    }
}

/// Graph facts derived from one flat IR function.
struct FlowGraph<'a> {
    /// Function whose blocks are being structured.
    function: &'a Function,
    /// Successor blocks for every block.
    successors: Vec<Vec<usize>>,
    /// Predecessor blocks for every block.
    predecessors: Vec<Vec<usize>>,
}

impl<'a> FlowGraph<'a> {
    /// Builds graph facts without changing the flat function.
    fn new(function: &'a Function) -> Self {
        let (successors, predecessors) =
            build_graph(function.blocks.iter().map(|block| block.exit.targets()));
        Self {
            function,
            successors,
            predecessors,
        }
    }

    /// Returns one block and fails loudly for an invalid graph node.
    fn block(&self, block: usize) -> &Block {
        &self.function.blocks[block]
    }

    /// Returns whether a block has instructions that must be materialized.
    ///
    /// Phi instructions describe incoming edges. Every other instruction is
    /// payload until the Shape-to-Region inliner concretely removes it.
    fn block_has_payload(&self, block: usize) -> bool {
        self.block(block)
            .instrs
            .iter()
            .any(|instr| !matches!(instr, Instr::Phi { .. }))
    }

    /// Returns whether two blocks only construct and return the same value pack.
    fn blocks_return_same_values(&self, left: usize, right: usize) -> bool {
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
        ) = (self.block(left), self.block(right))
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
}

impl GraphView for FlowGraph<'_> {
    type Item = Block;
    type Node = usize;

    fn get(&self, node: usize) -> Option<&Self::Item> {
        self.function.blocks.get(node)
    }

    fn entry(&self) -> usize {
        0
    }

    fn successors(&self, node: usize) -> impl Iterator<Item = usize> {
        self.successors[node].iter().copied()
    }

    fn predecessors(&self, node: usize) -> impl Iterator<Item = usize> {
        self.predecessors[node].iter().copied()
    }

    fn contains_node(&self, node: usize) -> bool {
        node < self.function.blocks.len()
    }

    fn nodes(&self) -> impl Iterator<Item = usize> {
        0..self.function.blocks.len()
    }

    fn len(&self) -> usize {
        self.function.blocks.len()
    }
}

/// The lexical control-flow shape recognized from CFG facts.
///
/// This layer intentionally keeps raw block IDs. It describes what the CFG
/// proves without deciding how instructions become AST nodes.
#[derive(Debug, Clone)]
enum RecognizedShape {
    /// A plain basic block id. Means nothing on its own, but is used to identify
    /// a basic block in the CFG.
    Block(usize),
    /// A sequence of sequential shapes.
    Sequence(Vec<RecognizedShape>),
    /// A structured if/else split.
    If(IfShape),
    /// A structured loop split.
    Loop(Box<LoopShape>),
    /// A structured break split.
    Break,
    /// A structured continue split.
    Continue,
    /// A structured return split.
    Return(PackId),
    /// A virtual exit split.
    VirtualExit,
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
    /// Normalizes control shape while FIR block identity is still available.
    fn normalize(self) -> Self {
        let mut current = self.normalize_once();
        loop {
            let next = current.clone().normalize_once();
            if next == current {
                return current;
            }
            current = next;
        }
    }

    /// Performs one bottom-up shape normalization sweep.
    fn normalize_once(self) -> Self {
        match self {
            Self::Sequence { nodes } => Self::sequence(nodes.into_iter().map(Self::normalize_once)),
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let then_branch = then_branch.normalize_once();
                let else_branch = else_branch.map(|branch| Box::new(branch.normalize_once()));
                Self::fold_if(condition, then_branch, else_branch)
            }
            Self::While { condition, body } => Self::While {
                condition,
                body: Box::new(body.normalize_once()),
            },
            Self::RepeatUntil { condition, body } => Self::RepeatUntil {
                condition,
                body: Box::new(body.normalize_once()),
            },
            Self::NumericFor {
                variable,
                start,
                end,
                step,
                body,
            } => Self::NumericFor {
                variable,
                start,
                end,
                step,
                body: Box::new(body.normalize_once()),
            },
            Self::GenericFor {
                variables,
                values,
                body,
            } => Self::GenericFor {
                variables,
                values,
                body: Box::new(body.normalize_once()),
            },
            other => other,
        }
    }

    /// Returns a flat sequence without empty sequence children.
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

    /// Folds one conditional using predicate and branch identity.
    fn fold_if(condition: Predicate, then_branch: Self, else_branch: Option<Box<Self>>) -> Self {
        let then_branch = then_branch.without_single_sequence();
        let else_branch = else_branch.map(|branch| Box::new(branch.without_single_sequence()));

        match condition {
            Predicate::True => return then_branch,
            Predicate::False => {
                return else_branch
                    .map(|branch| *branch)
                    .unwrap_or_else(|| Self::Sequence { nodes: Vec::new() });
            }
            _ => {}
        }

        if let Self::If {
            condition: inner_condition,
            then_branch: inner_then,
            else_branch: inner_else,
        } = then_branch
        {
            if inner_else == else_branch {
                return Self::If {
                    condition: Predicate::and(condition, inner_condition),
                    then_branch: inner_then,
                    else_branch,
                };
            }

            let rebuilt_then = Self::If {
                condition: inner_condition,
                then_branch: inner_then,
                else_branch: inner_else,
            };
            return Self::fold_or(condition, rebuilt_then, else_branch);
        }

        Self::fold_or(condition, then_branch, else_branch)
    }

    /// Removes sequence wrapping from one single child.
    fn without_single_sequence(self) -> Self {
        match self {
            Self::Sequence { mut nodes } if nodes.len() == 1 => nodes.pop().unwrap(),
            other => other,
        }
    }

    /// Folds a shared true payload reached through an `or` chain.
    fn fold_or(condition: Predicate, then_branch: Self, else_branch: Option<Box<Self>>) -> Self {
        let Some(else_branch) = else_branch else {
            return Self::If {
                condition,
                then_branch: Box::new(then_branch),
                else_branch: None,
            };
        };
        let Self::If {
            condition: inner_condition,
            then_branch: inner_then,
            else_branch: inner_else,
        } = *else_branch
        else {
            return Self::If {
                condition,
                then_branch: Box::new(then_branch),
                else_branch: Some(else_branch),
            };
        };

        if *inner_then == then_branch {
            return Self::If {
                condition: Predicate::or(condition, inner_condition),
                then_branch: Box::new(then_branch),
                else_branch: inner_else,
            };
        }

        Self::If {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: Some(Box::new(Self::If {
                condition: inner_condition,
                then_branch: inner_then,
                else_branch: inner_else,
            })),
        }
    }
}

/// Represents an unstructured `if` shape with a condition and then/else branches.
#[derive(Debug, Clone)]
struct IfShape {
    /// The condition expression of the `if` statement.
    condition: Predicate,
    /// Structured payload reached when `condition` is true.
    then_branch: Box<RecognizedShape>,
    /// Structured payload reached when `condition` is false, omitted
    /// when that side has no observable payload.
    else_branch: Option<Box<RecognizedShape>>,
}

/// Loop boundary facts needed while recursively structuring a loop body.
///
/// To make the distinctions concrete, consider a `while` loop where the
/// latch `L` jumps back to the header `H`, and some mid-body block `B`
/// also jumps to `H`:
///
/// - `continue_targets`         = {H, L}  - any in-body edge to these means "next iteration"
/// - `implicit_tail_blocks`     = {L}     - L's backedge is the loop tail - no explicit `continue`
/// - `payload_continue_targets` = {}      - neither H nor L carry statements before the jump
///
/// If instead L had statements before its jump back to H, then:
/// - `payload_continue_targets` = {L}     - L must be emitted as body payload first
#[derive(Debug, Clone)]
struct LoopCtx {
    /// Loop header block. Kept for diagnostics, as the header work is done on [`LoopInfo`].
    header: usize,
    /// In-body CFG targets that mean "start the next iteration".
    continue_targets: HashSet<usize>,
    /// Blocks whose backedge to a continue target are the loop's implicit tail.
    implicit_tail_blocks: HashSet<usize>,
    /// Continue targets that carry statements before the backedge jump and
    /// must be emitted as body payload rather than jumped over.
    payload_continue_targets: HashSet<usize>,
    /// CFG targets immediately outside the loop body.
    exits: HashSet<usize>,
    /// Exit targets that carry statements before reaching the post-loop code;
    /// a branch landing here must emit that payload before the implicit break.
    payload_exit_targets: HashSet<usize>,
}

/// An identifier for a loop, consisting of its header and latch blocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct LoopId {
    /// Dominating loop header reached by the backedge.
    header: usize,
    /// Backedge source block.
    latch: usize,
}

/// Structured loop plus the raw CFG exits used to resume the enclosing scope.
#[derive(Debug, Clone)]
struct LoopShape {
    /// Identifier for the current loop.
    id: LoopId,
    /// The loop kind.
    kind: LoopKind,
    /// Structured loop body.
    body: Box<RecognizedShape>,
    /// Immediate successor blocks outside the natural loop body. A single exit
    /// is the enclosing scope's next block; multiple exits require enclosing
    /// structure to account for them before linear sequencing can continue.
    exits: HashSet<usize>,
}

/// Determines where a recovered loop condition belongs in the source shape.
#[derive(Debug, Clone)]
enum LoopKind {
    /// `while cond do`; condition is owned by the loop header.
    While {
        /// Source-level condition that reaches the loop body when truthy.
        condition: Predicate,
        /// First payload block executed after the guard succeeds.
        body: usize,
        /// Empty conditional blocks consumed into `condition`; these are loop
        /// syntax, not body payload.
        guard_nodes: HashSet<usize>,
        /// Guard leaves reached when the while condition fails.
        exits: HashSet<usize>,
    },
    /// `repeat ... until cond`; condition is owned by the loop latch.
    RepeatUntil {
        condition: Predicate,
        latch: usize,
        body: usize,
    },
    /// for var = start, step, end
    NumericFor {
        variable: ValueId,
        start: ValueId,
        end: ValueId,
        step: ValueId,
        body: usize,
        exit: usize,
    },
    /// for \[vars\] in \[exprs\]
    GenericFor {
        variables: Vec<ValueId>,
        values: [ValueId; 3],
        body: usize,
        exit: usize,
    },
    /// `while true do`; loop exits are represented by `break`.
    Infinite { body: usize },
}

/// Scope parameters for structuring one loop's body, derived from [`LoopKind`]
/// and the lexical body/exit sets.
///
/// Separating these from [`LoopCtx`] keeps a clear responsibility split:
/// [`LoopBodyPlan`] describes *what to traverse* (entry point, available nodes,
/// hard boundaries), while [`LoopCtx`] describes *how to interpret edges* once
/// traversal is running (which targets mean continue, which mean break).
#[derive(Debug, Clone)]
struct LoopBodyPlan {
    /// Loop currently being structured.
    loop_id: LoopId,
    /// First block emitted as body payload.
    entry: usize,
    /// Blocks available to the body scope.
    nodes: HashSet<usize>,
    /// Hard boundaries for the body scope.
    exits: HashSet<usize>,
    /// For post-test (repeat-until) loops: the latch block whose conditional exit
    /// should be suppressed. The latch's statements are emitted as body payload,
    /// only its backedge/exit jump is owned by the loop syntax.
    suppress_exit: Option<usize>,
}

/// The CFG boundary currently being structured.
#[derive(Debug, Clone)]
struct Scope {
    /// First block to emit in this recursive structuring call.
    entry: usize,
    /// Blocks owned by this scope.
    ///
    /// Ordinary traversal should not walk outside this set, but a
    /// branch entry that is also an exit target is still allowed
    /// to be structured so its payload is not lost.
    nodes: HashSet<usize>,
    /// Boundary targets for this scope. These are stop points for sequencing.
    exits: HashSet<usize>,
    /// Exit targets that represent ordinary fallthrough for this scope, such as
    /// the merge block of a structured conditional branch.
    merge_points: HashSet<usize>,
    /// Whether this scope suppresses explicit `continue` for its loop's tail edge.
    ///
    /// In a `while` loop body, the latch's jump back to the header is the loop's
    /// natural tail - it is represented by the `while` syntax itself and emits no
    /// statement. A conditional branch nested inside that body must set this to
    /// `false`: if the then-branch falls through to the latch, that edge must
    /// become an explicit `continue` rather than silent fallthrough, otherwise the
    /// else-branch incorrectly inherits it.
    allow_implicit_continue: bool,
}

#[derive(Debug, Clone)]
struct ConditionalShape {
    /// CFG block whose terminator branches to `then_entry` or `else_entry`.
    head: usize,
    condition: Predicate,
    then_entry: usize,
    else_entry: usize,
    /// In-scope immediate post-dominator where both branches rejoin.
    merge: Option<usize>,
}

/// Natural-loop facts discovered from dominators and backedges.
#[derive(Debug, Clone)]
struct LoopInfo {
    id: LoopId,
    /// Header block of the loop.
    header: usize,
    /// Latch block of the loop.
    latch: usize,
    /// Backedge sources owned by this logical loop.
    ///
    /// Most loops have a single latch, but source-level pre-test loops can have
    /// several body exits that jump back to the same header.
    latches: HashSet<usize>,
    /// Natural loop body collected by walking predecessors from latch to header.
    body: HashSet<usize>,
    /// Successor targets reached by edges leaving the natural cycle body.
    exits: HashSet<usize>,
    /// Smallest containing loop, when loop bodies are nested by containment.
    parent: Option<LoopId>,
    /// Loops directly nested inside this loop.
    children: Vec<LoopId>,
}

#[derive(Debug, Clone)]
struct WhileGuard {
    /// Combined truth condition for all guard paths that reach `body`.
    condition: Predicate,
    /// Unique payload entry reached by the truthy guard paths.
    body: usize,
    /// Empty CFG blocks folded into `condition`.
    guard_nodes: HashSet<usize>,
    /// CFG targets reached by falsy guard paths.
    exits: HashSet<usize>,
}

#[derive(Debug, Clone)]
struct GuardBranch {
    /// Condition under which this branch reaches `body`.
    condition: Predicate,
    /// Payload entry reached by this branch, or `None` for a loop exit branch.
    body: Option<usize>,
    /// Empty CFG blocks folded while following this branch.
    guard_nodes: HashSet<usize>,
    /// Exit targets discovered while following this branch.
    exits: HashSet<usize>,
}

/// Index of all natural loops visible to the region structurer.
///
/// Loop discovery starts from dominator backedges, so one source-level loop can
/// temporarily appear as several [`LoopInfo`] values.
#[derive(Debug, Clone)]
struct LoopForest {
    /// Canonical loop facts keyed by the loop's representative header/latch pair.
    loops: HashMap<LoopId, LoopInfo>,
    /// Header index used during linear scope traversal. Each list is sorted by
    /// increasing body size so callers can deterministically choose the largest
    /// in-scope candidate for a block.
    by_header: HashMap<usize, Vec<LoopId>>,
}

impl LoopForest {
    /// Builds the normalized loop forest from dominator backedges.
    ///
    /// The returned forest has stable body/exits/parent invariants - every
    /// parent body includes all child bodies, exits are computed from those
    /// final bodies, and same-header multi-latch loops are represented by a
    /// single [`LoopInfo`] whose `latches` set records all backedge sources.
    fn build(cfg: &FlowGraph<'_>, idoms: &DominatorTree<usize>) -> Self {
        let mut loops = HashMap::new();
        let mut by_header: HashMap<usize, Vec<LoopId>> = HashMap::new();
        let reachable: HashSet<_> = cfg.reverse_post_order().into_iter().collect();

        for latch in cfg.nodes() {
            if !reachable.contains(&latch) {
                continue;
            }

            for header in cfg.successors(latch) {
                if reachable.contains(&header) && idoms.dominates(header, latch) {
                    let id = LoopId { header, latch };
                    let body = natural_loop_body(cfg, header, latch, &reachable);
                    let exits = body
                        .iter()
                        .flat_map(|&block| cfg.successors(block))
                        .filter(|target| !body.contains(target))
                        .collect();

                    loops.insert(
                        id,
                        LoopInfo {
                            id,
                            header,
                            latch,
                            latches: [latch].into_iter().collect(),
                            body,
                            exits,
                            parent: None,
                            children: Vec::new(),
                        },
                    );
                    by_header.entry(header).or_default().push(id);
                }
            }
        }

        for ids in by_header.values_mut() {
            ids.sort_unstable_by_key(|id| (loops[id].body.len(), *id));
        }

        // Normalize the raw per-backedge loops before deciding which
        // same-header loops must be aggregated. The order is fixed:
        //
        // 1. Recompute exits from the current body sets.
        // 2. Rebuild parent/child links, using body containment first and
        //    same-header exit containment second.
        // 3. Propagate child bodies into parents so a parent scope owns the
        //    entire lexical loop nest.
        // 4. Recompute exits again, because body propagation can turn an edge
        //    to a child block from an exit into an internal edge.
        Self::recompute_exits(cfg, &mut loops);
        Self::rebuild_tree(&mut loops);
        Self::propagate_child_bodies(&mut loops);
        Self::recompute_exits(cfg, &mut loops);

        // The canonical source pattern is a pre-test loop with an explicit `continue`
        // before the normal loop tail:
        //
        // ```luau
        // while cond do
        //     if skip then
        //         continue
        //     end
        //
        //     body()
        // end
        // ```
        //
        // Both the `continue` block and the tail block jump back to the same `while`
        // condition/header, so raw backedge discovery creates one natural loop per
        // latch.
        let aggregate_same_header_loops: Vec<_> = by_header
            .iter()
            .filter_map(|(&header, ids)| {
                if ids.len() < 2 {
                    return None;
                }

                let representative = ids
                    .iter()
                    .copied()
                    .max_by_key(|id| (loops[id].body.len(), *id))?;

                let mut body = HashSet::new();
                let mut latches = HashSet::new();
                for id in ids {
                    body.extend(loops[id].body.iter().copied());
                    latches.extend(loops[id].latches.iter().copied());
                }

                Some((header, representative, ids.clone(), body, latches))
            })
            .collect();

        for (header, representative, merged_ids, body, latches) in aggregate_same_header_loops {
            let info = loops
                .get_mut(&representative)
                .expect("representative loop should exist");
            info.header = header;
            info.latches = latches;
            info.body = body;

            for id in merged_ids {
                if id != representative {
                    loops.remove(&id);
                }
            }
        }

        // Aggregation mutates the representative's body and latches and removes
        // sibling entries, leaving exits and containment stale. The second
        // sequence restores the same invariants as the first.
        Self::recompute_exits(cfg, &mut loops);
        Self::rebuild_tree(&mut loops);
        Self::propagate_child_bodies(&mut loops);
        Self::recompute_exits(cfg, &mut loops);
        let by_header = Self::rebuild_by_header(&loops);

        Self { loops, by_header }
    }

    /// Recomputes each loop's outgoing CFG targets from its current body set.
    ///
    /// This must be run after any operation that changes `LoopInfo::body`,
    /// because exits are consumed both by containment recovery and by loop-kind
    /// classification.
    fn recompute_exits(cfg: &FlowGraph<'_>, loops: &mut HashMap<LoopId, LoopInfo>) {
        for info in loops.values_mut() {
            info.exits = info
                .body
                .iter()
                .flat_map(|&block| cfg.successors(block))
                .filter(|target| !info.body.contains(target))
                .collect();
        }
    }

    /// Rebuilds immediate loop containment relationships.
    ///
    /// The first pass handles ordinary nesting where one natural body is a
    /// strict subset of another. The second pass handles same-header loops that
    /// are not strict body subsets yet still behave as nested raw backedge loops:
    /// if all exits of one same-header loop land inside another same-header
    /// loop, the former is structurally contained by the latter.
    fn rebuild_tree(loops: &mut HashMap<LoopId, LoopInfo>) {
        for info in loops.values_mut() {
            info.parent = None;
            info.children.clear();
        }

        let ids: Vec<_> = loops.keys().copied().collect();
        let parents: Vec<_> = ids
            .iter()
            .copied()
            .filter_map(|id| {
                let loop_body = &loops.get(&id)?.body;
                let parent = ids
                    .iter()
                    .copied()
                    .filter(|&candidate| candidate != id)
                    .filter(|&candidate| {
                        let candidate_body = &loops[&candidate].body;
                        loop_body.len() < candidate_body.len()
                            && loop_body.iter().all(|node| candidate_body.contains(node))
                    })
                    .min_by_key(|candidate| (loops[candidate].body.len(), *candidate))?;

                Some((id, parent))
            })
            .collect();

        for (id, parent) in parents {
            loops.get_mut(&id).expect("child loop should exist").parent = Some(parent);
            loops
                .get_mut(&parent)
                .expect("parent loop should exist")
                .children
                .push(id);
        }

        let ids: Vec<_> = loops.keys().copied().collect();
        let same_header_parents: Vec<_> = ids
            .iter()
            .copied()
            .filter(|id| loops[id].parent.is_none())
            .filter_map(|id| {
                let child = &loops[&id];
                ids.iter()
                    .copied()
                    .filter(|&candidate| candidate != id)
                    .filter(|candidate| loops[candidate].header == child.header)
                    .filter(|candidate| {
                        child
                            .exits
                            .iter()
                            .all(|exit| loops[candidate].body.contains(exit))
                    })
                    .min_by_key(|candidate| (loops[candidate].body.len(), *candidate))
                    .map(|parent| (id, parent))
            })
            .collect();

        for (id, parent) in same_header_parents {
            loops.get_mut(&id).expect("child loop should exist").parent = Some(parent);
            loops
                .get_mut(&parent)
                .expect("parent loop should exist")
                .children
                .push(id);
        }

        for info in loops.values_mut() {
            info.children.sort_unstable();
            info.children.dedup();
        }
    }

    /// Expands each loop's body to include all descendant loop bodies.
    ///
    /// Parent loop's scope during structuring must also own every block in
    /// nested loops so they are not mistaken for external exits. Runs to
    /// fixed point because a grandchild's blocks may not be in a parent until
    /// the intermediate child is processed.
    fn propagate_child_bodies(loops: &mut HashMap<LoopId, LoopInfo>) {
        loop {
            let mut changed = false;
            let ids: Vec<_> = loops.keys().copied().collect();

            for id in ids {
                let children = loops[&id].children.clone();
                let mut child_body = HashSet::new();
                for child in children {
                    child_body.extend(loops[&child].body.iter().copied());
                }

                let info = loops.get_mut(&id).expect("loop should exist");
                let old_len = info.body.len();
                info.body.extend(child_body);
                changed |= info.body.len() != old_len;
            }

            if !changed {
                break;
            }
        }
    }

    /// Rebuilds the header lookup from the normalized loop map.
    ///
    /// This is done at the end instead of incrementally because same-header
    /// aggregation deletes raw loop IDs and may change the representative body
    /// size used for deterministic ordering.
    fn rebuild_by_header(loops: &HashMap<LoopId, LoopInfo>) -> HashMap<usize, Vec<LoopId>> {
        let mut by_header: HashMap<usize, Vec<LoopId>> = HashMap::new();

        for (&id, info) in loops {
            by_header.entry(info.header).or_default().push(id);
        }

        for ids in by_header.values_mut() {
            ids.sort_unstable_by_key(|id| (loops[id].body.len(), *id));
        }

        by_header
    }

    /// Finds the largest loop headed at `header` that the active scope can own.
    ///
    /// `blocked_loop` prevents recursive body structuring from immediately
    /// recognizing the same loop again at its header. The scope containment
    /// check is what lets nested calls ignore loops whose full body belongs to
    /// an outer region.
    fn candidate_in_scope(
        &self,
        header: usize,
        scope: &Scope,
        blocked_loop: Option<LoopId>,
    ) -> Option<&LoopInfo> {
        self.by_header
            .get(&header)?
            .iter()
            .copied()
            .filter(|id| Some(*id) != blocked_loop)
            .filter_map(|id| self.loops.get(&id))
            .filter(|info| info.body.iter().all(|node| scope.nodes.contains(node)))
            .max_by_key(|info| (info.body.len(), info.id))
    }
}

/// A SESE region graph. Built on top of the control flow graph with its exit
/// nodes tied to a single virtual exit.
struct RegionGraph {
    /// Entry block inherited from the flat graph.
    entry: usize,
    /// Synthetic exit reached from every terminal block.
    exit: usize,
    /// RecognizedShape associated with each real or synthetic block.
    nodes: HashMap<usize, RecognizedShape>,
    /// Successor blocks including edges to the synthetic exit.
    successors: HashMap<usize, Vec<usize>>,
    /// Predecessor blocks including terminal blocks at the synthetic exit.
    predecessors: HashMap<usize, Vec<usize>>,
}

impl GraphView for RegionGraph {
    type Item = RecognizedShape;
    type Node = usize;

    fn get(&self, node: usize) -> Option<&Self::Item> {
        self.nodes.get(&node)
    }

    fn entry(&self) -> usize {
        self.entry
    }

    fn successors(&self, node: usize) -> impl Iterator<Item = usize> {
        self.successors.get(&node).into_iter().flatten().copied()
    }

    fn predecessors(&self, node: usize) -> impl Iterator<Item = usize> {
        self.predecessors.get(&node).into_iter().flatten().copied()
    }

    fn contains_node(&self, node: usize) -> bool {
        self.nodes.contains_key(&node)
    }

    fn nodes(&self) -> impl Iterator<Item = usize> {
        self.nodes.keys().copied()
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }
}

impl SeseGraphView for RegionGraph {
    fn exit(&self) -> usize {
        self.exit
    }
}

impl RegionGraph {
    /// Creates a region graph from one flat control-flow graph.
    fn from_cfg(cfg: &FlowGraph<'_>) -> Self {
        let mut nodes: HashMap<_, _> = cfg
            .nodes()
            .map(|i| (i, RecognizedShape::Block(i)))
            .collect();
        let mut successors: HashMap<_, Vec<_>> = cfg
            .nodes()
            .map(|i| (i, cfg.successors(i).collect()))
            .collect();
        let mut predecessors: HashMap<_, Vec<_>> = cfg
            .nodes()
            .map(|i| (i, cfg.predecessors(i).collect()))
            .collect();

        let terminal_nodes: Vec<_> = nodes
            .keys()
            .copied()
            .filter(|&id| successors.get(&id).is_none_or(|s| s.is_empty()))
            .collect();

        let virtual_exit = usize::MAX;
        nodes.insert(virtual_exit, RecognizedShape::VirtualExit);

        for node in terminal_nodes {
            successors.entry(node).or_default().push(virtual_exit);
            predecessors.entry(virtual_exit).or_default().push(node);
        }

        successors.insert(virtual_exit, Vec::new());

        Self {
            entry: cfg.entry(),
            exit: virtual_exit,
            nodes,
            successors,
            predecessors,
        }
    }
}

/// State shared by recursive region recognition.
struct Structurer<'cfg, 'd> {
    /// Flat graph that owns executable block facts.
    cfg: &'cfg FlowGraph<'cfg>,
    /// SESE graph with one synthetic exit.
    graph: RegionGraph,
    /// Immediate post-dominators computed through the reversed SESE graph.
    ipdoms: DominatorTree<usize>,
    /// Natural loops and their lexical containment.
    loops: LoopForest,
    /// Diagnostic destination for recognition traces and warnings.
    diagnostics: &'d Diagnostics,
}

impl<'cfg, 'd> Structurer<'cfg, 'd> {
    /// Builds all graph analyses required by region recognition.
    fn new(cfg: &'cfg FlowGraph<'cfg>, diagnostics: &'d Diagnostics) -> Self {
        let graph = RegionGraph::from_cfg(cfg);
        let ipdoms = Reversed::new(&graph).build_idoms();

        let idoms = graph.build_idoms();
        let loops = LoopForest::build(cfg, &idoms);

        Self {
            cfg,
            graph,
            ipdoms,
            loops,
            diagnostics,
        }
    }

    /// Recursively structures the region graph into a [`RecognizedShape`] tree.
    fn structure(&self) -> RecognizedShape {
        let nodes = self.graph.reverse_post_order().into_iter().collect();
        let exits = [self.graph.exit()].into_iter().collect();
        let scope = Scope {
            entry: self.graph.entry(),
            nodes,
            exits,
            merge_points: HashSet::new(),
            allow_implicit_continue: false,
        };

        self.structure_scope(&scope, None, None, None)
    }

    /// Recursively structures the given scope into a [`RecognizedShape`] tree.
    fn structure_scope(
        &self,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
        blocked_loop: Option<LoopId>,
    ) -> RecognizedShape {
        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.block("scope:", |trace| {
            trace.line(1, format_args!("entry = {}", scope.entry));
            trace.line(1, format_args!("nodes = {:?}", sorted_nodes(&scope.nodes)));
            trace.line(1, format_args!("exits = {:?}", sorted_nodes(&scope.exits)));
            trace.line(
                1,
                format_args!("merge_points = {:?}", sorted_nodes(&scope.merge_points)),
            );
            trace.line(
                1,
                format_args!(
                    "allow_implicit_continue = {}",
                    scope.allow_implicit_continue
                ),
            );
            trace.line(1, format_args!("suppress_exit = {:?}", suppress_exit));
            trace.line(1, format_args!("blocked_loop = {:?}", blocked_loop));
            if let Some(ctx) = loop_ctx {
                trace.line(1, format_args!("loop_ctx.header = {}", ctx.header));
                trace.line(
                    1,
                    format_args!(
                        "loop_ctx.continue_targets = {:?}",
                        sorted_nodes(&ctx.continue_targets)
                    ),
                );
                trace.line(
                    1,
                    format_args!(
                        "loop_ctx.implicit_tail_blocks = {:?}",
                        sorted_nodes(&ctx.implicit_tail_blocks)
                    ),
                );
                trace.line(
                    1,
                    format_args!("loop_ctx.exits = {:?}", sorted_nodes(&ctx.exits)),
                );
            }
        });

        let mut nodes = Vec::new();
        let mut visited = HashSet::new();
        let mut current = scope.entry;

        visited.insert(usize::MAX); // virtual exit

        while scope.nodes.contains(&current)
            && !scope.exits.contains(&current)
            && visited.insert(current)
        {
            trace.line(1, format_args!("visit block {}", current));

            if suppress_exit == Some(current) {
                trace.line(2, format_args!("block is suppressed"));
                nodes.push(RecognizedShape::Block(current));
                break;
            }

            if let Some(loop_shape) = self.recognize_loop(current, scope, blocked_loop) {
                let next = single_target(&loop_shape.exits).copied();
                trace.line(
                    2,
                    format_args!("recognized loop {:?}, next = {:?}", loop_shape.id, next),
                );
                nodes.push(RecognizedShape::Loop(Box::new(loop_shape)));

                let Some(next) = next else {
                    break;
                };
                if scope.exits.contains(&next) {
                    if !scope.allow_implicit_continue
                        && loop_ctx.is_some_and(|ctx| {
                            ctx.continue_targets.contains(&next)
                                && !ctx.payload_continue_targets.contains(&next)
                        })
                    {
                        trace.line(
                            2,
                            format_args!("nested loop exits to outer continuation -> continue"),
                        );
                        nodes.push(RecognizedShape::Continue);
                    } else if loop_ctx.is_some_and(|ctx| ctx.exits.contains(&next)) {
                        trace.line(2, format_args!("nested loop exits outer loop -> break"));
                        nodes.push(RecognizedShape::Break);
                    }
                    break;
                }
                current = next;
                continue;
            }

            if let Some(conditional) =
                self.recognize_conditional(current, scope, loop_ctx, suppress_exit)
            {
                let merge = conditional.merge;
                trace.line(
                    2,
                    format_args!(
                        "recognized conditional: cond = ({}), then = {}, else = {}, merge = {:?}",
                        conditional.condition,
                        conditional.then_entry,
                        conditional.else_entry,
                        merge
                    ),
                );
                if self.cfg.block_has_payload(current) {
                    nodes.push(RecognizedShape::Block(current));
                }

                nodes.push(self.structure_conditional(
                    conditional,
                    scope,
                    loop_ctx,
                    suppress_exit,
                    blocked_loop,
                ));

                let Some(merge) = merge else {
                    break;
                };
                current = merge;
                continue;
            }

            nodes.push(self.shape_for_block(current, scope, loop_ctx, suppress_exit));

            let next = self
                .graph
                .successors(current)
                .find(|succ| scope.nodes.contains(succ) || scope.exits.contains(succ));

            let Some(next) = next else {
                trace.line(2, format_args!("no in-scope successor"));
                break;
            };

            if scope.exits.contains(&next) {
                trace.line(2, format_args!("next block {} is a scope exit", next));
                break;
            }

            trace.line(2, format_args!("next block = {}", next));
            current = next;
        }

        if scope.nodes.contains(&current) && !scope.exits.contains(&current) {
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

        RecognizedShape::sequence(nodes)
    }

    /// Attempts to recognize a loop shape by its header and scope.
    ///
    /// See: [`LoopForest::candidate_in_scope`]
    fn recognize_loop(
        &self,
        header: usize,
        scope: &Scope,
        blocked_loop: Option<LoopId>,
    ) -> Option<LoopShape> {
        let loop_info = self.loops.candidate_in_scope(header, scope, blocked_loop)?;
        let kind = self.classify_loop(loop_info);
        let (lexical_body, lexical_exits) = self.lexical_loop_body(loop_info, &kind);

        if blocked_loop.is_some_and(|blocked| {
            blocked.header == loop_info.header && lexical_body.contains(&blocked.latch)
        }) {
            self.diagnostics
                .at(LogLevel::Trace, LogTarget::Region)
                .line(
                    2,
                    format_args!(
                        "skip same-header loop {:?}: body would re-enter blocked loop {:?}",
                        loop_info.id, blocked_loop
                    ),
                );
            return None;
        }

        let body_plan = self.plan_loop_body(
            loop_info,
            &kind,
            lexical_body.clone(),
            lexical_exits.clone(),
        );

        let loop_ctx = LoopCtx {
            header,
            continue_targets: self.continue_targets(loop_info, &kind),
            implicit_tail_blocks: self.implicit_tail_blocks(loop_info, &kind),
            payload_continue_targets: self.payload_continue_targets(loop_info, &kind),
            exits: lexical_exits.clone(),
            payload_exit_targets: self.payload_exit_targets(loop_info, &lexical_exits),
        };

        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.block("loop:", |trace| {
            trace.line(1, format_args!("id = {:?}", loop_info.id));
            trace.line(1, format_args!("header = {}", header));
            trace.line(
                1,
                format_args!("natural_body = {:?}", sorted_nodes(&loop_info.body)),
            );
            trace.line(
                1,
                format_args!("body = {:?}", sorted_nodes(&body_plan.nodes)),
            );
            trace.line(
                1,
                format_args!("exits = {:?}", sorted_nodes(&lexical_exits)),
            );
            trace.line(
                1,
                format_args!(
                    "payload_exit_targets = {:?}",
                    sorted_nodes(&loop_ctx.payload_exit_targets)
                ),
            );
            trace.line(
                1,
                format_args!(
                    "continue_targets = {:?}",
                    sorted_nodes(&loop_ctx.continue_targets)
                ),
            );
            trace.line(
                1,
                format_args!(
                    "implicit_tail_blocks = {:?}",
                    sorted_nodes(&loop_ctx.implicit_tail_blocks)
                ),
            );
            trace.line(
                1,
                format_args!(
                    "payload_continue_targets = {:?}",
                    sorted_nodes(&loop_ctx.payload_continue_targets)
                ),
            );
            trace.line(1, format_args!("body_entry = {}", body_plan.entry));
            trace.line(
                1,
                format_args!("body_suppress_exit = {:?}", body_plan.suppress_exit),
            );
        });

        Some(LoopShape {
            id: loop_info.id,
            kind,
            body: Box::new(self.structure_loop_body(&body_plan, &loop_ctx)),
            exits: lexical_exits,
        })
    }

    /// Translates loop kind into a body traversal plan.
    ///
    /// - For `While`, guard nodes are removed from `nodes` (they became the
    ///   condition expression, not statements) and the header is added to `exits`
    ///   so an in-body jump back to it is recognized as a continue boundary.
    /// - For `RepeatUntil`, the latch is suppressed so its statements are emitted
    ///   before the loop syntax claims the conditional exit.
    ///
    /// All other kinds pass the lexical body through unchanged.
    fn plan_loop_body(
        &self,
        loop_info: &LoopInfo,
        kind: &LoopKind,
        lexical_body: HashSet<usize>,
        lexical_exits: HashSet<usize>,
    ) -> LoopBodyPlan {
        match kind {
            LoopKind::While {
                body, guard_nodes, ..
            } => {
                let mut nodes = lexical_body;
                for guard in guard_nodes {
                    nodes.remove(guard);
                }

                LoopBodyPlan {
                    loop_id: loop_info.id,
                    entry: *body,
                    nodes,
                    exits: [loop_info.header]
                        .into_iter()
                        .chain(lexical_exits.iter().copied())
                        .collect(),
                    suppress_exit: None,
                }
            }
            LoopKind::Infinite { body } => LoopBodyPlan {
                loop_id: loop_info.id,
                entry: *body,
                nodes: lexical_body,
                exits: lexical_exits,
                suppress_exit: None,
            },
            LoopKind::RepeatUntil { latch, body, .. } => LoopBodyPlan {
                loop_id: loop_info.id,
                entry: *body,
                nodes: lexical_body,
                exits: lexical_exits,
                suppress_exit: Some(*latch),
            },
            LoopKind::NumericFor { body, .. } | LoopKind::GenericFor { body, .. } => LoopBodyPlan {
                loop_id: loop_info.id,
                entry: *body,
                nodes: lexical_body,
                exits: lexical_exits,
                suppress_exit: None,
            },
        }
    }

    /// Returns the lexical loop body and exits for a given loop kind.
    ///
    /// The *natural* body (from [`natural_loop_body`]) proves the cycle exists.
    /// The *lexical* body is what the source loop actually owns - it starts from
    /// the natural body and expands to include any block reachable from inside
    /// without crossing a lexical exit. This matters when a branch inside the
    /// loop jumps forward to a block that is not part of the cycle but still
    /// executes before the loop exits.
    fn lexical_loop_body(
        &self,
        loop_info: &LoopInfo,
        kind: &LoopKind,
    ) -> (HashSet<usize>, HashSet<usize>) {
        let exits = self.lexical_loop_exits(loop_info, kind);
        let mut body = loop_info.body.clone();
        let mut stack: Vec<_> = body
            .iter()
            .flat_map(|&block| self.graph.successors(block))
            .filter(|target| !body.contains(target) && !exits.contains(target))
            .collect();

        while let Some(node) = stack.pop() {
            if exits.contains(&node) || !body.insert(node) {
                continue;
            }

            stack.extend(
                self.graph
                    .successors(node)
                    .filter(|target| !body.contains(target) && !exits.contains(target)),
            );
        }

        (body, exits)
    }

    /// Returns the canonical exit targets for a loop kind.
    ///
    /// These are the first blocks *outside* the loop that post-loop code lands on.
    /// - For typed loops (`NumericFor`, `GenericFor`) the exit is fixed by the loop
    ///   instruction.
    /// - For `RepeatUntil` it is the non-header successor of the latch.
    /// - For `While` it comes from the guard analysis.
    /// - For `Infinite`, it is the common post-dominator of all natural exits if one
    ///   exists, otherwise all natural exits.
    fn lexical_loop_exits(&self, loop_info: &LoopInfo, kind: &LoopKind) -> HashSet<usize> {
        match kind {
            LoopKind::NumericFor { exit, .. } | LoopKind::GenericFor { exit, .. } => {
                [*exit].into_iter().collect()
            }
            LoopKind::RepeatUntil { latch, .. } => self
                .graph
                .successors(*latch)
                .filter(|target| *target != loop_info.header)
                .collect(),
            LoopKind::While { exits, .. } => exits.clone(),
            LoopKind::Infinite { .. } => self.common_loop_follow(loop_info).map_or_else(
                || loop_info.exits.clone(),
                |follow| [follow].into_iter().collect(),
            ),
        }
    }

    /// Structures the loop body using the given plan and loop context.
    ///
    /// See: [`Structurer::structure_scope`]
    fn structure_loop_body(&self, plan: &LoopBodyPlan, loop_ctx: &LoopCtx) -> RecognizedShape {
        let scope = Scope {
            entry: plan.entry,
            nodes: plan.nodes.clone(),
            exits: plan.exits.clone(),
            merge_points: HashSet::new(),
            allow_implicit_continue: true,
        };

        self.structure_scope(
            &scope,
            Some(loop_ctx),
            plan.suppress_exit,
            Some(plan.loop_id),
        )
    }

    /// Returns the set of continue targets for the loop.
    ///
    /// For all kinds of loops, these are the loop latches.
    fn continue_targets(&self, loop_info: &LoopInfo, kind: &LoopKind) -> HashSet<usize> {
        match kind {
            LoopKind::While { .. } | LoopKind::Infinite { .. } => [loop_info.header]
                .into_iter()
                .chain(loop_info.latches.iter().copied())
                .collect(),
            LoopKind::RepeatUntil { .. }
            | LoopKind::NumericFor { .. }
            | LoopKind::GenericFor { .. } => [loop_info.latch].into_iter().collect(),
        }
    }

    /// Returns the set of implicit tail blocks for the loop body.
    ///
    /// Only [`LoopKind::While`] and [`LoopKind::Infinite`] have such -
    /// those are all the latches that are not the loop header.
    fn implicit_tail_blocks(&self, loop_info: &LoopInfo, kind: &LoopKind) -> HashSet<usize> {
        match kind {
            LoopKind::While { .. } | LoopKind::Infinite { .. } => loop_info
                .latches
                .iter()
                .copied()
                .filter(|latch| *latch != loop_info.header)
                .collect(),
            _ => HashSet::new(),
        }
    }

    /// Returns the set of payload exit targets for the loop body.
    fn payload_exit_targets(
        &self,
        loop_info: &LoopInfo,
        lexical_exits: &HashSet<usize>,
    ) -> HashSet<usize> {
        loop_info.exits.difference(lexical_exits).copied().collect()
    }

    /// Returns the set of payload continue targets for the loop body.
    ///
    /// - For a while/infinite loop, the continue targets are the loop latches
    ///   excluding the loop header.
    /// - For a repeat-until loop, the latch is a continue target, but not a
    ///   payload continue target - the latch's statements are emitted as the
    ///   body's terminal payload while its conditional backedge is suppressed and
    ///   represented by the `until` condition itself.
    /// - For a numeric/generic for loop, there is only one continue target,
    ///   the loop latch (given it is not empty.)
    fn payload_continue_targets(&self, loop_info: &LoopInfo, kind: &LoopKind) -> HashSet<usize> {
        match kind {
            LoopKind::While { .. } | LoopKind::Infinite { .. } => loop_info
                .latches
                .iter()
                .copied()
                .filter(|latch| *latch != loop_info.header)
                .collect(),
            LoopKind::NumericFor { .. } | LoopKind::GenericFor { .. }
                if self.cfg.block_has_payload(loop_info.latch) =>
            {
                [loop_info.latch].into_iter().collect()
            }
            _ => HashSet::new(),
        }
    }

    /// Attempts to recognize a conditional block at `head` in the given scope.
    ///
    /// This runs after loop recognition. The head only needs a branch exit.
    fn recognize_conditional(
        &self,
        head: usize,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
    ) -> Option<ConditionalShape> {
        let BlockExit::Branch {
            condition,
            then_block,
            else_block,
        } = &self.cfg.block(head).exit
        else {
            return None;
        };

        Some(ConditionalShape {
            head,
            condition: Predicate::Value(*condition),
            then_entry: *then_block,
            else_entry: *else_block,
            merge: self.find_merge_point(head, scope).or_else(|| {
                self.scoped_branch_merge(*then_block, *else_block, scope, loop_ctx, suppress_exit)
            }),
        })
    }

    /// Finds a local branch merge when full-graph postdominators are too coarse.
    ///
    /// Infinite loop bodies often postdominate through the loop latch/header, so
    /// the global immediate postdominator can miss the lexical continuation of a
    /// conditional. Searching only within the active scope recovers the first
    /// common continuation without pulling later sibling statements into both
    /// branches.
    ///
    /// See [`Structurer::branch_reachable_distances`].
    fn scoped_branch_merge(
        &self,
        then_entry: usize,
        else_entry: usize,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
    ) -> Option<usize> {
        let branch_exits = conditional_branch_exits(scope, loop_ctx, suppress_exit, None);
        let then_reachable = self.branch_reachable_distances(
            then_entry,
            scope,
            &branch_exits,
            loop_ctx,
            suppress_exit,
        );
        let else_reachable = self.branch_reachable_distances(
            else_entry,
            scope,
            &branch_exits,
            loop_ctx,
            suppress_exit,
        );

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

    /// Returns every candidate merge node reachable from one conditional branch.
    ///
    /// The search is a scope-bounded breadth-first walk. The returned value maps
    /// each accepted node to the shortest edge distance from `entry`, which lets
    /// [`Structurer::scoped_branch_merge`] choose the earliest common continuation between
    /// the then/else branches.
    fn branch_reachable_distances(
        &self,
        entry: usize,
        scope: &Scope,
        branch_exits: &HashSet<usize>,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
    ) -> HashMap<usize, usize> {
        let mut distances = HashMap::new();
        let mut queue = VecDeque::from([(entry, 0)]);

        while let Some((node, distance)) = queue.pop_front() {
            if distances.contains_key(&node) {
                continue;
            }

            if !self.is_scoped_merge_candidate(node, scope, branch_exits, loop_ctx, suppress_exit) {
                continue;
            }

            distances.insert(node, distance);

            if branch_exits.contains(&node) {
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

    /// Returns whether a node is a scoped merge candidate within the given scope.
    ///
    /// A scoped merge candidate is a node that is either owned by the scope or
    /// is a loop payload (continue/exit target).
    fn is_scoped_merge_candidate(
        &self,
        node: usize,
        scope: &Scope,
        branch_exits: &HashSet<usize>,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
    ) -> bool {
        let is_loop_payload = loop_ctx.is_some_and(|ctx| {
            ctx.payload_continue_targets.contains(&node) || ctx.payload_exit_targets.contains(&node)
        });

        (scope.nodes.contains(&node) || is_loop_payload)
            && (!branch_exits.contains(&node) || suppress_exit == Some(node) || is_loop_payload)
    }

    /// Structures a [`ConditionalShape`] into a [`RecognizedShape`] by recursively structuring
    /// the then/else branches and merging them together.
    fn structure_conditional(
        &self,
        shape: ConditionalShape,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
        blocked_loop: Option<LoopId>,
    ) -> RecognizedShape {
        let branch_exits = conditional_branch_exits(scope, loop_ctx, suppress_exit, shape.merge);

        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.block("conditional:", |trace| {
            trace.line(1, format_args!("head = {}", shape.head));
            trace.line(1, format_args!("then_entry = {}", shape.then_entry));
            trace.line(1, format_args!("else_entry = {}", shape.else_entry));
            trace.line(1, format_args!("merge = {:?}", shape.merge));
            trace.line(
                1,
                format_args!("branch_exits = {:?}", sorted_nodes(&branch_exits)),
            );
        });

        let owned_boundary_entry = |entry: usize| {
            Some(entry) != shape.merge
                && suppress_exit != Some(entry)
                && !scope.merge_points.contains(&entry)
                && loop_ctx.is_some_and(|ctx| {
                    ctx.payload_continue_targets.contains(&entry)
                        || ctx.payload_exit_targets.contains(&entry)
                })
        };

        let then_nodes = self.collect_reachable_until(
            shape.then_entry,
            scope,
            &branch_exits,
            owned_boundary_entry(shape.then_entry),
        );
        let else_nodes = self.collect_reachable_until(
            shape.else_entry,
            scope,
            &branch_exits,
            owned_boundary_entry(shape.else_entry),
        );

        trace.line(
            1,
            format_args!("then_nodes = {:?}", sorted_nodes(&then_nodes)),
        );
        trace.line(
            1,
            format_args!("else_nodes = {:?}", sorted_nodes(&else_nodes)),
        );

        let build_branch = |entry: usize, mut nodes: HashSet<usize>| {
            trace.line(
                1,
                format_args!(
                    "build_branch entry = {}, nodes = {:?}",
                    entry,
                    sorted_nodes(&nodes)
                ),
            );

            if nodes.is_empty() {
                // If the branch naturally falls through to the merge point, it's just empty.
                if Some(entry) == shape.merge {
                    trace.line(2, format_args!("empty branch falls through to merge"));
                    return RecognizedShape::sequence(Vec::new());
                }
                if Some(entry) == suppress_exit {
                    trace.line(2, format_args!("empty branch reaches suppressed terminal"));
                    return RecognizedShape::sequence(Vec::new());
                }
                if scope.merge_points.contains(&entry) {
                    trace.line(2, format_args!("empty branch reaches implicit outer merge"));
                    return RecognizedShape::sequence(Vec::new());
                }

                // If the branch jumps out of the region entirely, map it to the correct exit instruction.
                if let Some(ctx) = loop_ctx {
                    if ctx.continue_targets.contains(&entry) {
                        trace.line(
                            2,
                            format_args!("empty branch reaches loop continuation -> continue"),
                        );
                        return RecognizedShape::Continue;
                    }
                    if ctx.exits.contains(&entry) {
                        trace.line(2, format_args!("empty branch exits loop -> break"));
                        return RecognizedShape::Break;
                    }
                }

                // Empty branch nodes mean the target is a boundary owned by an
                // outer scope.
                //
                // A shared continuation may itself end in Return, but the edge
                // is still an ordinary fallthrough from this branch.
                trace.line(2, format_args!("empty branch reaches outer boundary"));
                return RecognizedShape::sequence(Vec::new());
            }

            let owned_payload_exit = loop_ctx.and_then(|ctx| {
                ctx.payload_continue_targets
                    .iter()
                    .copied()
                    .filter(|payload| {
                        !scope.merge_points.contains(payload)
                            && (Some(*payload) != shape.merge || scope.exits.contains(payload))
                    })
                    .find(|payload| {
                        entry == *payload
                            || single_target(self.graph.successors(entry)) == Some(*payload)
                    })
            });
            if let Some(payload) = owned_payload_exit {
                nodes.insert(payload);
            }

            let branch_scope = Scope {
                entry,
                nodes,
                exits: branch_exits
                    .iter()
                    .copied()
                    .filter(|exit| *exit != entry && Some(*exit) != owned_payload_exit)
                    .collect(),
                merge_points: shape.merge.into_iter().chain(owned_payload_exit).collect(),
                allow_implicit_continue: false,
            };
            self.structure_scope(&branch_scope, loop_ctx, suppress_exit, blocked_loop)
        };

        let then_shape = build_branch(shape.then_entry, then_nodes);
        let else_shape = build_branch(shape.else_entry, else_nodes);

        RecognizedShape::If(IfShape {
            condition: shape.condition,
            then_branch: Box::new(then_shape),
            else_branch: (!else_shape.is_empty()).then(|| Box::new(else_shape)),
        })
    }

    /// Classifies one natural loop using its typed exits and branch placement.
    fn classify_loop(&self, loop_info: &LoopInfo) -> LoopKind {
        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.line(
            0,
            format_args!("classify_loop: loop_info = {:?}", loop_info),
        );

        let single_latch = (loop_info.latches.len() == 1).then_some(loop_info.latch);

        if let Some(latch) = single_latch
            && let BlockExit::NumericForLoop {
                body_block,
                exit_block,
            } = &self.cfg.block(latch).exit
            && *body_block == loop_info.header
        {
            let prep_block = self.cfg.predecessors(loop_info.header).find(|&pred| {
                matches!(
                    &self.cfg.block(pred).exit,
                    BlockExit::NumericFor {
                        body_block: prep_body,
                        exit_block: prep_exit,
                        ..
                    } if prep_body == body_block
                       && (prep_exit == exit_block
                           // Luau can duplicate a return-only bytecode block after one
                           // branch on O1 and O2. FORNPREP skips to the shared return
                           // while FORNLOOP falls through to the duplicate return block.
                           //
                           // Dedicated test case: controlflow37.luau
                           || self.cfg.blocks_return_same_values(*prep_exit, *exit_block))
                )
            });

            if let Some(prep_block) = prep_block
                && let BlockExit::NumericFor {
                    variable,
                    start,
                    end,
                    step,
                    body_block,
                    exit_block,
                } = &self.cfg.block(prep_block).exit
            {
                trace.line(1, format_args!("kind = NumericFor"));

                return LoopKind::NumericFor {
                    body: *body_block,
                    exit: *exit_block,
                    variable: *variable,
                    start: *start,
                    end: *end,
                    step: *step,
                };
            }
        }

        if let Some(latch) = single_latch
            && let BlockExit::GenericForLoop {
                body_block,
                exit_block,
                ..
            } = &self.cfg.block(latch).exit
            && *body_block == loop_info.header
        {
            let prep_block = self.cfg.predecessors(loop_info.header).find(|&pred| {
                matches!(
                    &self.cfg.block(pred).exit,
                    BlockExit::GenericFor {
                        body_block: prep_body,
                        loop_block,
                        ..
                    } if prep_body == body_block && *loop_block == latch
                )
            });

            if let Some(prep_block) = prep_block
                && let BlockExit::GenericFor {
                    variables, values, ..
                } = &self.cfg.block(prep_block).exit
            {
                trace.line(1, format_args!("kind = GenericFor"));

                return LoopKind::GenericFor {
                    variables: variables.to_vec(),
                    values: *values,
                    body: *body_block,
                    exit: *exit_block,
                };
            }
        }

        // If the latch condition has one edge back to the header and one edge out,
        // this is a post-test loop. The latch owns the condition.
        if let Some(latch) = single_latch
            && let BlockExit::Branch {
                condition,
                then_block,
                else_block,
            } = &self.cfg.block(latch).exit
            && (*then_block == loop_info.header) ^ (*else_block == loop_info.header)
        {
            let condition = if *then_block == loop_info.header {
                Predicate::Value(*condition).invert()
            } else {
                Predicate::Value(*condition)
            };

            let loop_exit = if *then_block == loop_info.header {
                *else_block
            } else {
                *then_block
            };

            if self.can_represent_as_repeat_until(loop_info, loop_exit) {
                trace.line(1, format_args!("kind = RepeatUntil({})", condition));
                return LoopKind::RepeatUntil {
                    condition,
                    latch,
                    body: loop_info.header,
                };
            }
        }

        if let Some(guard) = self.recognize_while_guard(loop_info) {
            trace.line(1, format_args!("kind = While({})", guard.condition));
            return LoopKind::While {
                condition: guard.condition,
                body: guard.body,
                guard_nodes: guard.guard_nodes,
                exits: guard.exits,
            };
        }

        trace.line(1, format_args!("kind=Infinite"));
        LoopKind::Infinite {
            body: loop_info.header,
        }
    }

    /// Attempts to recover a `while` loop guard starting from the loop header.
    ///
    /// A while guard is a chain of empty conditional blocks at the top of the
    /// loop that collectively decide whether to enter the body or exit. Returns
    /// `None` if the header does not match that shape.
    fn recognize_while_guard(&self, loop_info: &LoopInfo) -> Option<WhileGuard> {
        let mut visiting = HashSet::new();
        let guard = self.recognize_while_guard_node(loop_info, loop_info.header, &mut visiting)?;

        Some(WhileGuard {
            condition: guard.condition,
            body: guard.body?,
            guard_nodes: guard.guard_nodes,
            exits: guard.exits,
        })
    }

    /// Tries to recursively fold `node` into the while guard as one conditional step.
    ///
    /// A node qualifies if it is empty, has a branch exit, and both
    /// outgoing edges can be classified by [`Structurer::recognize_while_guard_branch`].
    /// The resulting condition is the boolean combination that is `true`
    /// exactly when a path through this node reaches the loop body:
    ///
    /// `(cond && then_reaches_body) || (!cond && else_reaches_body)`
    fn recognize_while_guard_node(
        &self,
        loop_info: &LoopInfo,
        node: usize,
        visiting: &mut HashSet<usize>,
    ) -> Option<GuardBranch> {
        if !loop_info.body.contains(&node) || self.cfg.block_has_payload(node) {
            return None;
        }
        if !visiting.insert(node) {
            return None;
        }

        let BlockExit::Branch {
            condition,
            then_block,
            else_block,
        } = &self.cfg.block(node).exit
        else {
            visiting.remove(&node);
            return None;
        };

        let then_branch = self.recognize_while_guard_branch(loop_info, *then_block, visiting);
        let else_branch = self.recognize_while_guard_branch(loop_info, *else_block, visiting);

        visiting.remove(&node);

        let then_branch = then_branch?;
        let else_branch = else_branch?;
        let body = merge_optional_body(then_branch.body, else_branch.body)?;
        let mut guard_nodes = then_branch.guard_nodes;
        guard_nodes.extend(else_branch.guard_nodes);
        guard_nodes.insert(node);

        let mut exits = then_branch.exits;
        exits.extend(else_branch.exits);

        let condition = Predicate::Value(*condition);
        Some(GuardBranch {
            condition: Predicate::select(condition, then_branch.condition, else_branch.condition),
            body,
            guard_nodes,
            exits,
        })
    }

    /// Classifies one outgoing edge of a guard node.
    ///
    /// Three outcomes:
    /// - `target` is outside the loop body -> exit edge, condition `false`
    /// - `target` is an empty conditional that itself has a loop exit ->
    ///   recurse into `recognize_while_guard_node` to fold it in
    /// - anything else -> this is the body entry, condition `true`
    fn recognize_while_guard_branch(
        &self,
        loop_info: &LoopInfo,
        target: usize,
        visiting: &mut HashSet<usize>,
    ) -> Option<GuardBranch> {
        if !loop_info.body.contains(&target) {
            return Some(GuardBranch {
                condition: Predicate::False,
                body: None,
                guard_nodes: HashSet::new(),
                exits: [target].into_iter().collect(),
            });
        }

        if !loop_info.latches.contains(&target)
            && !self.cfg.block_has_payload(target)
            && matches!(&self.cfg.block(target).exit, BlockExit::Branch { .. })
            && self.conditional_has_loop_exit(loop_info, target)
            && let Some(guard) = self.recognize_while_guard_node(loop_info, target, visiting)
        {
            return Some(guard);
        }

        Some(GuardBranch {
            condition: Predicate::True,
            body: Some(target),
            guard_nodes: HashSet::new(),
            exits: HashSet::new(),
        })
    }

    /// Returns whether the Block `node` has a conditional jump that exits the loop body.
    fn conditional_has_loop_exit(&self, loop_info: &LoopInfo, node: usize) -> bool {
        let BlockExit::Branch {
            then_block,
            else_block,
            ..
        } = &self.cfg.block(node).exit
        else {
            return false;
        };

        !loop_info.body.contains(then_block) || !loop_info.body.contains(else_block)
    }

    /// Returns whether the loop can be represented as a `repeat until` loop.
    ///
    /// A loop can be represented as a `repeat until` loop if:
    /// 1. It only has one latch,
    /// 2. All of its successors are within the loop's body,
    /// 3. The loop exit block is empty.
    fn can_represent_as_repeat_until(&self, loop_info: &LoopInfo, loop_exit: usize) -> bool {
        let Some(latch) = (loop_info.latches.len() == 1).then_some(loop_info.latch) else {
            return false;
        };

        if loop_info.header != latch
            && self
                .graph
                .successors(loop_info.header)
                .any(|target| !loop_info.body.contains(&target))
        {
            return false;
        }

        if loop_info.exits.len() == 1 {
            return true;
        }

        !self.cfg.block_has_payload(loop_exit)
    }

    /// Returns the common loop follow target, if one exists.
    fn common_loop_follow(&self, loop_info: &LoopInfo) -> Option<usize> {
        // 1. Header's immediate post-dominator outside the loop
        if let Some(follow) = self.ipdoms.idom(loop_info.header)
            && !loop_info.body.contains(&follow)
        {
            return Some(follow);
        }

        // 2. O(N): Find the Lowest Common Post-Dominator among all exit blocks.
        // If that LCD is one of the exit blocks itself, it post-dominates all exits.
        if let Some(lcd) = self
            .ipdoms
            .lowest_common_dominator(loop_info.exits.iter().copied())
        {
            if loop_info.exits.contains(&lcd) {
                return Some(lcd);
            }
        }

        // 3. Fallback: Check if all exits share a single, identical external target.
        let mut follow = None;
        for &exit in &loop_info.exits {
            let target = single_target(self.graph.successors(exit))?;
            if loop_info.body.contains(&target) {
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

    /// Finds the merge point for the given `node` within the given `scope`, if one exists.
    ///
    /// A merge point is an immediate post dominator of `node`, that is within the given `scope`,
    /// and a known merge point of the `scope`.
    fn find_merge_point(&self, node: usize, scope: &Scope) -> Option<usize> {
        let merge = self.ipdoms.idom(node)?;
        // Nested conditionals may rejoin at the containing branch's merge.
        // Such a node is outside the nested scope by ownership, but it is
        // still ordinary fallthrough rather than a loop-control boundary.
        ((scope.nodes.contains(&merge) && !scope.exits.contains(&merge))
            || scope.merge_points.contains(&merge))
        .then_some(merge)
    }

    /// Emits one block together with any explicit loop or return transfer.
    fn shape_for_block(
        &self,
        block: usize,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
    ) -> RecognizedShape {
        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        let block_shape = RecognizedShape::Block(block);

        match &self.cfg.block(block).exit {
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if scope.merge_points.contains(target) =>
            {
                trace.line(
                    2,
                    format_args!("block {} exits to implicit target {}", block, target),
                );
                block_shape
            }
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if loop_ctx.is_some_and(|ctx| {
                    ctx.continue_targets.contains(target)
                        && !ctx.payload_continue_targets.contains(target)
                }) =>
            {
                if suppress_exit == Some(*target) && self.ipdoms.idom(block) == Some(*target) {
                    trace.line(
                        2,
                        format_args!(
                            "block {} reaches suppressed loop terminal {}",
                            block, target
                        ),
                    );
                    return block_shape;
                }

                if scope.allow_implicit_continue
                    && loop_ctx.is_some_and(|ctx| ctx.implicit_tail_blocks.contains(&block))
                {
                    trace.line(
                        2,
                        format_args!(
                            "block {} exits through implicit loop tail to {}",
                            block, target
                        ),
                    );
                    return block_shape;
                }

                trace.line(
                    2,
                    format_args!("block {} exits to continue target {}", block, target),
                );
                RecognizedShape::sequence([block_shape, RecognizedShape::Continue])
            }
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if loop_ctx.is_some_and(|ctx| ctx.exits.contains(target)) =>
            {
                trace.line(
                    2,
                    format_args!("block {} exits to break target {}", block, target),
                );
                RecognizedShape::sequence([block_shape, RecognizedShape::Break])
            }
            BlockExit::Return(values) => {
                RecognizedShape::sequence([block_shape, RecognizedShape::Return(*values)])
            }
            _ => block_shape,
        }
    }

    /// Collects scope-owned blocks reachable before any boundary block.
    fn collect_reachable_until(
        &self,
        entry: usize,
        scope: &Scope,
        exits: &HashSet<usize>,
        include_boundary_entry: bool,
    ) -> HashSet<usize> {
        let mut nodes = HashSet::new();
        let mut stack = vec![entry];

        while let Some(node) = stack.pop() {
            let owns_boundary_entry = include_boundary_entry && node == entry;
            if !scope.nodes.contains(&node) && !owns_boundary_entry {
                continue;
            }
            if exits.contains(&node) && !owns_boundary_entry {
                continue;
            }
            if !nodes.insert(node) {
                continue;
            }
            if exits.contains(&node) {
                continue;
            }

            stack.extend(
                self.graph
                    .successors(node)
                    .filter(|succ| !exits.contains(succ)),
            );
        }

        nodes
    }
}

impl RecognizedShape {
    /// Returns a sequence shape that concatenates the given `nodes`, flattening any nested sequences.
    fn sequence(nodes: impl IntoIterator<Item = RecognizedShape>) -> RecognizedShape {
        let nodes = nodes
            .into_iter()
            .flat_map(|node| match node {
                RecognizedShape::Sequence(nodes) => nodes,
                RecognizedShape::VirtualExit => Vec::new(),
                other => vec![other],
            })
            .collect();

        RecognizedShape::Sequence(nodes)
    }

    /// Returns `true` if this shape is empty, i.e. it is a sequence with no nodes.
    fn is_empty(&self) -> bool {
        matches!(self, RecognizedShape::Sequence(nodes) if nodes.is_empty())
    }

    /// Lowers one recognized shape into flat-IR structured control flow.
    fn lower(self) -> Shape {
        match self {
            RecognizedShape::Block(block) => Shape::Block { block },
            RecognizedShape::Sequence(nodes) => Shape::Sequence {
                nodes: nodes.into_iter().map(RecognizedShape::lower).collect(),
            },
            RecognizedShape::If(shape) => Shape::If {
                condition: shape.condition,
                then_branch: Box::new(shape.then_branch.lower()),
                else_branch: shape.else_branch.map(|branch| Box::new(branch.lower())),
            },
            RecognizedShape::Loop(shape) => match shape.kind {
                LoopKind::While { condition, .. } => Shape::While {
                    condition,
                    body: Box::new(shape.body.lower()),
                },
                LoopKind::RepeatUntil { condition, .. } => Shape::RepeatUntil {
                    condition,
                    body: Box::new(shape.body.lower()),
                },
                LoopKind::NumericFor {
                    variable,
                    start,
                    end,
                    step,
                    ..
                } => Shape::NumericFor {
                    variable,
                    start,
                    end,
                    step,
                    body: Box::new(shape.body.lower()),
                },
                LoopKind::GenericFor {
                    variables, values, ..
                } => Shape::GenericFor {
                    variables,
                    values,
                    body: Box::new(shape.body.lower()),
                },
                LoopKind::Infinite { .. } => Shape::While {
                    condition: Predicate::True,
                    body: Box::new(shape.body.lower()),
                },
            },
            RecognizedShape::Break => Shape::Break,
            RecognizedShape::Continue => Shape::Continue,
            RecognizedShape::Return(values) => Shape::Return { values },
            RecognizedShape::VirtualExit => {
                unreachable!("virtual exit must not survive shape lowering")
            }
        }
    }
}

/// Collect the natural loop body by walking predecessors back from `latch`
/// until `header` is reached. Returns the full set including header.
///
/// **Note**: Natural loop body does not account for lexical ownership or loop-kind
///           specific boundaries.
fn natural_loop_body(
    cfg: &FlowGraph<'_>,
    header: usize,
    latch: usize,
    reachable: &HashSet<usize>,
) -> HashSet<usize> {
    let mut body = HashSet::new();
    body.insert(header);

    let mut stack = vec![latch];
    while let Some(node) = stack.pop() {
        if !reachable.contains(&node) {
            continue;
        }

        if body.insert(node) && node != header {
            for pred in cfg.predecessors(node) {
                if reachable.contains(&pred) {
                    stack.push(pred);
                }
            }
        }
    }

    body
}

/// Returns `Some(target)` if `targets` contains exactly one target, otherwise `None`.
fn single_target<T, I: IntoIterator<Item = T>>(targets: I) -> Option<T> {
    let mut targets = targets.into_iter();
    let target = targets.next()?;
    targets.next().is_none().then_some(target)
}

/// Merges two optional body values, returning `None` if they differ.
fn merge_optional_body(lhs: Option<usize>, rhs: Option<usize>) -> Option<Option<usize>> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) if lhs != rhs => None,
        (Some(body), _) | (_, Some(body)) => Some(Some(body)),
        (None, None) => Some(None),
    }
}

/// Returns block IDs in deterministic order for diagnostics.
fn sorted_nodes(nodes: &HashSet<usize>) -> Vec<usize> {
    let mut nodes: Vec<_> = nodes.iter().copied().collect();
    nodes.sort_unstable();
    nodes
}

/// Returns the set of all conditional branch exits for the given scope.
fn conditional_branch_exits(
    scope: &Scope,
    loop_ctx: Option<&LoopCtx>,
    suppress_exit: Option<usize>,
    merge: Option<usize>,
) -> HashSet<usize> {
    let mut branch_exits = scope.exits.clone();
    if let Some(merge) = merge {
        branch_exits.insert(merge);
    }
    if let Some(block) = suppress_exit {
        branch_exits.insert(block);
    }
    if let Some(ctx) = loop_ctx {
        // Implicit tails still contain loop-body statements; structure them
        // in the branch and suppress only their final backedge.
        branch_exits.extend(ctx.continue_targets.iter().copied().filter(|target| {
            suppress_exit != Some(*target) && !ctx.implicit_tail_blocks.contains(target)
        }));
        branch_exits.extend(ctx.exits.iter().copied());
    }

    branch_exits
}

/// Structures one flat IR function without changing its blocks or instructions.
pub(crate) fn structure(function: &Function, diagnostics: &Diagnostics) -> Result<Shape> {
    ensure!(
        !function.blocks.is_empty(),
        "cannot structure an empty function"
    );

    let cfg = FlowGraph::new(function);
    let node = Structurer::new(&cfg, diagnostics)
        .structure()
        .lower()
        .normalize();
    Ok(node)
}
