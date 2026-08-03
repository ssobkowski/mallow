use std::collections::{HashMap, HashSet, VecDeque};

use smallvec::SmallVec;

use crate::hil::cflow::cfg::{BlockExit, ControlFlowGraph};
use crate::hil::cflow::graph::{DominatorTree, GraphView, Reversed, SeseGraphView};
use crate::hil::ir::{Expr, Stmt, ValuePack};
use crate::hil::lifter::ssa::SymbolId;
use crate::logging::{Diagnostics, LogLevel, LogTarget};
use crate::operator::UnOp;

/// The lexical control-flow shape recognized from CFG facts.
///
/// This layer intentionally keeps raw block IDs. It should describe what the
/// CFG proves, not how the final HIL tree is emitted.
#[derive(Debug, Clone)]
enum Shape {
    /// A plain basic block id. Means nothing on its own, but is used to identify
    /// a basic block in the CFG.
    Block(usize),
    /// A sequence of sequential shapes.
    Sequence(Vec<Shape>),
    /// A structured if/else split.
    If(IfShape),
    /// A structured loop split.
    Loop(LoopShape),
    /// A structured break split.
    Break,
    /// A structured continue split.
    Continue,
    /// A structured return split.
    Return(ValuePack),
    /// A virtual exit split.
    VirtualExit,
}

/// A structured region node in the structured control flow graph.
#[derive(Debug, Clone)]
pub enum RegionNode {
    /// A plain basic block payload that does not by itself decide control transfer.
    BasicBlock { stmts: Vec<Stmt> },
    /// A sequence of nodes executed sequentially.
    Sequence { nodes: Vec<RegionNode> },
    /// A structured if/else split.
    If {
        condition: Expr,
        then_branch: Box<RegionNode>,
        else_branch: Option<Box<RegionNode>>,
    },
    /// A structured while loop.
    While {
        condition: Expr,
        body: Box<RegionNode>,
    },
    /// A structured `repeat [body] until [condition]` loop.
    RepeatUntil {
        condition: Expr,
        body: Box<RegionNode>,
    },
    /// A structured numeric `for` loop.
    NumericFor {
        var: SymbolId,
        start: Expr,
        end: Expr,
        step: Expr,
        body: Box<RegionNode>,
    },
    /// A structured generic `for` loop.
    GenericFor {
        vars: SmallVec<[SymbolId; 3]>,
        exprs: ValuePack,
        body: Box<RegionNode>,
    },
    /// Explicit `continue` edge for a loop.
    Continue,
    /// Explicit `break` edge from a loop body.
    Break,
    /// Explicit return.
    Return { values: ValuePack },
}

impl RegionNode {
    /// Returns an empty structured region.
    pub fn empty() -> Self {
        RegionNode::Sequence { nodes: Vec::new() }
    }

    /// Returns whether this node has no observable payload.
    pub fn is_empty(&self) -> bool {
        match self {
            RegionNode::BasicBlock { stmts } => stmts.is_empty(),
            RegionNode::Sequence { nodes } => nodes.iter().all(Self::is_empty),
            _ => false,
        }
    }
}

/// Represents an unstructured `if` shape with a condition and then/else branches.
#[derive(Debug, Clone)]
struct IfShape {
    /// The condition expression of the `if` statement.
    condition: Expr,
    /// Structured payload reached when `condition` is true.
    then_branch: Box<Shape>,
    /// Structured payload reached when `condition` is false, omitted
    /// when that side has no observable payload.
    else_branch: Option<Box<Shape>>,
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
    body: Box<Shape>,
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
        condition: Expr,
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
        condition: Expr,
        latch: usize,
        body: usize,
    },
    /// for var = start, step, end
    NumericFor {
        var: SymbolId,
        start: Expr,
        end: Expr,
        step: Expr,
        body: usize,
        exit: usize,
    },
    /// for \[vars\] in \[exprs\]
    GenericFor {
        vars: SmallVec<[SymbolId; 3]>,
        exprs: ValuePack,
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
    condition: Expr,
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
    condition: Expr,
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
    condition: Expr,
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
    fn build(cfg: &ControlFlowGraph, idoms: &DominatorTree) -> Self {
        let mut loops = HashMap::new();
        let mut by_header: HashMap<usize, Vec<LoopId>> = HashMap::new();
        let reachable: HashSet<_> = cfg.reverse_post_order().into_iter().collect();

        for latch in cfg.iter() {
            if !reachable.contains(&latch) {
                continue;
            }

            for &header in cfg.successors(latch) {
                if reachable.contains(&header) && idoms.dominates(header, latch) {
                    let id = LoopId { header, latch };
                    let body = natural_loop_body(cfg, header, latch, &reachable);
                    let exits = body
                        .iter()
                        .flat_map(|&block| cfg.successors(block).iter().copied())
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
    fn recompute_exits(cfg: &ControlFlowGraph, loops: &mut HashMap<LoopId, LoopInfo>) {
        for info in loops.values_mut() {
            info.exits = info
                .body
                .iter()
                .flat_map(|&block| cfg.successors(block).iter().copied())
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
    entry: usize,
    exit: usize,
    nodes: HashMap<usize, Shape>,
    successors: HashMap<usize, Vec<usize>>,
    predecessors: HashMap<usize, Vec<usize>>,
}

impl GraphView for RegionGraph {
    type Item = Shape;

    fn get(&self, node: usize) -> Option<&Self::Item> {
        self.nodes.get(&node)
    }

    fn entry(&self) -> usize {
        self.entry
    }

    fn successors(&self, node: usize) -> &[usize] {
        self.successors.get(&node).map_or(&[], |v| v.as_slice())
    }

    fn predecessors(&self, node: usize) -> &[usize] {
        self.predecessors.get(&node).map_or(&[], |v| v.as_slice())
    }

    fn contains_node(&self, node: usize) -> bool {
        self.nodes.contains_key(&node)
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
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
    /// Returns a new [`RegionGraph`] constructed from the given [`ControlFlowGraph`].
    pub fn from_cfg(cfg: &ControlFlowGraph) -> Self {
        let mut nodes: HashMap<_, _> = cfg.iter().map(|i| (i, Shape::Block(i))).collect();
        let mut successors: HashMap<_, _> = cfg
            .iter()
            .map(|i| (i, cfg.successors(i).to_vec()))
            .collect();
        let mut predecessors: HashMap<_, _> = cfg
            .iter()
            .map(|i| (i, cfg.predecessors(i).to_vec()))
            .collect();

        let terminal_nodes: Vec<_> = nodes
            .keys()
            .copied()
            .filter(|&id| successors.get(&id).is_none_or(|s| s.is_empty()))
            .collect();

        let virtual_exit = usize::MAX;
        nodes.insert(virtual_exit, Shape::VirtualExit);

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

struct Structurer<'cfg, 'd> {
    cfg: &'cfg ControlFlowGraph,
    graph: RegionGraph,
    ipdoms: DominatorTree,
    loops: LoopForest,

    diagnostics: &'d Diagnostics,
}

impl<'cfg, 'd> Structurer<'cfg, 'd> {
    fn new(cfg: &'cfg ControlFlowGraph, diagnostics: &'d Diagnostics) -> Self {
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

    /// Recursively structures the region graph into a [`Shape`] tree.
    fn structure(&self) -> Shape {
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

    /// Recursively structures the given scope into a [`Shape`] tree.
    fn structure_scope(
        &self,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
        blocked_loop: Option<LoopId>,
    ) -> Shape {
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
                nodes.push(Shape::Block(current));
                break;
            }

            if let Some(loop_shape) = self.recognize_loop(current, scope, blocked_loop) {
                let next = single_target(&loop_shape.exits);
                trace.line(
                    2,
                    format_args!("recognized loop {:?}, next = {:?}", loop_shape.id, next),
                );
                nodes.push(Shape::Loop(loop_shape));

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
                        nodes.push(Shape::Continue);
                    } else if loop_ctx.is_some_and(|ctx| ctx.exits.contains(&next)) {
                        trace.line(2, format_args!("nested loop exits outer loop -> break"));
                        nodes.push(Shape::Break);
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
                if !self.cfg.get(current).is_empty() {
                    nodes.push(Shape::Block(current));
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
                .iter()
                .copied()
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

        Shape::sequence(nodes)
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
            .flat_map(|&block| self.graph.successors(block).iter().copied())
            .filter(|target| !body.contains(target) && !exits.contains(target))
            .collect();

        while let Some(node) = stack.pop() {
            if exits.contains(&node) || !body.insert(node) {
                continue;
            }

            stack.extend(
                self.graph
                    .successors(node)
                    .iter()
                    .copied()
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
                .iter()
                .copied()
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
    fn structure_loop_body(&self, plan: &LoopBodyPlan, loop_ctx: &LoopCtx) -> Shape {
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
                if !self.cfg.get(loop_info.latch).is_empty() =>
            {
                [loop_info.latch].into_iter().collect()
            }
            _ => HashSet::new(),
        }
    }

    /// Attempts to recognize a conditional block at `head` in the given scope.
    ///
    /// This function is ran after all the loops have been recognized, so all the
    /// `head` block needs to have is any [`BlockExit::CondJump`] exit.
    fn recognize_conditional(
        &self,
        head: usize,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
    ) -> Option<ConditionalShape> {
        let BlockExit::CondJump {
            cond,
            then_block,
            else_block,
        } = self.cfg.get(head).exit()
        else {
            return None;
        };

        Some(ConditionalShape {
            head,
            condition: cond.clone(),
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
                    .iter()
                    .copied()
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

    /// Structures a [`ConditionalShape`] into a [`Shape`] by recursively structuring
    /// the then/else branches and merging them together.
    fn structure_conditional(
        &self,
        shape: ConditionalShape,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
        blocked_loop: Option<LoopId>,
    ) -> Shape {
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
                    return Shape::sequence(Vec::new());
                }
                if Some(entry) == suppress_exit {
                    trace.line(2, format_args!("empty branch reaches suppressed terminal"));
                    return Shape::sequence(Vec::new());
                }
                if scope.merge_points.contains(&entry) {
                    trace.line(2, format_args!("empty branch reaches implicit outer merge"));
                    return Shape::sequence(Vec::new());
                }

                // If the branch jumps out of the region entirely, map it to the correct exit instruction.
                if let Some(ctx) = loop_ctx {
                    if ctx.continue_targets.contains(&entry) {
                        trace.line(
                            2,
                            format_args!("empty branch reaches loop continuation -> continue"),
                        );
                        return Shape::Continue;
                    }
                    if ctx.exits.contains(&entry) {
                        trace.line(2, format_args!("empty branch exits loop -> break"));
                        return Shape::Break;
                    }
                }

                // Empty branch nodes mean the target is a boundary owned by an
                // outer scope.
                //
                // A shared continuation may itself end in Return, but the edge
                // is still an ordinary fallthrough from this branch.
                trace.line(2, format_args!("empty branch reaches outer boundary"));
                return Shape::sequence(Vec::new());
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

        Shape::If(IfShape {
            condition: shape.condition,
            then_branch: Box::new(then_shape),
            else_branch: (!else_shape.is_empty()).then(|| Box::new(else_shape)),
        })
    }

    fn classify_loop(&self, loop_info: &LoopInfo) -> LoopKind {
        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        trace.line(
            0,
            format_args!("classify_loop: loop_info = {:?}", loop_info),
        );

        let single_latch = (loop_info.latches.len() == 1).then_some(loop_info.latch);

        if let Some(latch) = single_latch
            && let BlockExit::FornLoop { base, .. } = self.cfg.get(latch).exit()
        {
            let prep_block = self
                .cfg
                .predecessors(loop_info.header)
                .iter()
                .copied()
                .find(|&pred| {
                    matches!(self.cfg.get(pred).exit(), BlockExit::FornPrep { base: prep_base, .. } if prep_base == base)
                });

            if let Some(prep_block) = prep_block
                && let BlockExit::FornPrep {
                    var,
                    start,
                    end,
                    step,
                    body_block,
                    exit_block,
                    ..
                } = self.cfg.get(prep_block).exit()
            {
                trace.line(1, format_args!("kind = NumericFor"));

                return LoopKind::NumericFor {
                    body: *body_block,
                    exit: *exit_block,
                    var: *var,
                    start: start.clone(),
                    end: end.clone(),
                    step: step.clone(),
                };
            }
        }

        if let Some(latch) = single_latch
            && let BlockExit::ForgLoop {
                base,
                body_block,
                exit_block,
                ..
            } = self.cfg.get(latch).exit()
        {
            let prep_block = self
                .cfg
                .predecessors(loop_info.header)
                .iter()
                .copied()
                .find(|&pred| {
                    matches!(self.cfg.get(pred).exit(), BlockExit::ForgPrep { base: prep_base, .. } if prep_base == base)
                });

            if let Some(prep_block) = prep_block
                && let BlockExit::ForgPrep {
                    vars: prep_vars,
                    exprs,
                    ..
                } = self.cfg.get(prep_block).exit()
            {
                trace.line(1, format_args!("kind = GenericFor"));

                return LoopKind::GenericFor {
                    vars: prep_vars.clone(),
                    exprs: ValuePack::Fixed(exprs.to_vec()),
                    body: *body_block,
                    exit: *exit_block,
                };
            }
        }

        // If the latch condition has one edge back to the header and one edge out,
        // this is a post-test loop. The latch owns the condition.
        if let Some(latch) = single_latch
            && let BlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } = self.cfg.get(latch).exit()
            && (*then_block == loop_info.header) ^ (*else_block == loop_info.header)
        {
            let condition = if *then_block == loop_info.header {
                Expr::Unary {
                    op: UnOp::Not,
                    expr: Box::new(cond.clone()),
                }
            } else {
                cond.clone()
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
    /// A node qualifies if it is empty, has a `CondJump` exit, and both
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
        if !loop_info.body.contains(&node) || !self.cfg.get(node).is_empty() {
            return None;
        }
        if !visiting.insert(node) {
            return None;
        }

        let BlockExit::CondJump {
            cond,
            then_block,
            else_block,
        } = self.cfg.get(node).exit()
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

        Some(GuardBranch {
            condition: Expr::or(
                Expr::and(cond.clone(), then_branch.condition),
                Expr::and(cond.clone().invert(), else_branch.condition),
            ),
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
                condition: Expr::Bool(false),
                body: None,
                guard_nodes: HashSet::new(),
                exits: [target].into_iter().collect(),
            });
        }

        if !loop_info.latches.contains(&target)
            && self.cfg.get(target).is_empty()
            && matches!(self.cfg.get(target).exit(), BlockExit::CondJump { .. })
            && self.conditional_has_loop_exit(loop_info, target)
            && let Some(guard) = self.recognize_while_guard_node(loop_info, target, visiting)
        {
            return Some(guard);
        }

        Some(GuardBranch {
            condition: Expr::Bool(true),
            body: Some(target),
            guard_nodes: HashSet::new(),
            exits: HashSet::new(),
        })
    }

    /// Returns whether the Block `node` has a conditional jump that exits the loop body.
    fn conditional_has_loop_exit(&self, loop_info: &LoopInfo, node: usize) -> bool {
        let BlockExit::CondJump {
            then_block,
            else_block,
            ..
        } = self.cfg.get(node).exit()
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
                .iter()
                .any(|target| !loop_info.body.contains(target))
        {
            return false;
        }

        if loop_info.exits.len() == 1 {
            return true;
        }

        self.cfg.get(loop_exit).is_empty()
    }

    /// Returns the common loop follow target, if one exists.
    fn common_loop_follow(&self, loop_info: &LoopInfo) -> Option<usize> {
        if let Some(follow) = self.ipdoms.idom(loop_info.header)
            && !loop_info.body.contains(&follow)
        {
            return Some(follow);
        }

        // This tree uses the reversed graph, so dominance here means
        // that the candidate post-dominates every loop exit.
        //
        // TODO: This is O(N^2). Probably not the best way to do it.
        if let Some(follow) = loop_info.exits.iter().copied().find(|candidate| {
            loop_info
                .exits
                .iter()
                .all(|exit| self.ipdoms.dominates(*candidate, *exit))
        }) {
            return Some(follow);
        }

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

    fn shape_for_block(
        &self,
        block: usize,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        suppress_exit: Option<usize>,
    ) -> Shape {
        let trace = self.diagnostics.at(LogLevel::Trace, LogTarget::Region);
        let block_shape = Shape::Block(block);

        match self.cfg.get(block).exit() {
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
                Shape::sequence([block_shape, Shape::Continue])
            }
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if loop_ctx.is_some_and(|ctx| ctx.exits.contains(target)) =>
            {
                trace.line(
                    2,
                    format_args!("block {} exits to break target {}", block, target),
                );
                Shape::sequence([block_shape, Shape::Break])
            }
            BlockExit::Return(values) => {
                Shape::sequence([block_shape, Shape::Return(values.clone())])
            }
            _ => block_shape,
        }
    }

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
                    .iter()
                    .copied()
                    .filter(|succ| !exits.contains(succ)),
            );
        }

        nodes
    }
}

impl Shape {
    /// Returns a sequence shape that concatenates the given `nodes`, flattening any nested sequences.
    fn sequence(nodes: impl IntoIterator<Item = Shape>) -> Shape {
        let nodes = nodes
            .into_iter()
            .flat_map(|node| match node {
                Shape::Sequence(nodes) => nodes,
                Shape::VirtualExit => Vec::new(),
                other => vec![other],
            })
            .collect();

        Shape::Sequence(nodes)
    }

    /// Returns `true` if this shape is empty, i.e. it is a sequence with no nodes.
    fn is_empty(&self) -> bool {
        matches!(self, Shape::Sequence(nodes) if nodes.is_empty())
    }

    /// Lowers the unstructured [`Shape`] into a structured [`RegionNode`], consuming `self`.
    fn lower(self, cfg: &ControlFlowGraph, block_counts: &mut HashMap<usize, usize>) -> RegionNode {
        match self {
            Shape::Block(block) => {
                *block_counts.entry(block).or_default() += 1;
                RegionNode::BasicBlock {
                    stmts: cfg.get(block).stmts().to_vec(),
                }
            }
            Shape::Sequence(nodes) => RegionNode::Sequence {
                nodes: nodes
                    .into_iter()
                    .map(|node| node.lower(cfg, block_counts))
                    .collect(),
            },
            Shape::If(shape) => RegionNode::If {
                condition: shape.condition,
                then_branch: Box::new(shape.then_branch.lower(cfg, block_counts)),
                else_branch: shape
                    .else_branch
                    .map(|branch| Box::new(branch.lower(cfg, block_counts))),
            },
            Shape::Loop(shape) => match shape.kind {
                LoopKind::While { condition, .. } => RegionNode::While {
                    condition,
                    body: Box::new(shape.body.lower(cfg, block_counts)),
                },
                LoopKind::RepeatUntil { condition, .. } => RegionNode::RepeatUntil {
                    condition,
                    body: Box::new(shape.body.lower(cfg, block_counts)),
                },
                LoopKind::NumericFor {
                    var,
                    start,
                    end,
                    step,
                    ..
                } => RegionNode::NumericFor {
                    var,
                    start,
                    end,
                    step,
                    body: Box::new(shape.body.lower(cfg, block_counts)),
                },
                LoopKind::GenericFor { vars, exprs, .. } => RegionNode::GenericFor {
                    vars,
                    exprs,
                    body: Box::new(shape.body.lower(cfg, block_counts)),
                },
                LoopKind::Infinite { .. } => RegionNode::While {
                    condition: Expr::Bool(true),
                    body: Box::new(shape.body.lower(cfg, block_counts)),
                },
            },
            Shape::Break => RegionNode::Break,
            Shape::Continue => RegionNode::Continue,
            Shape::Return(values) => RegionNode::Return { values },
            Shape::VirtualExit => unreachable!("should have been unfolded already"),
        }
    }
}

/// Collect the natural loop body by walking predecessors back from `latch`
/// until `header` is reached. Returns the full set including header.
///
/// **Note**: Natural loop body does not account for lexical ownership or loop-kind
///           specific boundaries.
fn natural_loop_body(
    cfg: &ControlFlowGraph,
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
            for &pred in cfg.predecessors(node) {
                if reachable.contains(&pred) {
                    stack.push(pred);
                }
            }
        }
    }

    body
}

/// Returns `Some(target)` if `targets` contains exactly one target, otherwise `None`.
fn single_target<'a, I: IntoIterator<Item = &'a usize>>(targets: I) -> Option<usize> {
    let mut targets = targets.into_iter().copied();
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

/// Structures the given [`ControlFlowGraph`] into a [`RegionNode`].
pub fn structure(cfg: &ControlFlowGraph, diagnostics: &Diagnostics) -> RegionNode {
    let mut block_counts = HashMap::new();
    let node = Structurer::new(cfg, diagnostics)
        .structure()
        .lower(cfg, &mut block_counts);

    let duplicated_blocks: Vec<_> = block_counts
        .into_iter()
        .filter_map(|(block, count)| (count > 1).then_some(block))
        .collect();
    if !duplicated_blocks.is_empty() {
        diagnostics.at(LogLevel::Warning, LogTarget::Region).block(
            "structuring did not fully reduce",
            |trace| {
                trace.line(
                    1,
                    format_args!("duplicated blocks = {:?}", duplicated_blocks),
                );
            },
        );
    }

    node
}
