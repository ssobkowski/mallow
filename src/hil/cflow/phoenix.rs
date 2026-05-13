#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use smallvec::SmallVec;

use crate::{
    ast::{BinOp, UnOp},
    hil::{
        cflow::{
            cfg::{BlockExit, ControlFlowGraph},
            graph::{DominatorTree, GraphView, Reversed, SeseGraphView},
            region::RegionNode,
        },
        ir::HilExpr,
        lifter::ssa::SymbolId,
    },
    logging::verbose,
};

/// The lexical control-flow shape recognized from CFG facts.
///
/// This layer intentionally keeps raw block IDs. It should describe what the
/// CFG proves, not how the final HIL tree is emitted.
#[derive(Debug, Clone)]
enum Shape {
    Block(usize),
    Sequence(Vec<Shape>),
    If(IfShape),
    Loop(LoopShape),
    Break,
    Continue,
    Return { values: SmallVec<[HilExpr; 3]> },
    VirtualExit,
}

#[derive(Debug, Clone)]
struct IfShape {
    /// CFG block that owns the conditional terminator.
    head: usize,
    condition: HilExpr,
    /// Structured payload reached when `condition` is true.
    then_branch: Box<Shape>,
    /// Structured payload reached when `condition` is false, omitted
    /// when that side has no observable payload.
    else_branch: Option<Box<Shape>>,
    /// Immediate post-dominator inside the active scope, if one exists.
    merge: Option<usize>,
}

/// Loop boundary facts needed while recursively structuring a loop body.
#[derive(Debug, Clone)]
struct LoopCtx {
    /// Loop header block, mostly for diagnostics and future loop-owned tests.
    header: usize,
    /// In-body edge targets that mean "finish this iteration". For pre-test
    /// loops this includes the header/latch; for Luau numeric and generic
    /// loops this is the loop instruction latch.
    continue_targets: HashSet<usize>,
    /// Blocks whose edge to a continue target is the loop's ordinary tail edge.
    /// That edge is represented by the surrounding loop syntax and must not be
    /// lowered as an explicit `continue`.
    implicit_continue_sources: HashSet<usize>,
    /// Continue targets that still carry loop-body payload before completing
    /// the iteration.
    continue_payload_entries: HashSet<usize>,
    /// Edge targets immediately outside the natural loop body. These are raw
    /// CFG targets, not proof that the target block is payload-free.
    exits: HashSet<usize>,
    /// Exit targets that still belong to a branch inside the loop because they
    /// carry statements before reaching the loop's canonical resume point.
    exit_payload_entries: HashSet<usize>,
}

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
    id: LoopId,
    /// Header that identified this loop in the loop forest.
    header: usize,
    kind: LoopKind,
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
        condition: HilExpr,
        /// First CFG block in the guard tree.
        guard: usize,
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
        condition: HilExpr,
        latch: usize,
        body: usize,
    },
    /// for var = start, step, end
    NumericFor {
        var: SymbolId,
        start: HilExpr,
        end: HilExpr,
        step: HilExpr,
        prep: usize,
        body: usize,
        exit: usize,
    },
    /// for [vars] in [exprs]
    GenericFor {
        vars: SmallVec<[SymbolId; 3]>,
        exprs: [HilExpr; 3],
        prep: usize,
        body: usize,
        exit: usize,
    },
    /// `while true do`; loop exits are represented by `break`.
    Infinite { body: usize },
}

#[derive(Debug, Clone)]
struct LoopBodyPlan {
    /// Loop currently being structured. Passed back as `blocked_loop` so the
    /// body traversal does not recursively recognize the same loop again.
    loop_id: LoopId,
    /// First CFG block to structure as the loop body.
    entry: usize,
    /// Blocks considered available to the loop body scope. This starts from the
    /// natural loop body; branch structuring may still pull in an exit target
    /// when that target is the branch entry and carries statements before
    /// leaving the loop.
    nodes: HashSet<usize>,
    /// Boundary targets for the body scope. Reaching one stops ordinary linear
    /// traversal and is later lowered through `LoopCtx` when appropriate.
    exits: HashSet<usize>,
    terminal_policy: TerminalPolicy,
}

#[derive(Debug, Clone)]
enum TerminalPolicy {
    Normal,
    SuppressExitOf { block: usize },
}

impl TerminalPolicy {
    fn suppresses(&self, block: usize) -> bool {
        matches!(self, TerminalPolicy::SuppressExitOf { block: suppressed } if *suppressed == block)
    }
}

/// The CFG boundary currently being structured.
#[derive(Debug, Clone)]
struct Scope {
    /// First block to emit in this recursive structuring call.
    entry: usize,
    /// Blocks owned by this scope. Ordinary traversal should not walk outside
    /// this set, but a branch entry that is also an exit target is still allowed
    /// to be structured so its payload is not lost.
    nodes: HashSet<usize>,
    /// Boundary targets for this scope. These are stop points for sequencing,
    /// not a claim that the target blocks have no statements.
    exits: HashSet<usize>,
    /// Exit targets that represent ordinary fallthrough for this scope, such as
    /// the merge block of a structured conditional branch.
    implicit_exits: HashSet<usize>,
}

#[derive(Debug, Clone)]
struct ConditionalShape {
    /// CFG block whose terminator branches to `then_entry` or `else_entry`.
    head: usize,
    condition: HilExpr,
    then_entry: usize,
    else_entry: usize,
    /// In-scope immediate post-dominator where both branches rejoin.
    merge: Option<usize>,
}

/// Natural-loop facts discovered from dominators and backedges.
#[derive(Debug, Clone)]
struct LoopInfo {
    id: LoopId,
    header: usize,
    latch: usize,
    /// Natural loop body collected by walking predecessors from latch to
    /// header. This identifies the cycle that proves the loop exists; Phoenix
    /// expands it into a lexical body after classifying the loop kind.
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
    condition: HilExpr,
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
    condition: HilExpr,
    /// Payload entry reached by this branch, or `None` for a loop exit branch.
    body: Option<usize>,
    /// Empty CFG blocks folded while following this branch.
    guard_nodes: HashSet<usize>,
    /// Exit targets discovered while following this branch.
    exits: HashSet<usize>,
}

#[derive(Debug, Clone)]
struct LoopForest {
    loops: HashMap<LoopId, LoopInfo>,
    by_header: HashMap<usize, Vec<LoopId>>,
}

impl LoopForest {
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

        for info in loops.values_mut() {
            info.exits = info
                .body
                .iter()
                .flat_map(|&block| cfg.successors(block).iter().copied())
                .filter(|target| !info.body.contains(target))
                .collect();
        }

        for info in loops.values_mut() {
            info.children.sort_unstable();
            info.children.dedup();
        }

        Self { loops, by_header }
    }

    fn get(&self, id: LoopId) -> Option<&LoopInfo> {
        self.loops.get(&id)
    }

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

    fn is_nested_in(&self, inner: LoopId, outer: LoopId) -> bool {
        let mut current = self.get(inner).and_then(|info| info.parent);

        while let Some(id) = current {
            if id == outer {
                return true;
            }
            current = self.get(id).and_then(|info| info.parent);
        }

        false
    }

    fn direct_children(&self, id: LoopId) -> &[LoopId] {
        self.get(id).map_or(&[], |info| info.children.as_slice())
    }

    fn is_loop_header(&self, node: usize) -> bool {
        self.by_header.contains_key(&node)
    }
}

pub struct RegionGraph {
    entry: usize,
    exit: usize,
    nodes: HashMap<usize, Shape>,
    successors: HashMap<usize, Vec<usize>>,
    predecessors: HashMap<usize, Vec<usize>>,
}

impl GraphView for RegionGraph {
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
}

impl SeseGraphView for RegionGraph {
    fn exit(&self) -> usize {
        self.exit
    }
}

impl RegionGraph {
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

struct Structurer<'cfg> {
    cfg: &'cfg ControlFlowGraph,
    graph: RegionGraph,
    idoms: DominatorTree,
    ipdoms: DominatorTree,
    loops: LoopForest,
}

impl<'cfg> Structurer<'cfg> {
    fn new(cfg: &'cfg ControlFlowGraph) -> Self {
        let graph = RegionGraph::from_cfg(cfg);
        let idoms = graph.build_idoms();
        let ipdoms = Reversed::new(&graph).build_idoms();
        let loops = LoopForest::build(cfg, &idoms);

        Self {
            cfg,
            graph,
            idoms,
            ipdoms,
            loops,
        }
    }

    fn structure(&self) -> Shape {
        let nodes = self.graph.reverse_post_order().into_iter().collect();
        let exits = [self.graph.exit()].into_iter().collect();
        let scope = Scope {
            entry: self.graph.entry(),
            nodes,
            exits,
            implicit_exits: HashSet::new(),
        };

        self.structure_scope(&scope, None, &TerminalPolicy::Normal, None)
    }

    fn structure_scope(
        &self,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        terminal_policy: &TerminalPolicy,
        blocked_loop: Option<LoopId>,
    ) -> Shape {
        verbose!("scope:");
        verbose!(indent: 1, "entry = {}", scope.entry);
        verbose!(indent: 1, "nodes = {:?}", sorted_nodes(&scope.nodes));
        verbose!(indent: 1, "exits = {:?}", sorted_nodes(&scope.exits));
        verbose!(
            indent: 1,
            "implicit_exits = {:?}",
            sorted_nodes(&scope.implicit_exits)
        );
        verbose!(indent: 1, "terminal_policy = {:?}", terminal_policy);
        verbose!(indent: 1, "blocked_loop = {:?}", blocked_loop);
        if let Some(ctx) = loop_ctx {
            verbose!(indent: 1, "loop_ctx.header = {}", ctx.header);
            verbose!(
                indent: 1,
                "loop_ctx.continue_targets = {:?}",
                sorted_nodes(&ctx.continue_targets)
            );
            verbose!(
                indent: 1,
                "loop_ctx.implicit_continue_sources = {:?}",
                sorted_nodes(&ctx.implicit_continue_sources)
            );
            verbose!(indent: 1, "loop_ctx.exits = {:?}", sorted_nodes(&ctx.exits));
        }

        let mut nodes = Vec::new();
        let mut visited = HashSet::new();
        let mut current = scope.entry;

        visited.insert(usize::MAX); // virtual exit

        while scope.nodes.contains(&current)
            && !scope.exits.contains(&current)
            && visited.insert(current)
        {
            verbose!(indent: 1, "visit block {}", current);

            if terminal_policy.suppresses(current) {
                verbose!(indent: 2, "terminal policy suppresses this block");
                nodes.push(Shape::Block(current));
                break;
            }

            if let Some(loop_shape) = self.recognize_loop(current, scope, blocked_loop) {
                let next = single_target(&loop_shape.exits);
                verbose!(indent: 2, "recognized loop {:?}, next = {:?}", loop_shape.id, next);
                nodes.push(Shape::Loop(loop_shape));

                let Some(next) = next else {
                    break;
                };
                current = next;
                continue;
            }

            if let Some(conditional) = self.recognize_conditional(current, scope) {
                let merge = conditional.merge;
                verbose!(
                    indent: 2,
                    "recognized conditional: cond = ({}), then = {}, else = {}, merge = {:?}",
                    conditional.condition,
                    conditional.then_entry,
                    conditional.else_entry,
                    merge
                );

                if !self.cfg.get(current).is_empty() {
                    nodes.push(Shape::Block(current));
                }

                nodes.push(self.structure_conditional(
                    conditional,
                    scope,
                    loop_ctx,
                    terminal_policy,
                    blocked_loop,
                ));

                let Some(merge) = merge else {
                    break;
                };
                current = merge;
                continue;
            }

            nodes.push(self.shape_for_block(current, scope, loop_ctx));

            let next = self
                .graph
                .successors(current)
                .iter()
                .copied()
                .find(|succ| scope.nodes.contains(succ) || scope.exits.contains(succ));

            let Some(next) = next else {
                verbose!(indent: 2, "no in-scope successor");
                break;
            };

            if scope.exits.contains(&next) {
                verbose!(indent: 2, "next block {} is a scope exit", next);
                break;
            }

            verbose!(indent: 2, "next block = {}", next);
            current = next;
        }

        if scope.nodes.contains(&current) && !scope.exits.contains(&current) {
            verbose!(indent: 1, "stopped at block {} after revisit or terminal stop", current);
        } else {
            verbose!(indent: 1, "stopped before block {}", current);
        }

        Shape::sequence(nodes)
    }

    fn recognize_loop(
        &self,
        header: usize,
        scope: &Scope,
        blocked_loop: Option<LoopId>,
    ) -> Option<LoopShape> {
        let loop_info = self.loops.candidate_in_scope(header, scope, blocked_loop)?;
        let kind = self.classify_loop(loop_info);
        let (lexical_body, lexical_exits) = self.lexical_loop_body(loop_info, &kind);
        let body_plan = self.plan_loop_body(
            loop_info,
            &kind,
            lexical_body.clone(),
            lexical_exits.clone(),
        );

        let loop_ctx = LoopCtx {
            header,
            continue_targets: self.continue_targets(loop_info, &kind),
            implicit_continue_sources: self.implicit_continue_sources(loop_info, &kind),
            continue_payload_entries: self.continue_payload_entries(loop_info, &kind),
            exits: lexical_exits.clone(),
            exit_payload_entries: self.exit_payload_entries(loop_info, &lexical_exits),
        };

        verbose!("loop:");
        verbose!(indent: 1, "id = {:?}", loop_info.id);
        verbose!(indent: 1, "header = {}", header);
        verbose!(
            indent: 1,
            "natural_body = {:?}",
            sorted_nodes(&loop_info.body)
        );
        verbose!(indent: 1, "body = {:?}", sorted_nodes(&body_plan.nodes));
        verbose!(indent: 1, "exits = {:?}", sorted_nodes(&lexical_exits));
        verbose!(
            indent: 1,
            "exit_payload_entries = {:?}",
            sorted_nodes(&loop_ctx.exit_payload_entries)
        );
        verbose!(
            indent: 1,
            "continue_targets = {:?}",
            sorted_nodes(&loop_ctx.continue_targets)
        );
        verbose!(
            indent: 1,
            "implicit_continue_sources = {:?}",
            sorted_nodes(&loop_ctx.implicit_continue_sources)
        );
        verbose!(
            indent: 1,
            "continue_payload_entries = {:?}",
            sorted_nodes(&loop_ctx.continue_payload_entries)
        );
        verbose!(indent: 1, "body_entry = {}", body_plan.entry);
        verbose!(
            indent: 1,
            "body_terminal_policy = {:?}",
            body_plan.terminal_policy
        );

        Some(LoopShape {
            id: loop_info.id,
            header,
            kind,
            body: Box::new(self.structure_loop_body(&body_plan, &loop_ctx)),
            exits: lexical_exits,
        })
    }

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
                    terminal_policy: TerminalPolicy::Normal,
                }
            }
            LoopKind::Infinite { body } => LoopBodyPlan {
                loop_id: loop_info.id,
                entry: *body,
                nodes: lexical_body,
                exits: lexical_exits,
                terminal_policy: TerminalPolicy::Normal,
            },
            LoopKind::RepeatUntil { latch, body, .. } => LoopBodyPlan {
                loop_id: loop_info.id,
                entry: *body,
                nodes: lexical_body,
                exits: lexical_exits,
                terminal_policy: TerminalPolicy::SuppressExitOf { block: *latch },
            },
            LoopKind::NumericFor { body, .. } | LoopKind::GenericFor { body, .. } => LoopBodyPlan {
                loop_id: loop_info.id,
                entry: *body,
                nodes: lexical_body,
                exits: lexical_exits,
                terminal_policy: TerminalPolicy::Normal,
            },
        }
    }

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

    fn structure_loop_body(&self, plan: &LoopBodyPlan, loop_ctx: &LoopCtx) -> Shape {
        let scope = Scope {
            entry: plan.entry,
            nodes: plan.nodes.clone(),
            exits: plan.exits.clone(),
            implicit_exits: HashSet::new(),
        };

        self.structure_scope(
            &scope,
            Some(loop_ctx),
            &plan.terminal_policy,
            Some(plan.loop_id),
        )
    }

    fn continue_targets(&self, loop_info: &LoopInfo, kind: &LoopKind) -> HashSet<usize> {
        match kind {
            LoopKind::While { .. } | LoopKind::Infinite { .. } => {
                [loop_info.header, loop_info.latch].into_iter().collect()
            }
            LoopKind::RepeatUntil { .. }
            | LoopKind::NumericFor { .. }
            | LoopKind::GenericFor { .. } => [loop_info.latch].into_iter().collect(),
        }
    }

    fn implicit_continue_sources(&self, loop_info: &LoopInfo, kind: &LoopKind) -> HashSet<usize> {
        match kind {
            LoopKind::While { .. } | LoopKind::Infinite { .. }
                if loop_info.latch != loop_info.header =>
            {
                [loop_info.latch].into_iter().collect()
            }
            _ => HashSet::new(),
        }
    }

    fn exit_payload_entries(
        &self,
        loop_info: &LoopInfo,
        lexical_exits: &HashSet<usize>,
    ) -> HashSet<usize> {
        loop_info.exits.difference(lexical_exits).copied().collect()
    }

    fn continue_payload_entries(&self, loop_info: &LoopInfo, kind: &LoopKind) -> HashSet<usize> {
        match kind {
            LoopKind::While { .. } | LoopKind::Infinite { .. }
                if loop_info.latch != loop_info.header =>
            {
                [loop_info.latch].into_iter().collect()
            }
            LoopKind::NumericFor { .. } | LoopKind::GenericFor { .. }
                if !self.cfg.get(loop_info.latch).is_empty() =>
            {
                [loop_info.latch].into_iter().collect()
            }
            _ => HashSet::new(),
        }
    }

    fn recognize_conditional(&self, head: usize, scope: &Scope) -> Option<ConditionalShape> {
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
            merge: self.find_merge_point(head, scope),
        })
    }

    fn structure_conditional(
        &self,
        shape: ConditionalShape,
        scope: &Scope,
        loop_ctx: Option<&LoopCtx>,
        terminal_policy: &TerminalPolicy,
        blocked_loop: Option<LoopId>,
    ) -> Shape {
        let mut branch_exits = scope.exits.clone();
        if let Some(merge) = shape.merge {
            branch_exits.insert(merge);
        }
        if let TerminalPolicy::SuppressExitOf { block } = terminal_policy {
            branch_exits.insert(*block);
        }
        if let Some(ctx) = loop_ctx {
            branch_exits.extend(ctx.continue_targets.iter().copied());
            branch_exits.extend(ctx.exits.iter().copied());
        }

        verbose!("conditional:");
        verbose!(indent: 1, "head = {}", shape.head);
        verbose!(indent: 1, "then_entry = {}", shape.then_entry);
        verbose!(indent: 1, "else_entry = {}", shape.else_entry);
        verbose!(indent: 1, "merge = {:?}", shape.merge);
        verbose!(indent: 1, "branch_exits = {:?}", sorted_nodes(&branch_exits));

        let owned_boundary_entry = |entry: usize| {
            Some(entry) != shape.merge
                && !terminal_policy.suppresses(entry)
                && loop_ctx.is_some_and(|ctx| {
                    ctx.continue_payload_entries.contains(&entry)
                        || ctx.exit_payload_entries.contains(&entry)
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

        verbose!(indent: 1, "then_nodes = {:?}", sorted_nodes(&then_nodes));
        verbose!(indent: 1, "else_nodes = {:?}", sorted_nodes(&else_nodes));

        let build_branch = |entry: usize, nodes: HashSet<usize>| {
            verbose!(
                indent: 1,
                "build_branch entry = {}, nodes = {:?}",
                entry,
                sorted_nodes(&nodes)
            );

            if nodes.is_empty() {
                // If the branch naturally falls through to the merge point, it's just empty.
                if Some(entry) == shape.merge {
                    verbose!(indent: 2, "empty branch falls through to merge");
                    return Shape::sequence(Vec::new());
                }
                if terminal_policy.suppresses(entry) {
                    verbose!(indent: 2, "empty branch reaches suppressed terminal");
                    return Shape::sequence(Vec::new());
                }

                // If the branch jumps out of the region entirely, map it to the correct exit instruction.
                if let Some(ctx) = loop_ctx {
                    if ctx.continue_targets.contains(&entry) {
                        verbose!(indent: 2, "empty branch reaches loop continuation -> continue");
                        return Shape::Continue;
                    }
                    if ctx.exits.contains(&entry) {
                        verbose!(indent: 2, "empty branch exits loop -> break");
                        return Shape::Break;
                    }
                }

                // Catch edge cases where an empty branch is a direct return
                if let BlockExit::Return(values) = self.cfg.get(entry).exit() {
                    verbose!(indent: 2, "empty branch reaches return");
                    return Shape::Return {
                        values: values.clone(),
                    };
                }

                verbose!(indent: 2, "empty branch has no structured terminal");
                return Shape::sequence(Vec::new());
            }

            let branch_scope = Scope {
                entry,
                nodes,
                exits: branch_exits
                    .iter()
                    .copied()
                    .filter(|exit| *exit != entry)
                    .collect(),
                implicit_exits: shape.merge.into_iter().collect(),
            };
            self.structure_scope(&branch_scope, loop_ctx, terminal_policy, blocked_loop)
        };

        let then_shape = build_branch(shape.then_entry, then_nodes);
        let else_shape = build_branch(shape.else_entry, else_nodes);

        Shape::If(IfShape {
            head: shape.head,
            condition: shape.condition,
            then_branch: Box::new(then_shape),
            else_branch: (!else_shape.is_empty()).then(|| Box::new(else_shape)),
            merge: shape.merge,
        })
    }

    fn classify_loop(&self, loop_info: &LoopInfo) -> LoopKind {
        verbose!("classify_loop: loop_info = {:?}", loop_info);

        if let BlockExit::FornLoop { base, .. } = self.cfg.get(loop_info.latch).exit() {
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
                verbose!(indent: 1, "kind = NumericFor");

                return LoopKind::NumericFor {
                    prep: *base as usize,
                    body: *body_block,
                    exit: *exit_block,
                    var: *var,
                    start: start.clone(),
                    end: end.clone(),
                    step: step.clone(),
                };
            }
        }

        if let BlockExit::ForgLoop {
            base,
            vars,
            body_block,
            exit_block,
        } = self.cfg.get(loop_info.latch).exit()
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
                && let BlockExit::ForgPrep { exprs, .. } = self.cfg.get(prep_block).exit()
            {
                verbose!(indent: 1, "kind = GenericFor");

                return LoopKind::GenericFor {
                    vars: vars.clone(),
                    exprs: exprs.clone(),
                    prep: prep_block,
                    body: *body_block,
                    exit: *exit_block,
                };
            }
        }

        // If the latch condition has one edge back to the header and one edge out,
        // this is a post-test loop. The latch owns the condition.
        if let BlockExit::CondJump {
            cond,
            then_block,
            else_block,
        } = self.cfg.get(loop_info.latch).exit()
            && (*then_block == loop_info.header) ^ (*else_block == loop_info.header)
        {
            let condition = if *then_block == loop_info.header {
                HilExpr::Unary {
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
                verbose!(indent: 1, "kind = RepeatUntil");
                verbose!(indent: 1, "condition = ({})", condition);
                return LoopKind::RepeatUntil {
                    condition,
                    latch: loop_info.latch,
                    body: loop_info.header,
                };
            }
        }

        if let Some(guard) = self.recognize_while_guard(loop_info) {
            verbose!(indent: 1, "kind = While");
            verbose!(indent: 1, "condition = ({})", guard.condition);
            return LoopKind::While {
                condition: guard.condition,
                guard: loop_info.header,
                body: guard.body,
                guard_nodes: guard.guard_nodes,
                exits: guard.exits,
            };
        }

        verbose!(indent: 1, "kind=Infinite");
        LoopKind::Infinite {
            body: loop_info.header,
        }
    }

    fn recognize_while_guard(&self, loop_info: &LoopInfo) -> Option<WhileGuard> {
        let mut visiting = HashSet::new();
        let guard = self.recognize_while_guard_node(loop_info, loop_info.header, &mut visiting)?;
        let body = guard.body?;

        Some(WhileGuard {
            condition: guard.condition,
            body,
            guard_nodes: guard.guard_nodes,
            exits: guard.exits,
        })
    }

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
            condition: or_expr(
                and_expr(cond.clone(), then_branch.condition),
                and_expr(cond.clone().invert(), else_branch.condition),
            ),
            body,
            guard_nodes,
            exits,
        })
    }

    fn recognize_while_guard_branch(
        &self,
        loop_info: &LoopInfo,
        target: usize,
        visiting: &mut HashSet<usize>,
    ) -> Option<GuardBranch> {
        if !loop_info.body.contains(&target) {
            return Some(GuardBranch {
                condition: HilExpr::Bool(false),
                body: None,
                guard_nodes: HashSet::new(),
                exits: [target].into_iter().collect(),
            });
        }

        if target != loop_info.latch
            && self.cfg.get(target).is_empty()
            && matches!(self.cfg.get(target).exit(), BlockExit::CondJump { .. })
            && let Some(guard) = self.recognize_while_guard_node(loop_info, target, visiting)
        {
            return Some(guard);
        }

        Some(GuardBranch {
            condition: HilExpr::Bool(true),
            body: Some(target),
            guard_nodes: HashSet::new(),
            exits: HashSet::new(),
        })
    }

    fn can_represent_as_repeat_until(&self, loop_info: &LoopInfo, loop_exit: usize) -> bool {
        if loop_info.exits.len() == 1 {
            return true;
        }

        self.cfg.get(loop_exit).is_empty()
    }

    fn common_loop_follow(&self, loop_info: &LoopInfo) -> Option<usize> {
        let follow = self.ipdoms.idom(loop_info.header)?;
        (!loop_info.body.contains(&follow)).then_some(follow)
    }

    fn find_merge_point(&self, node: usize, scope: &Scope) -> Option<usize> {
        let merge = self.ipdoms.idom(node)?;
        (scope.nodes.contains(&merge) && !scope.exits.contains(&merge)).then_some(merge)
    }

    fn shape_for_block(&self, block: usize, scope: &Scope, loop_ctx: Option<&LoopCtx>) -> Shape {
        let block_shape = Shape::Block(block);

        match self.cfg.get(block).exit() {
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if scope.implicit_exits.contains(target) =>
            {
                verbose!(indent: 2, "block {} exits to implicit target {}", block, target);
                block_shape
            }
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if loop_ctx.is_some_and(|ctx| ctx.continue_targets.contains(target)) =>
            {
                if loop_ctx.is_some_and(|ctx| ctx.implicit_continue_sources.contains(&block)) {
                    verbose!(
                        indent: 2,
                        "block {} exits through implicit loop tail to {}",
                        block,
                        target
                    );
                    return block_shape;
                }

                verbose!(indent: 2, "block {} exits to continue target {}", block, target);
                Shape::sequence([block_shape, Shape::Continue])
            }
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if loop_ctx.is_some_and(|ctx| ctx.exits.contains(target)) =>
            {
                verbose!(indent: 2, "block {} exits to break target {}", block, target);
                Shape::sequence([block_shape, Shape::Break])
            }
            BlockExit::Return(values) => Shape::sequence([
                block_shape,
                Shape::Return {
                    values: values.clone(),
                },
            ]),
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

    fn is_empty(&self) -> bool {
        matches!(self, Shape::Sequence(nodes) if nodes.is_empty())
    }

    fn lower(self, cfg: &ControlFlowGraph) -> RegionNode {
        match self {
            Shape::Block(block) => RegionNode::BasicBlock {
                stmts: cfg
                    .get(block)
                    .stmts()
                    .iter()
                    .map(|stmt| stmt.node.clone())
                    .collect(),
            },
            Shape::Sequence(nodes) => RegionNode::Sequence {
                nodes: nodes.into_iter().map(|node| node.lower(cfg)).collect(),
            },
            Shape::If(shape) => RegionNode::If {
                condition: shape.condition,
                then_branch: Box::new(shape.then_branch.lower(cfg)),
                else_branch: shape.else_branch.map(|branch| Box::new(branch.lower(cfg))),
            },
            Shape::Loop(shape) => match shape.kind {
                LoopKind::While { condition, .. } => RegionNode::While {
                    condition,
                    body: Box::new(shape.body.lower(cfg)),
                },
                LoopKind::RepeatUntil { condition, .. } => RegionNode::RepeatUntil {
                    condition,
                    body: Box::new(shape.body.lower(cfg)),
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
                    body: Box::new(shape.body.lower(cfg)),
                },
                LoopKind::GenericFor { vars, exprs, .. } => RegionNode::GenericFor {
                    vars,
                    exprs: exprs.into(),
                    body: Box::new(shape.body.lower(cfg)),
                },
                LoopKind::Infinite { .. } => RegionNode::While {
                    condition: HilExpr::Bool(true),
                    body: Box::new(shape.body.lower(cfg)),
                },
            },
            Shape::Break => RegionNode::Break,
            Shape::Continue => RegionNode::Continue,
            Shape::Return { values } => RegionNode::Return { values },
            Shape::VirtualExit => unreachable!("should have been unfolded already"),
        }
    }
}

/// Collect the natural loop body by walking predecessors back from `latch`
/// until `header` is reached. Returns the full set including header.
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

fn single_target(targets: &HashSet<usize>) -> Option<usize> {
    let mut targets = targets.iter().copied();
    let target = targets.next()?;
    targets.next().is_none().then_some(target)
}

fn merge_optional_body(lhs: Option<usize>, rhs: Option<usize>) -> Option<Option<usize>> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) if lhs != rhs => None,
        (Some(body), _) | (_, Some(body)) => Some(Some(body)),
        (None, None) => Some(None),
    }
}

fn and_expr(lhs: HilExpr, rhs: HilExpr) -> HilExpr {
    match (lhs, rhs) {
        (HilExpr::Bool(false), _) | (_, HilExpr::Bool(false)) => HilExpr::Bool(false),
        (HilExpr::Bool(true), expr) | (expr, HilExpr::Bool(true)) => expr,
        (lhs, rhs) => HilExpr::Binary {
            lhs: Box::new(lhs),
            op: BinOp::And,
            rhs: Box::new(rhs),
        },
    }
}

fn or_expr(lhs: HilExpr, rhs: HilExpr) -> HilExpr {
    match (lhs, rhs) {
        (HilExpr::Bool(true), _) | (_, HilExpr::Bool(true)) => HilExpr::Bool(true),
        (HilExpr::Bool(false), expr) | (expr, HilExpr::Bool(false)) => expr,
        (
            lhs,
            HilExpr::Binary {
                lhs: and_lhs,
                op: BinOp::And,
                rhs: and_rhs,
            },
        ) if lhs.clone().invert() == *and_lhs => or_expr(lhs, *and_rhs),
        (lhs, rhs) => HilExpr::Binary {
            lhs: Box::new(lhs),
            op: BinOp::Or,
            rhs: Box::new(rhs),
        },
    }
}

fn sorted_nodes(nodes: &HashSet<usize>) -> Vec<usize> {
    let mut nodes: Vec<_> = nodes.iter().copied().collect();
    nodes.sort_unstable();
    nodes
}

pub fn structure(cfg: &ControlFlowGraph) -> (RegionNode, bool) {
    let root = Structurer::new(cfg).structure().lower(cfg);
    (root, true)
}
