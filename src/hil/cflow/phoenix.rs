#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use smallvec::SmallVec;

use crate::{
    hil::{
        cflow::{
            cfg::{BlockExit, ControlFlowGraph},
            graph::{DominatorTree, GraphView, Reversed, SeseGraphView},
            region::RegionNode,
        },
        ir::HilExpr,
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
    head: usize,
    condition: HilExpr,
    then_branch: Box<Shape>,
    else_branch: Option<Box<Shape>>,
    merge: Option<usize>,
}

#[derive(Debug, Clone)]
struct LoopCtx {
    header: usize,
    continue_targets: HashSet<usize>,
    exits: HashSet<usize>,
}

#[derive(Debug, Clone)]
struct LoopShape {
    header: usize,
    kind: LoopKind,
    body: Box<Shape>,
    exits: HashSet<usize>,
}

/// Determines where a recovered loop condition belongs in the source shape.
#[derive(Debug, Clone)]
enum LoopKind {
    /// `while cond do`; condition is owned by the loop header.
    While { condition: HilExpr },
    /// `repeat ... until cond`; condition is owned by the loop latch.
    RepeatUntil { condition: HilExpr },
    /// `while true do`; loop exits are represented by `break`.
    Infinite,
}

/// The CFG boundary currently being structured.
#[derive(Debug, Clone)]
struct Scope {
    entry: usize,
    nodes: HashSet<usize>,
    exits: HashSet<usize>,
}

#[derive(Debug, Clone)]
struct ConditionalShape {
    head: usize,
    condition: HilExpr,
    then_entry: usize,
    else_entry: usize,
    merge: Option<usize>,
}

#[derive(Debug, Clone)]
struct LoopInfo {
    header: usize,
    latches: Vec<usize>,
    body: HashSet<usize>,
    exits: HashSet<usize>,
    parent: Option<usize>,
    children: Vec<usize>,
}

#[derive(Debug, Clone)]
struct LoopForest {
    loops: HashMap<usize, LoopInfo>,
    /// Headers sorted so that an inner loop always appears before its parent.
    innermost_first: Vec<usize>,
    /// For each block, the innermost loop header that contains it.
    innermost_loop_for_block: HashMap<usize, usize>,
}

impl LoopForest {
    fn build(cfg: &ControlFlowGraph, idoms: &DominatorTree) -> Self {
        let mut latches_by_header: HashMap<_, Vec<_>> = HashMap::new();
        for latch in cfg.iter() {
            for &succ in cfg.successors(latch) {
                if idoms.dominates(succ, latch) {
                    latches_by_header.entry(succ).or_default().push(latch);
                }
            }
        }

        let mut loops: HashMap<_, _> = latches_by_header
            .into_iter()
            .map(|(header, mut latches)| {
                latches.sort_unstable();
                latches.dedup();

                let body = latches
                    .iter()
                    .copied()
                    .fold(HashSet::new(), |mut body, latch| {
                        body.extend(natural_loop_body(cfg, header, latch));
                        body
                    });

                let exits = body
                    .iter()
                    .flat_map(|&block| cfg.successors(block).iter().copied())
                    .filter(|target| !body.contains(target))
                    .collect();

                (
                    header,
                    LoopInfo {
                        header,
                        latches,
                        body,
                        exits,
                        parent: None,
                        children: Vec::new(),
                    },
                )
            })
            .collect();

        let headers: Vec<_> = loops.keys().copied().collect();
        let parents: Vec<_> = headers
            .iter()
            .copied()
            .filter_map(|header| {
                let loop_body = &loops.get(&header)?.body;
                let parent = headers
                    .iter()
                    .copied()
                    .filter(|&candidate| candidate != header)
                    .filter(|&candidate| {
                        let candidate_body = &loops[&candidate].body;
                        loop_body.len() < candidate_body.len()
                            && loop_body.iter().all(|node| candidate_body.contains(node))
                    })
                    .min_by_key(|candidate| (loops[candidate].body.len(), *candidate))?;

                Some((header, parent))
            })
            .collect();

        for (header, parent) in parents {
            loops
                .get_mut(&header)
                .expect("child loop should exist")
                .parent = Some(parent);
            loops
                .get_mut(&parent)
                .expect("parent loop should exist")
                .children
                .push(header);
        }

        for info in loops.values_mut() {
            info.children.sort_unstable();
        }

        let mut innermost_first: Vec<_> = loops.keys().copied().collect();
        innermost_first.sort_by_key(|header| (loops[header].body.len(), *header));

        let mut innermost_loop_for_block = HashMap::new();
        for &header in innermost_first.iter().rev() {
            for &block in &loops[&header].body {
                innermost_loop_for_block.insert(block, header);
            }
        }

        Self {
            loops,
            innermost_first,
            innermost_loop_for_block,
        }
    }

    fn get(&self, header: usize) -> Option<&LoopInfo> {
        self.loops.get(&header)
    }

    fn is_nested_in(&self, inner_header: usize, outer_header: usize) -> bool {
        let mut current = self.get(inner_header).and_then(|info| info.parent);

        while let Some(header) = current {
            if header == outer_header {
                return true;
            }
            current = self.get(header).and_then(|info| info.parent);
        }

        false
    }

    fn direct_children(&self, header: usize) -> &[usize] {
        self.get(header)
            .map_or(&[], |info| info.children.as_slice())
    }

    fn is_loop_header(&self, node: usize) -> bool {
        self.loops.contains_key(&node)
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
            entry: cfg.entry_block,
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
        };

        self.structure_scope(&scope, None)
    }

    fn structure_scope(&self, scope: &Scope, loop_ctx: Option<&LoopCtx>) -> Shape {
        let mut nodes = Vec::new();
        let mut visited = HashSet::new();
        let mut current = scope.entry;

        while scope.nodes.contains(&current)
            && !scope.exits.contains(&current)
            && visited.insert(current)
        {
            if let Some(loop_shape) = self.recognize_loop(current, scope) {
                let next = single_target(&loop_shape.exits);
                nodes.push(Shape::Loop(loop_shape));

                let Some(next) = next else {
                    break;
                };
                current = next;
                continue;
            }

            if let Some(conditional) = self.recognize_conditional(current, scope) {
                let merge = conditional.merge;

                if !self.cfg.blocks[current].stmts.is_empty() {
                    nodes.push(Shape::Block(current));
                }

                nodes.push(self.structure_conditional(conditional, scope, loop_ctx));

                let Some(merge) = merge else {
                    break;
                };
                current = merge;
                continue;
            }

            nodes.push(self.shape_for_block(current, loop_ctx));

            let next = self
                .graph
                .successors(current)
                .iter()
                .copied()
                .find(|succ| scope.nodes.contains(succ) || scope.exits.contains(succ));

            let Some(next) = next else {
                break;
            };

            if scope.exits.contains(&next) {
                break;
            }

            current = next;
        }

        Shape::sequence(nodes)
    }

    fn recognize_loop(&self, header: usize, scope: &Scope) -> Option<LoopShape> {
        let loop_info = self.loops.get(header)?;
        if !loop_info.body.iter().all(|node| scope.nodes.contains(node)) {
            return None;
        }

        let body_entry = self
            .graph
            .successors(header)
            .iter()
            .copied()
            .find(|succ| loop_info.body.contains(succ) && *succ != header)
            .unwrap_or(header);

        let mut body_nodes = loop_info.body.clone();

        // the header of a repeat/until is a normal block; only while discards it
        let kind = self.classify_loop(loop_info);
        if matches!(kind, LoopKind::While { .. }) {
            body_nodes.remove(&header);
        }

        let body_scope = Scope {
            entry: body_entry,
            nodes: body_nodes.clone(),
            exits: [header]
                .into_iter()
                .chain(loop_info.exits.iter().copied())
                .collect(),
        };

        let loop_ctx = LoopCtx {
            header,
            continue_targets: [header]
                .into_iter()
                .chain(loop_info.latches.iter().copied())
                .collect(),
            exits: loop_info.exits.clone(),
        };

        verbose!("loop:");
        verbose!(indent: 1, "header = {}", header);
        verbose!(indent: 1, "body = {:?}", body_nodes);
        verbose!(indent: 1, "exits = {:?}", loop_info.exits);

        Some(LoopShape {
            header,
            kind,
            body: Box::new(self.structure_scope(&body_scope, Some(&loop_ctx))),
            exits: loop_info.exits.clone(),
        })
    }

    fn recognize_conditional(&self, head: usize, scope: &Scope) -> Option<ConditionalShape> {
        let BlockExit::CondJump {
            cond,
            then_block,
            else_block,
        } = &self.cfg.blocks.get(head)?.exit
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
    ) -> Shape {
        let mut branch_exits = scope.exits.clone();
        if let Some(merge) = shape.merge {
            branch_exits.insert(merge);
        }

        let then_nodes = self.collect_reachable_until(shape.then_entry, scope, &branch_exits);
        let else_nodes = self.collect_reachable_until(shape.else_entry, scope, &branch_exits);

        let build_branch = |entry: usize, nodes: HashSet<usize>| {
            if nodes.is_empty() {
                // If the branch naturally falls through to the merge point, it's just empty.
                if Some(entry) == shape.merge {
                    return Shape::sequence(Vec::new());
                }

                // If the branch jumps out of the region entirely, map it to the correct exit instruction.
                if let Some(ctx) = loop_ctx {
                    if ctx.exits.contains(&entry) {
                        return Shape::Break;
                    }
                    if ctx.continue_targets.contains(&entry) {
                        return Shape::Continue;
                    }
                }

                // Catch edge cases where an empty branch is a direct return
                if let BlockExit::Return(values) = &self.cfg.blocks[entry].exit {
                    return Shape::Return {
                        values: values.clone(),
                    };
                }

                return Shape::sequence(Vec::new());
            }

            let branch_scope = Scope {
                entry,
                nodes,
                exits: branch_exits.clone(),
            };
            self.structure_scope(&branch_scope, loop_ctx)
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

        // if loop header is also a latch, and the header's CondJump has one edge back to itself and one edge out, this is a post-test loop
        if loop_info.latches.contains(&loop_info.header)
            && let BlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } = &self.cfg.blocks[loop_info.header].exit
            && (*then_block == loop_info.header) ^ (*else_block == loop_info.header)
        {
            verbose!(indent:1, "kind = RepeatUntil");
            verbose!(indent:1, "condition = ({})", cond);
            return LoopKind::RepeatUntil {
                condition: cond.clone(),
            };
        }

        if let BlockExit::CondJump { cond, .. } = &self.cfg.blocks[loop_info.header].exit {
            verbose!(indent:1, "kind = While");
            verbose!(indent:1, "condition = ({})", cond);
            return LoopKind::While {
                condition: cond.clone(),
            };
        }

        verbose!(indent:1, "kind=Infinite");
        LoopKind::Infinite
    }

    fn find_merge_point(&self, node: usize, scope: &Scope) -> Option<usize> {
        let merge = self.ipdoms.idom(node)?;
        (scope.nodes.contains(&merge) && !scope.exits.contains(&merge)).then_some(merge)
    }

    fn shape_for_block(&self, block: usize, loop_ctx: Option<&LoopCtx>) -> Shape {
        let block_shape = Shape::Block(block);

        match &self.cfg.blocks[block].exit {
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if loop_ctx.is_some_and(|ctx| ctx.continue_targets.contains(target)) =>
            {
                Shape::sequence([block_shape, Shape::Continue])
            }
            BlockExit::Jump(target) | BlockExit::Fallthrough(target)
                if loop_ctx.is_some_and(|ctx| ctx.exits.contains(target)) =>
            {
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
    ) -> HashSet<usize> {
        let mut nodes = HashSet::new();
        let mut stack = vec![entry];

        while let Some(node) = stack.pop() {
            if exits.contains(&node) || !scope.nodes.contains(&node) || !nodes.insert(node) {
                continue;
            }

            stack.extend(self.graph.successors(node).iter().copied());
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
                stmts: cfg.blocks[block]
                    .stmts
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
                LoopKind::While { condition } => RegionNode::While {
                    condition,
                    body: Box::new(shape.body.lower(cfg)),
                },
                LoopKind::RepeatUntil { condition } => RegionNode::RepeatUntil {
                    condition,
                    body: Box::new(shape.body.lower(cfg)),
                },
                LoopKind::Infinite => RegionNode::While {
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
fn natural_loop_body(cfg: &ControlFlowGraph, header: usize, latch: usize) -> HashSet<usize> {
    let mut body = HashSet::new();
    body.insert(header);

    let mut stack = vec![latch];
    while let Some(node) = stack.pop() {
        if body.insert(node) && node != header {
            for &pred in cfg.predecessors(node) {
                stack.push(pred);
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

pub fn structure(cfg: &ControlFlowGraph) -> (RegionNode, bool) {
    let root = Structurer::new(cfg).structure().lower(cfg);
    (root, true)
}
