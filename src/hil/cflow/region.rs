use std::collections::{HashMap, HashSet};

use either::Either;
use smallvec::SmallVec;

use crate::hil::{
    cflow::{
        common::invert_condition,
        graph::{BlockExit, ControlFlowGraph, build_immediate_dominators},
    },
    ir::{HilExpr, HilStmt},
    lifter::ssa::SymbolId,
};

#[derive(Debug)]
enum Loop {
    While {
        cond: HilExpr,
        exit_block: usize,
    },
    RepeatUntil {
        // We don't need to hold cond here as it's a conditional jump inside the body.
        exit_block: usize,
    },
    /// A structured numeric `for` loop recovered from `FORNPREP/FORNLOOP`.
    NumericFor {
        var: SymbolId,
        start: HilExpr,
        end: HilExpr,
        step: HilExpr,
        prep_block: usize,
        exit_block: usize,
    },
    /// A structured generic `for` loop recovered from `FORGPREP/FORGLOOP`.
    GenericFor {
        vars: SmallVec<[SymbolId; 3]>,
        exprs: [HilExpr; 3],
        prep_block: usize,
        exit_block: usize,
    },
}

impl Loop {
    fn exit_block(&self) -> usize {
        match self {
            Loop::While { exit_block, .. }
            | Loop::RepeatUntil { exit_block, .. }
            | Loop::NumericFor { exit_block, .. }
            | Loop::GenericFor { exit_block, .. } => *exit_block,
        }
    }
}

/// One structured control-flow node in the intermediate region tree.
#[derive(Debug, Clone)]
pub enum CfgNode {
    /// A plain basic block payload that does not by itself decide control transfer.
    BasicBlock { block: usize },
    /// A sequence of nodes executed sequentially.
    Sequence { nodes: Vec<CfgNode> },
    /// A structured if/else split.
    If {
        condition: HilExpr,
        then_branch: Box<CfgNode>,
        else_branch: Option<Box<CfgNode>>,
    },
    /// A structured while loop recovered from backedges.
    While {
        condition: HilExpr,
        body: Box<CfgNode>,
    },
    /// A structured numeric `for` loop recovered from `FORNPREP/FORNLOOP`.
    NumericFor {
        var: SymbolId,
        start: HilExpr,
        end: HilExpr,
        step: HilExpr,
        body: Box<CfgNode>,
    },
    /// A structured generic `for` loop recovered from `FORGPREP/FORGLOOP`.
    GenericFor {
        vars: SmallVec<[SymbolId; 3]>,
        exprs: [HilExpr; 3],
        body: Box<CfgNode>,
    },
    /// Explicit `continue` edge for a recovered loop.
    Continue,
    /// Explicit `break` edge from a loop body.
    Break,
    /// Explicit return.
    Return { values: SmallVec<[HilExpr; 3]> },

    /// A temporary scaffolding node used to merge multiple physical exits
    /// into a Single-Entry, Single-Exit (SESE) graph.
    VirtualExit,
}

/// A region node in the structured control flow graph.
#[derive(Debug, Clone)]
pub enum RegionNode {
    /// A plain basic block payload that does not by itself decide control transfer.
    BasicBlock { stmts: Vec<HilStmt> },
    /// A sequence of nodes executed sequentially.
    Sequence { nodes: Vec<RegionNode> },
    /// A structured if/else split.
    If {
        condition: HilExpr,
        then_branch: Box<RegionNode>,
        else_branch: Option<Box<RegionNode>>,
    },
    /// A structured while loop recovered from backedges.
    While {
        condition: HilExpr,
        body: Box<RegionNode>,
    },
    /// A structured numeric `for` loop recovered from `FORNPREP/FORNLOOP`.
    NumericFor {
        var: SymbolId,
        start: HilExpr,
        end: HilExpr,
        step: HilExpr,
        body: Box<RegionNode>,
    },
    /// A structured generic `for` loop recovered from `FORGPREP/FORGLOOP`.
    GenericFor {
        vars: SmallVec<[SymbolId; 3]>,
        exprs: [HilExpr; 3],
        body: Box<RegionNode>,
    },
    /// Explicit `continue` edge for a recovered loop.
    Continue,
    /// Explicit `break` edge from a loop body.
    Break,
    /// Explicit return.
    Return { values: SmallVec<[HilExpr; 3]> },
}

impl CfgNode {
    /// Merges nodes into a `Sequence` node, flattening nested sequences.
    fn merge(nodes: impl IntoIterator<Item = CfgNode>) -> CfgNode {
        let seq_nodes = nodes
            .into_iter()
            .flat_map(|node| match node {
                CfgNode::Sequence { nodes } => Either::Left(nodes.into_iter()),
                other => Either::Right(std::iter::once(other)),
            })
            .collect();

        CfgNode::Sequence { nodes: seq_nodes }
    }

    /// Recursively replaces raw basic blocks that jump to the loop header/exit
    /// with explicit Break and Continue nodes.
    pub fn resolve_escapes(
        &mut self,
        continue_target: usize,
        continue_target_alt: Option<usize>,
        exit: usize,
        cfg: &ControlFlowGraph,
        region_map: &HashMap<usize, usize>,
    ) {
        match self {
            CfgNode::Sequence { nodes } => nodes.iter_mut().for_each(|n| {
                n.resolve_escapes(continue_target, continue_target_alt, exit, cfg, region_map)
            }),
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                then_branch.resolve_escapes(
                    continue_target,
                    continue_target_alt,
                    exit,
                    cfg,
                    region_map,
                );
                if let Some(e) = else_branch {
                    e.resolve_escapes(continue_target, continue_target_alt, exit, cfg, region_map);
                }
            }
            CfgNode::BasicBlock { block } => {
                let exit_node = &cfg.blocks[*block].exit;

                let replacement = match exit_node {
                    BlockExit::Jump(raw_target) => {
                        let active = region_map[raw_target];
                        if active == continue_target {
                            Some(CfgNode::Continue)
                        } else if active == exit {
                            Some(CfgNode::Break)
                        } else {
                            None
                        }
                    }
                    BlockExit::Fallthrough(raw_target) => {
                        let active = region_map[raw_target];
                        if active == exit {
                            Some(CfgNode::Break)
                        } else {
                            None
                        }
                    }
                    BlockExit::CondJump {
                        cond,
                        then_block,
                        else_block,
                    } => {
                        let active_then = region_map[then_block];
                        let active_else = region_map[else_block];

                        let then_terminal = if active_then == continue_target
                            || continue_target_alt.is_some_and(|t| *then_block == t)
                        {
                            Some(CfgNode::Continue)
                        } else if active_then == exit {
                            Some(CfgNode::Break)
                        } else {
                            None
                        };

                        let else_terminal = if active_else == continue_target
                            || continue_target_alt.is_some_and(|t| *else_block == t)
                        {
                            Some(CfgNode::Continue)
                        } else if active_else == exit {
                            Some(CfgNode::Break)
                        } else {
                            None
                        };

                        match (then_terminal, else_terminal) {
                            (None, None) => None,
                            (Some(terminal), None) => Some(CfgNode::If {
                                condition: cond.clone(),
                                then_branch: Box::new(terminal),
                                else_branch: None,
                            }),
                            (None, Some(terminal)) => Some(CfgNode::If {
                                condition: invert_condition(cond.clone()),
                                then_branch: Box::new(terminal),
                                else_branch: None,
                            }),
                            (Some(then_terminal), Some(else_terminal)) => Some(CfgNode::If {
                                condition: cond.clone(),
                                then_branch: Box::new(then_terminal),
                                else_branch: Some(Box::new(else_terminal)),
                            }),
                        }
                    }
                    _ => None,
                };

                if let Some(terminal) = replacement {
                    *self = CfgNode::Sequence {
                        nodes: vec![CfgNode::BasicBlock { block: *block }, terminal],
                    };
                }
            }
            _ => {}
        }
    }

    fn strip_virtual_exits(&mut self) {
        match self {
            CfgNode::Sequence { nodes } => {
                nodes.retain(|n| !matches!(n, CfgNode::VirtualExit));
                for node in nodes {
                    node.strip_virtual_exits();
                }
            }
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                then_branch.strip_virtual_exits();
                if let Some(e) = else_branch {
                    e.strip_virtual_exits();
                }
            }
            CfgNode::While { body, .. }
            | CfgNode::NumericFor { body, .. }
            | CfgNode::GenericFor { body, .. } => {
                body.strip_virtual_exits();
            }
            _ => {}
        }
    }

    /// Recursively replaces raw basic blocks that terminate with a return
    /// with explicit Return nodes.
    fn resolve_returns(&mut self, cfg: &ControlFlowGraph) {
        match self {
            CfgNode::Sequence { nodes } => {
                for node in nodes.iter_mut() {
                    node.resolve_returns(cfg);
                }
            }
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                then_branch.resolve_returns(cfg);
                if let Some(e) = else_branch {
                    e.resolve_returns(cfg);
                }
            }
            CfgNode::While { body, .. }
            | CfgNode::NumericFor { body, .. }
            | CfgNode::GenericFor { body, .. } => {
                body.resolve_returns(cfg);
            }
            CfgNode::BasicBlock { block } => {
                if let BlockExit::Return(values) = &cfg.blocks[*block].exit {
                    let terminal = CfgNode::Return {
                        values: values.clone(),
                    };

                    *self = CfgNode::Sequence {
                        nodes: vec![CfgNode::BasicBlock { block: *block }, terminal],
                    };
                }
            }
            _ => {}
        }
    }

    /// Returns whether this node starts with the given raw CFG block.
    ///
    /// Sequence nodes recurse into their first child so merged wrappers do not
    /// hide the real leading block.
    fn starts_with_block(&self, block: usize) -> bool {
        match self {
            CfgNode::BasicBlock { block: id } => *id == block,
            CfgNode::Sequence { nodes } => nodes
                .first()
                .is_some_and(|first| first.starts_with_block(block)),
            _ => false,
        }
    }

    /// Returns whether this node ends in an explicit loop escape statement.
    fn ends_with_escape(&self) -> bool {
        match self {
            CfgNode::Continue | CfgNode::Break => true,
            CfgNode::Sequence { nodes } => nodes.last().is_some_and(|n| n.ends_with_escape()),
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                then_branch.ends_with_escape()
                    && else_branch.as_ref().is_some_and(|e| e.ends_with_escape())
            }
            _ => false,
        }
    }

    /// Lowers the node into an owned [`RegionNode`], consuming the control flow graph.
    fn lower(self, cfg: &ControlFlowGraph) -> RegionNode {
        match self {
            CfgNode::BasicBlock { block } => RegionNode::BasicBlock {
                // TODO: `std::mem::take` here to avoid cloning?
                stmts: cfg.blocks[block]
                    .stmts
                    .iter()
                    .cloned()
                    .map(|stmt| stmt.inner)
                    .collect(),
            },
            CfgNode::Sequence { nodes } => {
                // Because we now own the statements, we can flatten sequences of
                // BasicBlocks into one basic block with chained statements.
                let mut out = Vec::new();
                let mut buf = Vec::new();

                for n in nodes {
                    match n.lower(cfg) {
                        RegionNode::BasicBlock { stmts } => buf.extend(stmts),
                        other => {
                            if !buf.is_empty() {
                                out.push(RegionNode::BasicBlock {
                                    stmts: std::mem::take(&mut buf),
                                });
                            }
                            out.push(other);
                        }
                    }
                }
                if !buf.is_empty() {
                    out.push(RegionNode::BasicBlock { stmts: buf });
                }
                RegionNode::Sequence {
                    nodes: flatten_regions(out),
                }
            }
            CfgNode::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => RegionNode::If {
                condition,
                then_branch: Box::new(then_branch.lower(cfg)),
                else_branch: else_branch.map(|e| Box::new(e.lower(cfg))),
            },
            CfgNode::While {
                condition, body, ..
            } => RegionNode::While {
                condition,
                body: Box::new(body.lower(cfg)),
            },
            CfgNode::NumericFor {
                var,
                start,
                end,
                step,
                body,
            } => RegionNode::NumericFor {
                var,
                start,
                end,
                step,
                body: Box::new(body.lower(cfg)),
            },
            CfgNode::GenericFor {
                vars, exprs, body, ..
            } => RegionNode::GenericFor {
                vars,
                exprs,
                body: Box::new(body.lower(cfg)),
            },
            CfgNode::Continue => RegionNode::Continue,
            CfgNode::Break => RegionNode::Break,
            CfgNode::Return { values } => RegionNode::Return { values },
            CfgNode::VirtualExit => unreachable!("should be stripped before lowering"),
        }
    }
}

pub struct FoldableGraph<'a> {
    cfg: &'a ControlFlowGraph,
    nodes: HashMap<usize, CfgNode>,
    region_for_block: HashMap<usize, usize>,

    entry_node: usize,
    exit_node: usize,

    successors: HashMap<usize, Vec<usize>>,
    predecessors: HashMap<usize, Vec<usize>>,

    idoms: Option<HashMap<usize, usize>>,
    postidoms: Option<HashMap<usize, usize>>,

    id_counter: usize,
}

impl<'a> FoldableGraph<'a> {
    pub fn new(cfg: &'a ControlFlowGraph) -> Self {
        let mut nodes: HashMap<_, _> = cfg
            .blocks
            .iter()
            .enumerate()
            .map(|(i, _)| (i, CfgNode::BasicBlock { block: i }))
            .collect();

        let mut successors: HashMap<_, _> = cfg.successors.iter().cloned().enumerate().collect();
        let mut predecessors: HashMap<_, _> =
            cfg.predecessors.iter().cloned().enumerate().collect();

        let terminal_nodes: Vec<_> = nodes
            .keys()
            .copied()
            .filter(|&id| successors.get(&id).is_none_or(|s| s.is_empty()))
            .collect();

        let mut id_counter = cfg.blocks.len();
        let exit_node = if terminal_nodes.len() == 1 {
            terminal_nodes[0]
        } else {
            // Because we have multiple exit points, we create a "virtual exit",
            // which all current exits point in order to have a complete SESE graph.
            let virtual_exit_id = id_counter;
            id_counter += 1;

            nodes.insert(virtual_exit_id, CfgNode::VirtualExit);

            for node in terminal_nodes {
                successors.entry(node).or_default().push(virtual_exit_id);
                predecessors.entry(virtual_exit_id).or_default().push(node);
            }
            successors.insert(virtual_exit_id, Vec::new());

            virtual_exit_id
        };

        let mut reachable = HashSet::new();
        let mut stack = vec![cfg.entry_block];
        while let Some(node) = stack.pop() {
            if reachable.insert(node)
                && let Some(succs) = successors.get(&node)
            {
                stack.extend(succs.iter().copied());
            }
        }

        let all_nodes: Vec<_> = nodes.keys().copied().collect();
        for node in all_nodes {
            if !reachable.contains(&node) {
                nodes.remove(&node);

                if let Some(succs) = successors.remove(&node) {
                    for succ in succs {
                        if let Some(preds) = predecessors.get_mut(&succ) {
                            preds.retain(|&p| p != node);
                        }
                    }
                }
                predecessors.remove(&node);
            }
        }

        FoldableGraph {
            cfg,
            nodes,
            region_for_block: (0..cfg.blocks.len()).map(|i| (i, i)).collect(),
            entry_node: cfg.entry_block,
            exit_node,
            successors,
            predecessors,
            idoms: None,
            postidoms: None,
            id_counter,
        }
    }

    /// Returns the next available node ID and increments the counter.
    fn next_id(&mut self) -> usize {
        let id = self.id_counter;
        self.id_counter += 1;
        id
    }

    /// Lazily recalculates the immediate dominators for each node in the graph.
    fn get_or_calc_idoms(&mut self) -> &HashMap<usize, usize> {
        match self.idoms {
            Some(ref idoms) => idoms,
            None => {
                self.idoms = Some(build_idoms_sparse(
                    self.entry_node,
                    self.nodes.keys().copied(),
                    &self.successors,
                    &self.predecessors,
                ));
                self.idoms.as_ref().unwrap()
            }
        }
    }

    /// Lazily recalculates the post-dominators for each node in the graph.
    fn get_or_calc_postidoms(&mut self) -> &HashMap<usize, usize> {
        match self.postidoms {
            Some(ref doms) => doms,
            None => {
                self.postidoms = Some(build_idoms_sparse(
                    self.exit_node,
                    self.nodes.keys().copied(),
                    &self.predecessors,
                    &self.successors,
                ));
                self.postidoms.as_ref().unwrap()
            }
        }
    }

    /// Invalidates the cached immediate dominators and post-dominators,
    /// forcing a recalculation on the next `get_or_calc*` call.
    fn invalidate_doms(&mut self) {
        self.idoms = None;
        self.postidoms = None;
    }

    /// Transfers all predecessors from `from` to `to`, updating the successor list of each predecessor.
    fn transfer_predecessors(&mut self, from: usize, to: usize) {
        let preds = self.predecessors.remove(&from).unwrap_or_default();
        for p in &preds {
            if let Some(succs) = self.successors.get_mut(p) {
                for s in succs.iter_mut() {
                    if *s == from {
                        *s = to;
                    }
                }
            }
        }
        self.predecessors.entry(to).or_default().extend(preds);
    }

    /// Transfers all successors from `from` to `to`, updating the predecessor list of each successor.
    fn transfer_successors(&mut self, from: usize, to: usize) {
        let succs = self.successors.remove(&from).unwrap_or_default();
        for s in &succs {
            if let Some(preds) = self.predecessors.get_mut(s) {
                for p in preds.iter_mut() {
                    if *p == from {
                        *p = to;
                    }
                }
            }
        }
        self.successors.entry(to).or_default().extend(succs);
    }

    fn update_regionmap(&mut self, mut pred: impl FnMut(usize) -> bool, new: usize) {
        for val in self.region_for_block.values_mut() {
            if pred(*val) {
                *val = new;
            }
        }
    }

    /// Returns the exact successors of a node, if the successor count matches `N`.
    fn exact_successors<const N: usize>(&self, node: usize) -> Option<[usize; N]> {
        self.successors
            .get(&node)
            .and_then(|v| v.as_slice().try_into().ok())
    }

    /// Returns the exact predecessors of a node, if the predecessor count matches `N`.
    fn exact_predecessors<const N: usize>(&self, node: usize) -> Option<[usize; N]> {
        self.predecessors
            .get(&node)
            .and_then(|v| v.as_slice().try_into().ok())
    }

    fn should_preserve_loop_exit_stub(&self, node: usize) -> bool {
        let Some([pred]) = self.exact_predecessors(node) else {
            return false;
        };

        let Some((_, raw_then, raw_else)) = self.extract_cond_jump(&self.nodes[&pred]) else {
            return false;
        };

        let Some(&active_then) = self.region_for_block.get(&raw_then) else {
            return false;
        };
        let Some(&active_else) = self.region_for_block.get(&raw_else) else {
            return false;
        };

        (active_then == pred && active_else == node) || (active_else == pred && active_then == node)
    }

    /// Collapses sequentially executed blocks into a `BlockSequence` node.
    fn collapse_sequential(&mut self) -> bool {
        // Theory: If a basic block A has only one successor B, and B has only one predecessor A,
        // then A and B are sequential and can be collapsed into a `BlockSequence` node.

        let mut changed = false;

        let mut work = self.post_order();
        while let Some(curr) = work.pop() {
            if !self.nodes.contains_key(&curr) {
                continue;
            }

            if let Some([next]) = self.exact_successors(curr)
                && let Some([prev]) = self.exact_predecessors(next)
                && prev == curr
                && curr != next
                && !self.should_preserve_loop_exit_stub(curr)
            {
                let seq_id = self.next_id();

                let node_a = self.nodes.remove(&curr).unwrap();
                let node_b = self.nodes.remove(&next).unwrap();

                self.nodes.insert(seq_id, CfgNode::merge([node_a, node_b]));

                self.update_regionmap(|val| val == curr || val == next, seq_id);

                self.transfer_predecessors(curr, seq_id);
                self.transfer_successors(next, seq_id);

                self.successors.remove(&curr);
                self.predecessors.remove(&next);

                if curr == self.entry_node {
                    self.entry_node = seq_id;
                }
                if next == self.exit_node {
                    self.exit_node = seq_id;
                }
                self.invalidate_doms();

                work.push(seq_id);
                changed = true;
            }
        }

        changed
    }

    fn extract_exit(&self, node: &CfgNode) -> Option<&BlockExit> {
        match node {
            CfgNode::BasicBlock { block } => Some(&self.cfg.blocks[*block].exit),
            CfgNode::Sequence { nodes } => nodes.last().and_then(|n| self.extract_exit(n)),
            _ => None,
        }
    }

    fn extract_cond_jump(&self, node: &CfgNode) -> Option<(HilExpr, usize, usize)> {
        if let Some(BlockExit::CondJump {
            cond,
            then_block,
            else_block,
        }) = self.extract_exit(node)
        {
            Some((cond.clone(), *then_block, *else_block))
        } else {
            None
        }
    }

    fn node_emits_statements(&self, node: &CfgNode) -> bool {
        match node {
            CfgNode::BasicBlock { block } => !self.cfg.blocks[*block].stmts.is_empty(),
            CfgNode::Sequence { nodes } => {
                nodes.iter().any(|node| self.node_emits_statements(node))
            }
            CfgNode::If { .. }
            | CfgNode::While { .. }
            | CfgNode::NumericFor { .. }
            | CfgNode::GenericFor { .. }
            | CfgNode::Continue
            | CfgNode::Break
            | CfgNode::Return { .. } => true,
            CfgNode::VirtualExit => false,
        }
    }

    /// Restructures a loop header's conditional branch into a structured if-then-else
    /// or one-armed if guard, pulling the target branches out of the body sequence.
    ///
    /// When the loop header has a CondJump, this function identifies the branch targets
    /// in the body sequence and restructures them. If both targets end with escape
    /// (break/continue), they're pulled into an if-then-else at the top. If only one
    /// target escapes, a one-armed guard is created. If neither escapes, both branches
    /// are still restructured into an if-then-else since the conditional must be
    /// represented in the output.
    fn fold_head_escape_guard(&self, head_node: CfgNode, body_ast: CfgNode) -> CfgNode {
        let Some((mut cond, then_block, else_block)) = self.extract_cond_jump(&head_node) else {
            return CfgNode::merge([head_node, body_ast]);
        };

        let CfgNode::Sequence { mut nodes } = body_ast else {
            return CfgNode::merge([head_node, body_ast]);
        };

        let then_idx = nodes
            .iter()
            .position(|node| node.starts_with_block(then_block));
        let else_idx = nodes
            .iter()
            .position(|node| node.starts_with_block(else_block));

        let Some((then_idx, else_idx)) = (match (then_idx, else_idx) {
            (Some(t), Some(e)) if t != e => Some((t, e)),
            _ => {
                return CfgNode::merge([head_node, CfgNode::Sequence { nodes }]);
            }
        }) else {
            return CfgNode::merge([head_node, CfgNode::Sequence { nodes }]);
        };

        let then_escape = nodes[then_idx].ends_with_escape();
        let else_escape = nodes[else_idx].ends_with_escape();

        if then_escape && else_escape {
            let mut guarded = Vec::with_capacity(nodes.len() + 2);
            guarded.push(head_node);
            let mut then_node = None;
            let mut else_node = None;
            let mut remove_order = [then_idx, else_idx];
            remove_order.sort_unstable_by(|a, b| b.cmp(a));

            for idx in remove_order {
                let removed = nodes.remove(idx);
                if idx == then_idx {
                    then_node = Some(removed);
                } else {
                    else_node = Some(removed);
                }
            }

            guarded.push(CfgNode::If {
                condition: cond,
                then_branch: Box::new(then_node.unwrap()),
                else_branch: Some(Box::new(else_node.unwrap())),
            });
            guarded.extend(nodes);
            return CfgNode::Sequence { nodes: guarded };
        }

        if let Some((escape_idx, invert)) = if then_escape {
            Some((then_idx, false))
        } else if else_escape {
            Some((else_idx, true))
        } else {
            None
        } {
            if invert {
                cond = invert_condition(cond);
            }

            let mut guarded = Vec::with_capacity(nodes.len() + 2);
            guarded.push(head_node);

            let escape_node = nodes.remove(escape_idx);
            guarded.push(CfgNode::If {
                condition: cond,
                then_branch: Box::new(escape_node),
                else_branch: None,
            });
            guarded.extend(nodes);

            return CfgNode::Sequence { nodes: guarded };
        }

        // Neither branch always escapes, but both targets are present in the body.
        // Restructure into an if-then-else to properly represent the conditional.
        // Remaining nodes (after removing then and else targets) are appended to
        // the then branch, as they logically belong to the "then" path's fall-through.
        let mut then_node_val = None;
        let mut else_node_val = None;
        let mut remove_order = [then_idx, else_idx];
        remove_order.sort_unstable_by(|a, b| b.cmp(a));

        for idx in remove_order {
            let removed = nodes.remove(idx);
            if idx == then_idx {
                then_node_val = Some(removed);
            } else {
                else_node_val = Some(removed);
            }
        }

        let then_branch = CfgNode::merge(std::iter::once(then_node_val.unwrap()).chain(nodes));
        let else_branch = else_node_val.unwrap();

        CfgNode::Sequence {
            nodes: vec![
                head_node,
                CfgNode::If {
                    condition: cond,
                    then_branch: Box::new(then_branch),
                    else_branch: Some(Box::new(else_branch)),
                },
            ],
        }
    }

    /// Folds one conditional in a sequence into an explicit escape guard.
    ///
    /// Detects `head` blocks whose branch targets are represented later in the
    /// same sequence and where at least one target ends in `break`/`continue`.
    /// Rewrites the suffix via `fold_head_escape_guard`.
    fn fold_escape_guard_in_sequence(&self, nodes: &mut Vec<CfgNode>) -> bool {
        for i in 0..nodes.len() {
            let Some((cond, then_block, else_block)) = self.extract_cond_jump(&nodes[i]) else {
                continue;
            };

            let then_idx =
                (i + 1..nodes.len()).find(|&idx| nodes[idx].starts_with_block(then_block));
            let else_idx =
                (i + 1..nodes.len()).find(|&idx| nodes[idx].starts_with_block(else_block));

            if let Some(escape_idx) = then_idx
                && else_idx.is_none()
                && nodes[escape_idx].ends_with_escape()
            {
                let suffix = nodes.split_off(i + 1);
                let head = nodes.pop().unwrap();
                let mut suffix_nodes = suffix;

                let suffix_escape_idx = suffix_nodes
                    .iter()
                    .position(|node| node.starts_with_block(then_block))
                    .unwrap();
                let escape_node = suffix_nodes.remove(suffix_escape_idx);

                nodes.push(head);
                nodes.push(CfgNode::If {
                    condition: cond,
                    then_branch: Box::new(escape_node),
                    else_branch: None,
                });
                nodes.extend(suffix_nodes);
                return true;
            }

            if let Some(escape_idx) = else_idx
                && then_idx.is_none()
                && nodes[escape_idx].ends_with_escape()
            {
                let suffix = nodes.split_off(i + 1);
                let head = nodes.pop().unwrap();
                let mut suffix_nodes = suffix;

                let suffix_escape_idx = suffix_nodes
                    .iter()
                    .position(|node| node.starts_with_block(else_block))
                    .unwrap();
                let escape_node = suffix_nodes.remove(suffix_escape_idx);

                nodes.push(head);
                nodes.push(CfgNode::If {
                    condition: invert_condition(cond),
                    then_branch: Box::new(escape_node),
                    else_branch: None,
                });
                nodes.extend(suffix_nodes);
                return true;
            }

            let Some(then_idx) = then_idx else {
                continue;
            };
            let Some(else_idx) = else_idx else {
                continue;
            };
            if then_idx == else_idx {
                continue;
            }

            let then_escape = nodes[then_idx].ends_with_escape();
            let else_escape = nodes[else_idx].ends_with_escape();
            if !then_escape && !else_escape {
                continue;
            }

            let suffix = nodes.split_off(i + 1);
            let head = nodes.pop().unwrap();
            let folded = self.fold_head_escape_guard(head, CfgNode::Sequence { nodes: suffix });

            match folded {
                CfgNode::Sequence {
                    nodes: mut folded_nodes,
                } => nodes.append(&mut folded_nodes),
                other => nodes.push(other),
            }

            return true;
        }

        false
    }

    fn normalize_escape_guards(&self, node: &mut CfgNode) {
        match node {
            CfgNode::Sequence { nodes } => {
                for node in nodes.iter_mut() {
                    self.normalize_escape_guards(node);
                }

                while self.fold_escape_guard_in_sequence(nodes) {}
            }
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.normalize_escape_guards(then_branch);
                if let Some(else_branch) = else_branch {
                    self.normalize_escape_guards(else_branch);
                }
            }
            CfgNode::While { body, .. }
            | CfgNode::NumericFor { body, .. }
            | CfgNode::GenericFor { body, .. } => self.normalize_escape_guards(body),
            _ => {}
        }
    }

    /// Returns whether `dom` dominates `node`.
    #[must_use]
    pub fn dominates(&mut self, dom: usize, node: usize) -> bool {
        let idoms = self.get_or_calc_idoms();
        if dom == node {
            return true;
        }
        let mut current = node;
        loop {
            match idoms.get(&current).copied() {
                Some(idom) if idom == dom => return true,
                Some(idom) => current = idom,
                None => return false,
            }
        }
    }

    /// Collapses conditionally executed blocks into a `If` node.
    fn collapse_conditional(&mut self) -> bool {
        // Let 'Head' be a node with exactly two successors: 'Left' and 'Right'
        //
        // Theory(if):
        // If 'Left' has exactly one predecessor ('Head') and exactly one successor ('Right'),
        // then subgraph [Head, Left] is a SESE region. [Head, Left] is collapsed into a new `If` node,
        // and its successor wired to 'Right'.
        // (This applies symmetrically if `Right` is the body and `Left` is the merge point).
        // ```luau
        // [Head]
        // if <cond> then
        //   [Left]
        // end
        // [Right]
        // ```
        //
        // Theory(if-else):
        // Let 'Merge' be the immediate post-dominator of 'Head'. If both 'Left' and 'Right' have exactly
        // one predecessor ('Head'), and exactly one successor ('Merge'), then subgraph [Head, Left, Right]
        // is a SESE region. [Head, Left, Right] is collapsed into a new `If` node, and its successor wired to 'Merge'.
        // ```luau
        // [Head]
        // if <cond> then
        //   [Left]
        // else
        //   [Right]
        // end
        // [Merge]
        // ```
        //
        // Both patterns must also not have any loop edges.

        let mut work = self.post_order();
        work.reverse();

        while let Some(head) = work.pop() {
            if !self.nodes.contains_key(&head) {
                continue;
            }

            if let Some([left, right]) = self.exact_successors(head) {
                let Some(tail) = self.get_or_calc_postidoms().get(&head).copied() else {
                    continue;
                };

                let Some((mut cond, raw_then, raw_else)) =
                    self.extract_cond_jump(&self.nodes[&head])
                else {
                    continue;
                };

                let active_then = self.region_for_block[&raw_then];
                let active_else = self.region_for_block[&raw_else];

                let (left, right) = if left == active_then && right == active_else {
                    (left, right)
                } else if left == active_else && right == active_then {
                    cond = invert_condition(cond);
                    (right, left)
                } else {
                    continue;
                };

                // A block is a strict body if it only comes from Head, and only goes to Tail.
                let is_strict_body = |node: usize, tail: usize| {
                    self.exact_predecessors(node).is_some_and(|p| p == [head])
                        && self.exact_successors(node).is_some_and(|s| s == [tail])
                };

                // TODO: clean this shitchain up
                let mut then_node_id = None;
                let mut else_node_id = None;

                if left == tail && is_strict_body(right, tail) {
                    // If-Then (The body is on the FALSE path)
                    then_node_id = Some(right);
                    cond = invert_condition(cond);
                } else if right == tail && is_strict_body(left, tail) {
                    // If-Then (The body is on the TRUE path)
                    then_node_id = Some(left);
                } else if is_strict_body(left, tail) && is_strict_body(right, tail) {
                    // If-Then-Else
                    then_node_id = Some(left);
                    else_node_id = Some(right);
                }

                let Some(then_node_id) = then_node_id else {
                    continue;
                };

                let new_id = self.next_id();
                let header_node = self.nodes.remove(&head).unwrap();
                let then_ast = Box::new(self.nodes.remove(&then_node_id).unwrap());
                let else_ast = else_node_id.map(|id| Box::new(self.nodes.remove(&id).unwrap()));
                self.nodes.insert(
                    new_id,
                    CfgNode::merge([
                        header_node,
                        CfgNode::If {
                            condition: cond,
                            then_branch: then_ast,
                            else_branch: else_ast,
                        },
                    ]),
                );
                self.transfer_predecessors(head, new_id);

                self.update_regionmap(
                    |val| val == head || val == then_node_id || Some(val) == else_node_id,
                    new_id,
                );

                if let Some(tail_preds) = self.predecessors.get_mut(&tail) {
                    tail_preds
                        .retain(|&p| p != head && p != then_node_id && Some(p) != else_node_id);
                    tail_preds.push(new_id)
                }

                self.successors.insert(new_id, vec![tail]);

                self.successors.remove(&head);
                self.successors.remove(&then_node_id);
                self.predecessors.remove(&then_node_id);

                if let Some(else_id) = else_node_id {
                    self.successors.remove(&else_id);
                    self.predecessors.remove(&else_id);
                }

                if head == self.entry_node {
                    self.entry_node = new_id;
                }
                self.invalidate_doms();

                return true;
            }
        }

        false
    }

    /// Returns the first found backedge from `node` if one exists, otherwise `None`.
    fn find_backedge(&mut self, node: usize) -> Option<usize> {
        for i in 0..self.predecessors.get(&node)?.len() {
            let pred = self.predecessors[&node][i];
            if self.dominates(node, pred) {
                return Some(pred);
            }
        }
        None
    }

    /// Identifies all nodes belonging to a SESE loop region.
    #[must_use]
    fn get_loop_region(&mut self, head: usize, exit: usize) -> HashSet<usize> {
        self.post_order()
            .into_iter()
            .filter(|&node| self.dominates(head, node) && !self.dominates(exit, node))
            .collect()
    }

    /// Computes the standard "natural loop" (only nodes that reach the backedge)
    /// strictly to safely identify the loop type and exit block.
    #[must_use]
    fn get_natural_loop(&self, head: usize, tail: usize) -> HashSet<usize> {
        let mut stack = vec![tail];
        let mut seen = HashSet::new();
        seen.insert(head);

        while let Some(node) = stack.pop() {
            if seen.insert(node)
                && let Some(preds) = self.predecessors.get(&node)
            {
                stack.extend(preds.iter().copied());
            }
        }

        seen.remove(&head);
        seen
    }

    /// Identifies the loop type, if there is one.
    fn identify_loop(
        &self,
        head: usize,
        tail: usize,
        body_blocks: &HashSet<usize>,
    ) -> Option<Loop> {
        if let Some(tail_exit) = self.extract_exit(&self.nodes[&tail]) {
            match tail_exit {
                BlockExit::FornLoop {
                    base, exit_block, ..
                } => {
                    let prep_id = self.predecessors[&head].iter().copied().find(|&p| {
                        if p == tail || body_blocks.contains(&p) {
                            return false;
                        }
                        if let Some(BlockExit::FornPrep { base: p_base, .. }) =
                            self.extract_exit(&self.nodes[&p])
                        {
                            return p_base == base;
                        }
                        false
                    });
                    if let Some(prep) = prep_id
                        && let Some(BlockExit::FornPrep {
                            var,
                            start,
                            end,
                            step,
                            ..
                        }) = self.extract_exit(&self.nodes[&prep])
                    {
                        return Some(Loop::NumericFor {
                            var: *var,
                            start: start.clone(),
                            end: end.clone(),
                            step: step.clone(),
                            prep_block: prep,
                            exit_block: self.region_for_block[exit_block],
                        });
                    }
                }
                BlockExit::ForgLoop {
                    base,
                    exit_block,
                    vars,
                    ..
                } => {
                    let prep_id = self.predecessors[&head].iter().copied().find(|&p| {
                        if p == tail || body_blocks.contains(&p) {
                            return false;
                        }
                        if let Some(BlockExit::ForgPrep { base: p_base, .. }) =
                            self.extract_exit(&self.nodes[&p])
                        {
                            return p_base == base;
                        }
                        false
                    });
                    if let Some(prep) = prep_id
                        && let Some(BlockExit::ForgPrep { exprs, .. }) =
                            self.extract_exit(&self.nodes[&prep])
                    {
                        return Some(Loop::GenericFor {
                            vars: vars.clone(),
                            exprs: exprs.clone(),
                            prep_block: prep,
                            exit_block: self.region_for_block[exit_block],
                        });
                    }
                }
                _ => {}
            }
        }

        // repeat..until: condition is evaluated at the tail.
        if tail != head
            && let Some((_, raw_then, raw_else)) = self.extract_cond_jump(&self.nodes[&tail])
        {
            let active_then = self.region_for_block[&raw_then];
            let active_else = self.region_for_block[&raw_else];
            if active_then == head || active_else == head {
                let exit_block = if active_then == head {
                    active_else // Branches to head on TRUE, meaning it repeats while true (until false)
                } else {
                    active_then
                };

                return Some(Loop::RepeatUntil {
                    exit_block: self.forward_jump_exit(exit_block, head),
                });
            }
        }

        // while: condition is evaluated at the head.
        if let Some((cond, raw_then, raw_else)) = self.extract_cond_jump(&self.nodes[&head]) {
            // One branch must go into the loop body, the other must exit.
            let active_then = self.region_for_block[&raw_then];
            let active_else = self.region_for_block[&raw_else];

            let then_in_body = body_blocks.contains(&active_then) || active_then == tail;
            let else_in_body = body_blocks.contains(&active_else) || active_else == tail;

            if then_in_body != else_in_body {
                let (exit_block, invert) = if then_in_body {
                    (active_else, false)
                } else {
                    (active_then, true)
                };

                let final_cond = if invert { invert_condition(cond) } else { cond };
                return Some(Loop::While {
                    cond: final_cond,
                    exit_block,
                });
            }
        }

        None
    }

    fn forward_jump_exit(&self, exit_block: usize, loop_head: usize) -> usize {
        let Some(exit_node) = self.nodes.get(&exit_block) else {
            return exit_block;
        };

        let Some(BlockExit::Jump(next_raw)) = self.extract_exit(exit_node) else {
            return exit_block;
        };

        let Some(&next_block) = self.region_for_block.get(next_raw) else {
            return exit_block;
        };

        if next_block == loop_head {
            exit_block
        } else {
            next_block
        }
    }

    fn collapse_loops(&mut self) -> bool {
        // Theory: In a simple program, the control flow always moves "forward". A loop exists when a node has a backedge,
        // ie. an edge from node 'Tail' to node 'Head' is a backedge if and only if 'Head' dominates 'Tail'. Because 'Head'
        // dominates 'Tail', it is physically impossible to reach 'Tail' without first passing through 'Head'.

        let mut changed = false;

        let mut work = self.post_order();
        work.reverse();

        while let Some(head) = work.pop() {
            if let Some(tail) = self.find_backedge(head) {
                let body_blocks_used = self.get_natural_loop(head, tail);

                // We can expect two types of a loop here:
                // 1. while: the backedge is an unconditional jump, while the head either jumps to the body or the loop exit
                // 2. repeat..until: the backedge is a conditional jump, the header can be any block
                if let Some(kind) = self.identify_loop(head, tail, &body_blocks_used) {
                    let body_blocks_used = self.get_loop_region(head, kind.exit_block());

                    let mut body_nodes: Vec<_> = self
                        .nodes
                        .extract_if(|id, _| body_blocks_used.contains(id) && *id != head)
                        .collect();

                    let po_rank: HashMap<_, _> = self
                        .post_order()
                        .into_iter()
                        .enumerate()
                        .map(|(i, node)| (node, i))
                        .collect();

                    body_nodes.sort_unstable_by_key(|(id, _)| std::cmp::Reverse(po_rank[id]));

                    let mut body_ast = CfgNode::merge(body_nodes.into_iter().map(|(_, b)| b));

                    // While loops jump to the head, repeat..until/for loops jump to the tail.
                    let (continue_tgt, continue_tgt_alt) = match &kind {
                        Loop::While { .. } => (head, Some(tail)),
                        _ => (tail, None),
                    };
                    body_ast.resolve_escapes(
                        continue_tgt,
                        continue_tgt_alt,
                        kind.exit_block(),
                        self.cfg,
                        &self.region_for_block,
                    );

                    let loop_id = self.next_id();
                    let head_node = self.nodes.remove(&head).unwrap();

                    let mut absorbed_blocks = HashSet::new();
                    let (region_entry, loop_node, exit_block) = match kind {
                        Loop::While { cond, exit_block } => {
                            let mut effective_exit = exit_block;
                            let mut break_payload = CfgNode::Break;

                            if let Some(exit_node) = self.nodes.get(&exit_block)
                                && let Some(BlockExit::Jump(next_raw)) =
                                    self.extract_exit(exit_node)
                                && let Some(&next_block) = self.region_for_block.get(next_raw)
                                && next_block != head
                            {
                                effective_exit = next_block;
                                absorbed_blocks.insert(exit_block);
                                if self.node_emits_statements(exit_node) {
                                    break_payload =
                                        CfgNode::merge([exit_node.clone(), CfgNode::Break]);
                                }
                            }

                            let must_guard = self.node_emits_statements(&head_node)
                                || !matches!(break_payload, CfgNode::Break);

                            let loop_node = if must_guard {
                                let mut parts = Vec::with_capacity(3);
                                if self.node_emits_statements(&head_node) {
                                    parts.push(head_node);
                                }

                                let break_guard = CfgNode::If {
                                    condition: invert_condition(cond),
                                    then_branch: Box::new(break_payload),
                                    else_branch: None,
                                };
                                parts.push(break_guard);
                                parts.push(body_ast);

                                CfgNode::While {
                                    condition: HilExpr::Bool(true),
                                    body: Box::new(CfgNode::merge(parts)),
                                }
                            } else {
                                CfgNode::While {
                                    condition: cond,
                                    body: Box::new(body_ast),
                                }
                            };

                            (head, loop_node, effective_exit)
                        }
                        Loop::RepeatUntil { exit_block } => (
                            head,
                            {
                                let mut body = self.fold_head_escape_guard(head_node, body_ast);
                                self.normalize_escape_guards(&mut body);

                                CfgNode::While {
                                    condition: HilExpr::Bool(true),
                                    body: Box::new(body),
                                }
                            },
                            exit_block,
                        ),
                        Loop::NumericFor {
                            var,
                            start,
                            end,
                            step,
                            prep_block,
                            exit_block,
                        } => {
                            let prep_node = self.nodes.remove(&prep_block).unwrap();
                            let mut for_body = self.fold_head_escape_guard(head_node, body_ast);
                            self.normalize_escape_guards(&mut for_body);
                            let for_node = CfgNode::NumericFor {
                                var,
                                start,
                                end,
                                step,
                                body: Box::new(for_body),
                            };
                            (
                                prep_block,
                                CfgNode::merge([prep_node, for_node]),
                                exit_block,
                            )
                        }
                        Loop::GenericFor {
                            vars,
                            exprs,
                            prep_block,
                            exit_block,
                        } => {
                            let prep_node = self.nodes.remove(&prep_block).unwrap();
                            let mut for_body = self.fold_head_escape_guard(head_node, body_ast);
                            self.normalize_escape_guards(&mut for_body);
                            let for_node = CfgNode::GenericFor {
                                vars,
                                exprs,
                                body: Box::new(for_body),
                            };
                            (
                                prep_block,
                                CfgNode::merge([prep_node, for_node]),
                                exit_block,
                            )
                        }
                    };

                    self.nodes.insert(loop_id, loop_node);
                    self.update_regionmap(
                        |val| {
                            val == region_entry
                                || val == head
                                || body_blocks_used.contains(&val)
                                || absorbed_blocks.contains(&val)
                        },
                        loop_id,
                    );

                    self.transfer_predecessors(region_entry, loop_id);
                    if let Some(preds) = self.predecessors.get_mut(&loop_id) {
                        preds.retain(|&p| {
                            !body_blocks_used.contains(&p)
                                && !absorbed_blocks.contains(&p)
                                && p != tail
                                && p != loop_id
                                && p != head
                        });
                    }

                    self.successors.insert(loop_id, vec![exit_block]);
                    if let Some(exit_preds) = self.predecessors.get_mut(&exit_block) {
                        exit_preds.retain(|&p| {
                            p != region_entry
                                && p != head
                                && p != tail
                                && !absorbed_blocks.contains(&p)
                                && !body_blocks_used.contains(&p)
                        });
                        exit_preds.push(loop_id);
                    }

                    for block in &body_blocks_used {
                        self.successors.remove(block);
                        self.predecessors.remove(block);
                    }
                    for block in &absorbed_blocks {
                        self.nodes.remove(block);
                        self.successors.remove(block);
                        self.predecessors.remove(block);
                    }
                    self.successors.remove(&head);
                    if region_entry != head {
                        self.successors.remove(&region_entry);
                    }

                    if region_entry != head {
                        self.successors.remove(&region_entry);
                    }
                    if region_entry == self.entry_node || head == self.entry_node {
                        self.entry_node = loop_id;
                    }
                    self.invalidate_doms();

                    work.push(loop_id);
                    changed = true;
                }
            }
        }

        changed
    }

    /// Returns the post-order traversal of the region nodes.
    fn post_order(&self) -> Vec<usize> {
        let mut order = Vec::new();
        let mut visited = HashSet::new();

        fn dfs(
            block: usize,
            successors: &HashMap<usize, Vec<usize>>,
            visited: &mut HashSet<usize>,
            order: &mut Vec<usize>,
        ) {
            visited.insert(block);

            let block_successors = successors
                .get(&block)
                .map_or(&[] as &[usize], |p| p.as_slice());

            for &succ in block_successors {
                if !visited.contains(&succ) {
                    dfs(succ, successors, visited, order);
                }
            }
            order.push(block);
        }

        dfs(self.entry_node, &self.successors, &mut visited, &mut order);

        order
    }

    fn structure(&mut self) {
        loop {
            if self.collapse_sequential() {
                eprintln!("Collapsed sequential");
                continue;
            }

            if self.collapse_conditional() {
                eprintln!("Collapsed conditional");
                continue;
            }

            if self.collapse_loops() {
                eprintln!("Collapsed loops");
                continue;
            }

            break;
        }
    }
}

/// A wrapper around `build_immediate_dominators` that handles sparse/non-continuous node IDs.
pub fn build_idoms_sparse(
    entry_node: usize,
    active_nodes: impl Iterator<Item = usize>,
    successors_map: &HashMap<usize, Vec<usize>>,
    predecessors_map: &HashMap<usize, Vec<usize>>,
) -> HashMap<usize, usize> {
    let mut sparse_to_dense = HashMap::new();
    let mut dense_to_sparse = Vec::new();

    for (dense, sparse) in active_nodes.enumerate() {
        sparse_to_dense.insert(sparse, dense);
        dense_to_sparse.push(sparse);
    }

    let num_nodes = dense_to_sparse.len();

    // Safety check: if the entry node was folded or deleted, we can't compute
    let Some(&dense_entry) = sparse_to_dense.get(&entry_node) else {
        return HashMap::new();
    };

    let mut dense_succs = vec![Vec::new(); num_nodes];
    let mut dense_preds = vec![Vec::new(); num_nodes];

    for &sparse in &dense_to_sparse {
        let dense = sparse_to_dense[&sparse];

        if let Some(succs) = successors_map.get(&sparse) {
            // Only include edges to nodes that still exist in the graph
            dense_succs[dense] = succs
                .iter()
                .filter_map(|s| sparse_to_dense.get(s).copied())
                .collect();
        }

        if let Some(preds) = predecessors_map.get(&sparse) {
            dense_preds[dense] = preds
                .iter()
                .filter_map(|p| sparse_to_dense.get(p).copied())
                .collect();
        }
    }

    let dense_doms = build_immediate_dominators(dense_entry, &dense_succs, &dense_preds);
    let mut sparse_doms = HashMap::new();
    for (dense, &sparse) in dense_to_sparse.iter().enumerate() {
        if let Some(dense_idom) = dense_doms[dense] {
            sparse_doms.insert(sparse, dense_to_sparse[dense_idom]);
        }
    }

    sparse_doms
}

fn flatten_regions(nodes: Vec<RegionNode>) -> Vec<RegionNode> {
    let mut out = Vec::new();

    for n in nodes {
        match n {
            RegionNode::Sequence { nodes: inner } => {
                out.extend(flatten_regions(inner));
            }
            other => out.push(other),
        }
    }

    out
}

pub fn structure(cfg: &ControlFlowGraph) -> (RegionNode, bool) {
    let mut fg = FoldableGraph::new(cfg);

    fg.structure();

    let reduced = fg.nodes.iter().len() == 1;

    let mut root = fg.nodes.remove(&fg.entry_node).unwrap();
    root.strip_virtual_exits();
    root.resolve_returns(cfg);
    (root.lower(cfg), reduced)
}
