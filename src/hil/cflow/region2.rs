use std::collections::{HashMap, HashSet};

use either::Either;
use smallvec::SmallVec;

use crate::hil::{
    cflow::{
        common::invert_condition,
        graph::{BlockExit, ControlFlowGraph, build_immediate_dominators},
    },
    ir::HilExpr,
    lifter::ssa::SymbolId,
};

struct WorkList<T> {
    items: Vec<T>,
    cursor: usize,
}

impl<T: Copy + Ord> WorkList<T> {
    fn from_keys<'a, K: Iterator<Item = &'a T>>(keys: K) -> Self
    where
        T: 'a,
    {
        let mut items: Vec<T> = keys.copied().collect();
        items.sort_unstable();
        Self { items, cursor: 0 }
    }

    fn next(&mut self) -> Option<T> {
        let item = self.items.get(self.cursor).copied();
        self.cursor += 1;
        item
    }

    fn push(&mut self, item: T) {
        self.items.push(item);
    }
}

#[derive(Debug)]
enum Loop {
    While { cond: HilExpr, exit_block: usize },
    RepeatUntil { cond: HilExpr, exit_block: usize },
}

/// One structured control-flow node in the intermediate region tree.
#[derive(Debug, Clone)]
pub enum RegionNode {
    /// A plain basic block payload that does not by itself decide control transfer.
    BasicBlock { block: usize },
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
    /// A structured repeat/until loop recovered from backedges.
    RepeatUntil {
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

impl RegionNode {
    /// Merges nodes into a `Sequence` node, flattening nested sequences.
    fn merge(nodes: impl IntoIterator<Item = RegionNode>) -> RegionNode {
        let seq_nodes = nodes
            .into_iter()
            .flat_map(|node| match node {
                RegionNode::Sequence { nodes } => Either::Left(nodes.into_iter()),
                other => Either::Right(std::iter::once(other)),
            })
            .collect();

        RegionNode::Sequence { nodes: seq_nodes }
    }
}

pub struct FoldableGraph<'a> {
    cfg: &'a ControlFlowGraph,
    nodes: HashMap<usize, RegionNode>,

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
            .map(|(i, _)| (i, RegionNode::BasicBlock { block: i }))
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

            nodes.insert(
                virtual_exit_id,
                RegionNode::BasicBlock { block: usize::MAX },
            );

            for node in terminal_nodes {
                successors.entry(node).or_default().push(virtual_exit_id);
                predecessors.entry(virtual_exit_id).or_default().push(node);
            }

            virtual_exit_id
        };

        FoldableGraph {
            cfg,
            nodes,
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

    /// Collapses sequentially executed blocks into a `BlockSequence` node.
    fn collapse_sequential(&mut self) -> bool {
        // Theory: If a basic block A has only one successor B, and B has only one predecessor A,
        // then A and B are sequential and can be collapsed into a `BlockSequence` node.

        let mut changed = false;

        let mut work = WorkList::from_keys(self.nodes.keys());
        while let Some(curr) = work.next() {
            if !self.nodes.contains_key(&curr) {
                continue;
            }

            if let Some([next]) = self.exact_successors(curr)
                && let Some([prev]) = self.exact_predecessors(next)
                && prev == curr
                && curr != next
            {
                let seq_id = self.next_id();

                let node_a = self.nodes.remove(&curr).unwrap();
                let node_b = self.nodes.remove(&next).unwrap();

                self.nodes
                    .insert(seq_id, RegionNode::merge([node_a, node_b]));

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

    // Returns (Condition, ThenTarget, ElseTarget)
    fn extract_cond_jump(&self, node: &RegionNode) -> Option<(HilExpr, usize, usize)> {
        match node {
            RegionNode::BasicBlock { block } => {
                if let BlockExit::CondJump {
                    cond,
                    then_block,
                    else_block,
                } = &self.cfg.blocks[*block].exit
                {
                    Some((cond.clone(), *then_block, *else_block))
                } else {
                    None
                }
            }
            RegionNode::Sequence { nodes } => {
                nodes.last().and_then(|last| self.extract_cond_jump(last))
            }
            _ => None,
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

        let mut changed = false;

        let mut work = WorkList::from_keys(self.nodes.keys());
        while let Some(head) = work.next() {
            if !self.nodes.contains_key(&head) {
                continue;
            }

            // if
            if let Some([left, right]) = self.exact_successors(head) {
                let Some(tail) = self.get_or_calc_postidoms().get(&head).copied() else {
                    continue;
                };

                let Some((mut cond, _, _)) = self.extract_cond_jump(&self.nodes[&head]) else {
                    continue;
                };

                // A block is a strict body if it only comes from Head, and only goes to Tail.
                let is_strict_body = |node: usize, tail: usize| {
                    self.exact_predecessors(node).is_some_and(|p| p == [head])
                        && self.exact_successors(node).is_some_and(|s| s == [tail])
                };

                let mut then_node_id = None;
                let mut else_node_id = None;
                let mut is_valid = false;

                if left == tail && is_strict_body(right, tail) {
                    // If-Then (The body is on the FALSE path)
                    then_node_id = Some(right);
                    cond = invert_condition(cond);
                    is_valid = true;
                } else if right == tail && is_strict_body(left, tail) {
                    // If-Then (The body is on the TRUE path)
                    then_node_id = Some(left);
                    is_valid = true;
                } else if is_strict_body(left, tail) && is_strict_body(right, tail) {
                    // If-Then-Else
                    then_node_id = Some(left);
                    else_node_id = Some(right);
                    is_valid = true;
                }

                if !is_valid {
                    continue;
                }
                let then_node_id = then_node_id.unwrap(); // always exists at this point

                let new_id = self.next_id();
                let header_node = self.nodes.remove(&head).unwrap();
                let then_ast = Box::new(self.nodes.remove(&then_node_id).unwrap());
                let else_ast = else_node_id.map(|id| Box::new(self.nodes.remove(&id).unwrap()));
                self.nodes.insert(
                    new_id,
                    RegionNode::merge([
                        header_node,
                        RegionNode::If {
                            condition: cond,
                            then_branch: then_ast,
                            else_branch: else_ast,
                        },
                    ]),
                );
                self.transfer_predecessors(head, new_id);

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

                work.push(new_id);
                changed = true;
            }
        }

        changed
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

    /// Collects backward-reachable blocks from `start` without stepping onto `target`.
    #[must_use]
    fn backward_reachable_without_target(&mut self, start: usize, target: usize) -> HashSet<usize> {
        let mut stack = vec![start];
        let mut seen = HashSet::new();

        while let Some(block) = stack.pop() {
            if block == target || !seen.insert(block) {
                continue;
            }

            // This below is some of the worst fucking code I have ever written, handling
            // borrow checker in the most retarded way possible.
            let preds_len = match self.predecessors.get(&block) {
                Some(p) => p.len(),
                None => continue,
            };

            for i in 0..preds_len {
                let pred = self.predecessors[&block][i];
                if pred != target && self.dominates(target, pred) {
                    stack.push(pred);
                }
            }
        }

        seen
    }

    /// Identifies the loop type, if there is one.
    fn identify_loop(
        &self,
        head: usize,
        tail: usize,
        body_blocks: &HashSet<usize>,
    ) -> Option<Loop> {
        // repeat..until: condition is evaluated at the tail.
        if let Some((cond, then_tgt, else_tgt)) = self.extract_cond_jump(&self.nodes[&tail])
            && (then_tgt == head || else_tgt == head)
        {
            let (exit_block, invert) = if then_tgt == head {
                (else_tgt, true) // Branches to head on TRUE, meaning it repeats while true (until false)
            } else {
                (then_tgt, false)
            };

            let final_cond = if invert { invert_condition(cond) } else { cond };
            return Some(Loop::RepeatUntil {
                cond: final_cond,
                exit_block,
            });
        }

        // while: condition is evaluated at the head.
        if let Some((cond, then_tgt, else_tgt)) = self.extract_cond_jump(&self.nodes[&head]) {
            // One branch must go into the loop body, the other must exit.
            let then_in_body = body_blocks.contains(&then_tgt) || then_tgt == tail;
            let else_in_body = body_blocks.contains(&else_tgt) || else_tgt == tail;

            if then_in_body != else_in_body {
                let (exit_block, invert) = if then_in_body {
                    (else_tgt, false)
                } else {
                    (then_tgt, true)
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

    fn collapse_loops(&mut self) -> bool {
        // Theory: In a simple program, the control flow always moves "forward". A loop exists when a node has a backedge,
        // ie. an edge from node 'Tail' to node 'Head' is a backedge if and only if 'Head' dominates 'Tail'. Because 'Head'
        // dominates 'Tail', it is physically impossible to reach 'Tail' without first passing through 'Head'.

        let mut changed = false;

        let mut work = WorkList::from_keys(self.nodes.keys());
        while let Some(head) = work.next() {
            if let Some(tail) = self.find_backedge(head) {
                let body_blocks_used = self.backward_reachable_without_target(tail, head);

                // We can expect two types of a loop here:
                // 1. while: the backedge is an unconditional jump, while the head either jumps to the body or the loop exit
                // 2. repeat..until: the backedge is a conditional jump, the header can be any block
                if let Some(kind) = self.identify_loop(head, tail, &body_blocks_used) {
                    eprintln!("kind: {:#?}", kind);
                    eprintln!("body: {:?}", body_blocks_used);

                    // this is quite ugly
                    let mut body_nodes: Vec<_> = self
                        .nodes
                        .extract_if(|id, _| body_blocks_used.contains(id))
                        .collect();
                    body_nodes.sort_unstable_by_key(|(id, _)| *id);
                    let body_ast = RegionNode::merge(body_nodes.into_iter().map(|(_, b)| b));

                    let loop_id = self.next_id();
                    let head_node = self.nodes.remove(&head).unwrap();

                    let (loop_node, exit_block) = match kind {
                        Loop::While {
                            cond, exit_block, ..
                        } => (
                            RegionNode::While {
                                condition: cond,
                                body: Box::new(body_ast),
                            },
                            exit_block,
                        ),
                        Loop::RepeatUntil { cond, exit_block } => (
                            RegionNode::RepeatUntil {
                                condition: cond,
                                body: Box::new(RegionNode::merge([head_node, body_ast])),
                            },
                            exit_block,
                        ),
                    };

                    self.nodes.insert(loop_id, loop_node);
                    self.transfer_predecessors(head, loop_id);

                    self.successors.insert(loop_id, vec![exit_block]);
                    if let Some(exit_preds) = self.predecessors.get_mut(&exit_block) {
                        exit_preds
                            .retain(|&p| p != head && p != tail && !body_blocks_used.contains(&p));
                        exit_preds.push(loop_id);
                    }

                    for block in &body_blocks_used {
                        self.successors.remove(block);
                        self.predecessors.remove(block);
                    }

                    if head == self.entry_node {
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

    fn structure(&mut self) {
        loop {
            if self.collapse_loops() {
                eprintln!("Collapsed loops");
                continue;
            }

            if self.collapse_sequential() {
                eprintln!("Collapsed sequential");
                continue;
            }

            if self.collapse_conditional() {
                eprintln!("Collapsed conditional");
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

pub fn structure(cfg: &ControlFlowGraph) -> HashMap<usize, RegionNode> {
    let mut fg = FoldableGraph::new(cfg);

    fg.structure();

    fg.nodes
}
