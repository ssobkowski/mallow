use std::collections::{HashMap, HashSet};

use either::Either;
use smallvec::SmallVec;

use crate::{
    ast::BinOp,
    hil::{
        cflow::{
            cfg::{BlockExit, ControlFlowGraph},
            graph::{DominatorTree, GraphView, Reversed, SeseGraphView},
        },
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
    },
};

#[derive(Debug)]
enum Loop {
    While {
        cond: HilExpr,
        exit_block: Option<usize>,
        guard: Option<GuardTree>,
        absorbed: Vec<usize>,
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

#[derive(Debug, Clone)]
enum GuardTree {
    Body,
    Exit,
    Branch {
        condition: HilExpr,
        then_branch: Box<GuardTree>,
        else_branch: Box<GuardTree>,
    },
}

#[derive(Debug, Clone, PartialEq)]
enum BoolExpr {
    True,
    False,
    Atom(HilExpr),
    Not(Box<BoolExpr>),
    And(Box<BoolExpr>, Box<BoolExpr>),
    Or(Box<BoolExpr>, Box<BoolExpr>),
}

impl BoolExpr {
    fn atom(expr: HilExpr) -> Self {
        match expr {
            HilExpr::Bool(true) => Self::True,
            HilExpr::Bool(false) => Self::False,
            other => Self::Atom(other),
        }
    }

    fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Atom(expr) => Self::atom(expr.invert()),
            Self::Not(inner) => *inner,
            other => Self::Not(Box::new(other)),
        }
    }

    fn and(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, rhs) => rhs,
            (lhs, Self::True) => lhs,
            (lhs, rhs) => Self::And(Box::new(lhs), Box::new(rhs)),
        }
    }

    fn or(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, rhs) => rhs,
            (lhs, Self::False) => lhs,
            (lhs, Self::And(and_lhs, and_rhs)) if lhs == and_lhs.as_ref().clone().not() => {
                lhs.or(*and_rhs)
            }
            (Self::And(and_lhs, and_rhs), rhs) if rhs == and_lhs.as_ref().clone().not() => {
                rhs.or(*and_rhs)
            }
            (lhs, rhs) => Self::Or(Box::new(lhs), Box::new(rhs)),
        }
    }

    fn into_hil(self) -> HilExpr {
        match self {
            Self::True => HilExpr::Bool(true),
            Self::False => HilExpr::Bool(false),
            Self::Atom(expr) => expr,
            Self::Not(expr) => expr.into_hil().invert(),
            Self::And(lhs, rhs) => HilExpr::Binary {
                lhs: Box::new(lhs.into_hil()),
                op: BinOp::And,
                rhs: Box::new(rhs.into_hil()),
            },
            Self::Or(lhs, rhs) => HilExpr::Binary {
                lhs: Box::new(lhs.into_hil()),
                op: BinOp::Or,
                rhs: Box::new(rhs.into_hil()),
            },
        }
    }
}

impl From<GuardTree> for BoolExpr {
    fn from(guard: GuardTree) -> Self {
        match guard {
            GuardTree::Body => BoolExpr::True,
            GuardTree::Exit => BoolExpr::False,
            GuardTree::Branch {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond_expr = BoolExpr::atom(condition);
                let then_condition = BoolExpr::from(*then_branch);
                let else_condition = BoolExpr::from(*else_branch);

                cond_expr
                    .clone()
                    .and(then_condition)
                    .or(cond_expr.not().and(else_condition))
            }
        }
    }
}

#[derive(Debug)]
struct GuardBuild {
    tree: GuardTree,
    exit_block: Option<usize>,
    has_body: bool,
    absorbed: HashSet<usize>,
}

impl GuardBuild {
    fn body() -> Self {
        Self {
            tree: GuardTree::Body,
            exit_block: None,
            has_body: true,
            absorbed: HashSet::new(),
        }
    }

    fn exit(exit_block: usize) -> Self {
        Self {
            tree: GuardTree::Exit,
            exit_block: Some(exit_block),
            has_body: false,
            absorbed: HashSet::new(),
        }
    }
}

impl Loop {
    fn exit_block(&self) -> Option<usize> {
        match self {
            Loop::While { exit_block, .. } => *exit_block,
            Loop::RepeatUntil { exit_block, .. }
            | Loop::NumericFor { exit_block, .. }
            | Loop::GenericFor { exit_block, .. } => Some(*exit_block),
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

impl CfgNode {
    pub const fn is_empty(&self) -> bool {
        matches!(self, CfgNode::Sequence { nodes } if nodes.is_empty())
    }
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
        exprs: SmallVec<[HilExpr; 3]>,
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
        exit: Option<usize>,
        cfg: &ControlFlowGraph,
        region_map: &HashMap<usize, usize>,
        require_empty_continue_target: bool,
    ) {
        let is_continue_target = |raw_target: usize, active_target: usize| {
            if active_target == continue_target {
                !require_empty_continue_target || cfg.blocks[raw_target].stmts.is_empty()
            } else {
                continue_target_alt.is_some_and(|target| raw_target == target)
            }
        };

        match self {
            CfgNode::Sequence { nodes } => nodes.iter_mut().for_each(|n| {
                n.resolve_escapes(
                    continue_target,
                    continue_target_alt,
                    exit,
                    cfg,
                    region_map,
                    require_empty_continue_target,
                )
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
                    require_empty_continue_target,
                );
                if let Some(e) = else_branch {
                    e.resolve_escapes(
                        continue_target,
                        continue_target_alt,
                        exit,
                        cfg,
                        region_map,
                        require_empty_continue_target,
                    );
                }
            }
            CfgNode::BasicBlock { block } => {
                let exit_node = &cfg.blocks[*block].exit;

                let replacement = match exit_node {
                    BlockExit::Jump(raw_target) => {
                        let active = region_map[raw_target];
                        if is_continue_target(*raw_target, active) {
                            Some(CfgNode::Continue)
                        } else if exit.is_some_and(|exit| active == exit) {
                            Some(CfgNode::Break)
                        } else {
                            None
                        }
                    }
                    BlockExit::Fallthrough(raw_target) => {
                        let active = region_map[raw_target];
                        if exit.is_some_and(|exit| active == exit) {
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

                        let then_terminal = if is_continue_target(*then_block, active_then) {
                            Some(CfgNode::Continue)
                        } else if exit.is_some_and(|exit| active_then == exit) {
                            Some(CfgNode::Break)
                        } else {
                            None
                        };

                        let else_terminal = if is_continue_target(*else_block, active_else) {
                            Some(CfgNode::Continue)
                        } else if exit.is_some_and(|exit| active_else == exit) {
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
                                condition: cond.clone().invert(),
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

    /// Returns the first raw basic block contained in this structured node.
    ///
    /// Post-structuring cleanup uses this to relate a structured loop body back to
    /// the raw CFG edge that re-enters it.
    fn first_block(&self) -> Option<usize> {
        match self {
            CfgNode::BasicBlock { block } => Some(*block),
            CfgNode::Sequence { nodes } => nodes.first().and_then(|n| n.first_block()),
            _ => None,
        }
    }

    /// Returns whether this node starts with the given raw CFG block.
    ///
    /// Sequence nodes recurse into their first child so merged wrappers do not
    /// hide the real leading block.
    fn starts_with_block(&self, block: usize) -> bool {
        self.first_block().is_some_and(|id| id == block)
    }

    /// Returns whether this node ends in an explicit terminal statement.
    fn ends_with_escape(&self) -> bool {
        match self {
            CfgNode::Continue | CfgNode::Break | CfgNode::Return { .. } => true,
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
                    .map(|stmt| stmt.node)
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
                exprs: exprs.into(),
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

    idoms: Option<DominatorTree>,
    postidoms: Option<DominatorTree>,

    id_counter: usize,
}

impl GraphView for FoldableGraph<'_> {
    fn entry(&self) -> usize {
        self.entry_node
    }

    fn successors(&self, node: usize) -> &[usize] {
        self.successors.get(&node).map_or(&[], Vec::as_slice)
    }

    fn predecessors(&self, node: usize) -> &[usize] {
        self.predecessors.get(&node).map_or(&[], Vec::as_slice)
    }

    fn contains_node(&self, node: usize) -> bool {
        self.nodes.contains_key(&node)
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.nodes.keys().copied()
    }
}

impl SeseGraphView for FoldableGraph<'_> {
    fn exit(&self) -> usize {
        self.exit_node
    }
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
    fn get_or_calc_idoms(&mut self) -> &DominatorTree {
        if self.idoms.is_none() {
            self.idoms = Some(self.build_idoms());
        }

        self.idoms
            .as_ref()
            .expect("immediate dominators should be cached")
    }

    /// Lazily recalculates the post-dominators for each node in the graph.
    fn get_or_calc_postidoms(&mut self) -> &DominatorTree {
        if self.postidoms.is_none() {
            self.postidoms = Some(Reversed::new(&*self).build_idoms());
        }

        self.postidoms
            .as_ref()
            .expect("post-dominators should be cached")
    }

    /// Invalidates the cached immediate dominators and post-dominators,
    /// forcing a recalculation on the next `get_or_calc*` call.
    fn invalidate_doms(&mut self) {
        self.idoms = None;
        self.postidoms = None;
    }

    /// Removes stale adjacency entries after region nodes have absorbed raw CFG nodes.
    ///
    /// Folding keeps the original block IDs inside `CfgNode::BasicBlock` leaves, but
    /// the folded-away graph node IDs must disappear from `successors` and
    /// `predecessors`. If they remain, later SESE checks see phantom edges and skip
    /// otherwise valid conditional or loop folds.
    fn prune_stale_edges(&mut self) {
        let live: HashSet<_> = self.nodes.keys().copied().collect();

        self.successors.retain(|node, _| live.contains(node));
        for succs in self.successors.values_mut() {
            let mut seen = HashSet::new();
            succs.retain(|succ| live.contains(succ));
            succs.retain(|succ| seen.insert(*succ));
        }

        self.predecessors.retain(|node, _| live.contains(node));
        for preds in self.predecessors.values_mut() {
            let mut seen = HashSet::new();
            preds.retain(|pred| live.contains(pred));
            preds.retain(|pred| seen.insert(*pred));
        }
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

    fn refresh_entry_node(&mut self) {
        if self.nodes.contains_key(&self.entry_node) {
            return;
        }

        if let Some(&entry_node) = self.region_for_block.get(&self.cfg.entry_block)
            && self.nodes.contains_key(&entry_node)
        {
            self.entry_node = entry_node;
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

    fn node_ends_with_terminal(&self, node: &CfgNode) -> bool {
        match node {
            CfgNode::BasicBlock { block } => {
                matches!(self.cfg.blocks[*block].exit, BlockExit::Return(_))
            }
            CfgNode::Sequence { nodes } => nodes
                .last()
                .is_some_and(|node| self.node_ends_with_terminal(node)),
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.node_ends_with_terminal(then_branch)
                    && else_branch
                        .as_ref()
                        .is_some_and(|branch| self.node_ends_with_terminal(branch))
            }
            _ => node.ends_with_escape(),
        }
    }

    /// Returns the normalized `(start, end, step)` shape for a range that contains
    /// exactly one structured numeric `for` loop.
    ///
    /// Flattened loop regions often look like:
    ///
    /// ```text
    /// BasicBlock(assign loop bounds)
    /// NumericFor(start = bound_symbol, end = bound_symbol, step = bound_symbol)
    /// ```
    ///
    /// This helper treats those simple binding blocks as part of the loop range and
    /// resolves the loop bounds through them, so two adjacent alternatives can be
    /// compared by value rather than by temporary SSA symbol IDs.
    fn numeric_for_range_shape(
        &self,
        nodes: &[CfgNode],
        start: usize,
        end: usize,
    ) -> Option<(HilExpr, HilExpr, HilExpr)> {
        let mut bindings = HashMap::new();
        for node in &nodes[start..end] {
            self.collect_simple_bindings(node, &mut bindings);
        }

        // There should be one real loop-emitting node in the range. Binding-only
        // blocks are allowed because FORNPREP setup can remain as a sibling of the
        // recovered `NumericFor` node until lowering.
        let mut shape = None;

        for node in &nodes[start..end] {
            if let Some((start, end, step)) = self.node_numeric_for_shape(node) {
                let normalized = (
                    Self::resolve_simple_binding(start, &bindings),
                    Self::resolve_simple_binding(end, &bindings),
                    Self::resolve_simple_binding(step, &bindings),
                );

                if shape.replace(normalized).is_some() {
                    return None;
                }
            } else if self.node_is_simple_binding_block(node) || !self.node_emits_statements(node) {
                continue;
            } else {
                return None;
            }
        }

        shape
    }

    /// Collects single-symbol assignments that can be used to normalize loop bounds.
    ///
    /// The bindings are intentionally shallow and local to the candidate branch
    /// range. They are used only for shape comparison, not for rewriting the IR.
    fn collect_simple_bindings(&self, node: &CfgNode, bindings: &mut HashMap<SymbolId, HilExpr>) {
        match node {
            CfgNode::BasicBlock { block } => {
                for stmt in &self.cfg.blocks[*block].stmts {
                    if let HilStmt::Assign {
                        left: HilExpr::Symbol(symbol),
                        value,
                    } = &stmt.node
                    {
                        bindings.insert(*symbol, value.clone());
                    }
                }
            }
            CfgNode::Sequence { nodes } => {
                for node in nodes {
                    self.collect_simple_bindings(node, bindings);
                }
            }
            _ => {}
        }
    }

    /// Returns true when a node only defines temporary values.
    ///
    /// Such blocks are safe to ignore while looking for the numeric-for shape,
    /// because their statements are loop setup that will still be emitted wherever
    /// the containing branch is moved.
    fn node_is_simple_binding_block(&self, node: &CfgNode) -> bool {
        match node {
            CfgNode::BasicBlock { block } => self.cfg.blocks[*block].stmts.iter().all(|stmt| {
                matches!(
                    &stmt.node,
                    HilStmt::Assign {
                        left: HilExpr::Symbol(_),
                        ..
                    } | HilStmt::Phi(_)
                )
            }),
            CfgNode::Sequence { nodes } => nodes
                .iter()
                .all(|node| self.node_is_simple_binding_block(node)),
            _ => false,
        }
    }

    /// Replaces a symbol expression with a simple binding collected from the same range.
    fn resolve_simple_binding(expr: HilExpr, bindings: &HashMap<SymbolId, HilExpr>) -> HilExpr {
        match expr {
            HilExpr::Symbol(symbol) => bindings
                .get(&symbol)
                .cloned()
                .unwrap_or(HilExpr::Symbol(symbol)),
            other => other,
        }
    }

    /// Extracts the raw numeric-for bounds from a single structured loop node.
    fn node_numeric_for_shape(&self, node: &CfgNode) -> Option<(HilExpr, HilExpr, HilExpr)> {
        match node {
            CfgNode::NumericFor {
                start, end, step, ..
            } => Some((start.clone(), end.clone(), step.clone())),
            _ => None,
        }
    }

    /// Extracts a normalized numeric-for shape from a branch node.
    ///
    /// Used by the cleanup pass that repairs one-armed `if` nodes followed by the
    /// matching alternative loop.
    fn branch_numeric_for_shape(&self, node: &CfgNode) -> Option<(HilExpr, HilExpr, HilExpr)> {
        match node {
            CfgNode::Sequence { nodes } => self.numeric_for_range_shape(nodes, 0, nodes.len()),
            other => self.node_numeric_for_shape(other),
        }
    }

    /// Checks whether two flattened branch ranges contain matching numeric loops.
    ///
    /// The comparison is deliberately narrow: both ranges must reduce to exactly one
    /// numeric-for shape after ignoring simple loop-setup bindings. This prevents
    /// broad if/else reconstruction in hash code where adjacent numeric loops may be
    /// sequential work rather than alternatives.
    fn ranges_are_matching_numeric_fors(
        &self,
        nodes: &[CfgNode],
        then_idx: usize,
        then_end: usize,
        else_idx: usize,
        else_end: usize,
    ) -> bool {
        let Some(then_shape) = self.numeric_for_range_shape(nodes, then_idx, then_end) else {
            return false;
        };
        self.numeric_for_range_shape(nodes, else_idx, else_end)
            .is_some_and(|else_shape| then_shape == else_shape)
    }

    /// Restructures a loop header's conditional branch inside a recovered loop body.
    ///
    /// Numeric and generic loop recovery can leave the header block and the two raw
    /// conditional targets as siblings in the loop body. This pass recognizes those
    /// target siblings and rebuilds the source-level `if`, either as an escape guard
    /// (`if cond then break end`) or as a normal `if/else`.
    fn fold_head_escape_guard(&self, head_node: CfgNode, body_ast: CfgNode) -> CfgNode {
        let Some((mut cond, then_block, else_block)) = self.extract_cond_jump(&head_node) else {
            return CfgNode::merge([head_node, body_ast]);
        };

        let CfgNode::Sequence { mut nodes } = body_ast else {
            return CfgNode::merge([head_node, body_ast]);
        };

        // Locate the current structured nodes that start with each raw conditional
        // target. After earlier folds these are usually not bare blocks anymore:
        // they can be sequences such as `prep block + NumericFor`.
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

        // The simplest loop-header condition is a guard where one or both branches
        // exit the current loop. Pull those targets next to the header so lowering
        // emits a clear guard instead of leaving the raw jump shape in the sequence.
        let then_escape = self.node_ends_with_terminal(&nodes[then_idx]);
        let else_escape = self.node_ends_with_terminal(&nodes[else_idx]);

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
                cond = cond.invert();
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
        // Preserve the older single-node fold for ordinary branch shapes. The wider
        // segment logic below is only for flattened loop regions where a branch is
        // represented by multiple adjacent siblings.
        let has_flattened_loop_region = nodes.iter().any(|node| {
            matches!(
                node,
                CfgNode::NumericFor { .. } | CfgNode::GenericFor { .. }
            )
        });

        if !has_flattened_loop_region {
            if let Some((then_branch, fallback_node, remaining)) =
                self.build_shared_fallback_chain(&nodes, then_block, else_block)
            {
                let mut folded = Vec::with_capacity(remaining.len() + 3);
                folded.push(head_node);
                folded.push(CfgNode::If {
                    condition: cond,
                    then_branch: Box::new(then_branch),
                    else_branch: None,
                });
                folded.push(fallback_node);
                folded.extend(remaining);

                return CfgNode::Sequence { nodes: folded };
            }

            if let Some((else_branch, fallback_node, remaining)) =
                self.build_shared_fallback_chain(&nodes, else_block, then_block)
            {
                let mut folded = Vec::with_capacity(remaining.len() + 3);
                folded.push(head_node);
                folded.push(CfgNode::If {
                    condition: cond.invert(),
                    then_branch: Box::new(else_branch),
                    else_branch: None,
                });
                folded.push(fallback_node);
                folded.extend(remaining);

                return CfgNode::Sequence { nodes: folded };
            }

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

            return CfgNode::Sequence {
                nodes: vec![
                    head_node,
                    CfgNode::If {
                        condition: cond,
                        then_branch: Box::new(then_branch),
                        else_branch: Some(Box::new(else_branch)),
                    },
                ],
            };
        }

        // For flattened loop branches, include the prep block plus the immediately
        // following structured loop. When the opposite conditional target appears
        // later, a one-armed branch may also include the intervening continuation
        // nodes; this is the shape produced by some hash finalization loops.
        let branch_end = |start: usize, other_start: usize| {
            let mut end = start + 1;
            let mut saw_loop = false;
            if matches!(
                nodes.get(end),
                Some(CfgNode::NumericFor { .. } | CfgNode::GenericFor { .. })
            ) {
                end += 1;
                saw_loop = true;
            }

            if saw_loop && start < other_start {
                end = other_start;
            }

            end
        };

        let then_end = branch_end(then_idx, else_idx);
        let else_end = branch_end(else_idx, then_idx);

        let then_touches_else = then_end == else_idx && then_end > then_idx + 1;
        let else_touches_then = else_end == then_idx && else_end > else_idx + 1;
        if then_touches_else || else_touches_then {
            // Adjacent branch ranges can be either real alternatives or a one-armed
            // guard followed by continuation. Only rebuild an `if/else` here when
            // both sides are matching numeric-for ranges; otherwise keep the safer
            // one-armed interpretation.
            if then_touches_else
                && else_end > else_idx + 1
                && self.ranges_are_matching_numeric_fors(
                    &nodes, then_idx, then_end, else_idx, else_end,
                )
            {
                let mut then_nodes = Vec::new();
                let mut else_nodes = Vec::new();
                let mut remaining = Vec::with_capacity(nodes.len());
                for (idx, node) in nodes.into_iter().enumerate() {
                    if (then_idx..then_end).contains(&idx) {
                        then_nodes.push(node);
                    } else if (else_idx..else_end).contains(&idx) {
                        else_nodes.push(node);
                    } else {
                        remaining.push(node);
                    }
                }

                let mut folded = Vec::with_capacity(remaining.len() + 2);
                folded.push(head_node);
                folded.push(CfgNode::If {
                    condition: cond,
                    then_branch: Box::new(CfgNode::Sequence { nodes: then_nodes }),
                    else_branch: Some(Box::new(CfgNode::Sequence { nodes: else_nodes })),
                });
                folded.extend(remaining);

                return CfgNode::Sequence { nodes: folded };
            }

            if else_touches_then
                && then_end > then_idx + 1
                && self.ranges_are_matching_numeric_fors(
                    &nodes, then_idx, then_end, else_idx, else_end,
                )
            {
                let mut then_nodes = Vec::new();
                let mut else_nodes = Vec::new();
                let mut remaining = Vec::with_capacity(nodes.len());
                for (idx, node) in nodes.into_iter().enumerate() {
                    if (then_idx..then_end).contains(&idx) {
                        then_nodes.push(node);
                    } else if (else_idx..else_end).contains(&idx) {
                        else_nodes.push(node);
                    } else {
                        remaining.push(node);
                    }
                }

                let mut folded = Vec::with_capacity(remaining.len() + 2);
                folded.push(head_node);
                folded.push(CfgNode::If {
                    condition: cond,
                    then_branch: Box::new(CfgNode::Sequence { nodes: then_nodes }),
                    else_branch: Some(Box::new(CfgNode::Sequence { nodes: else_nodes })),
                });
                folded.extend(remaining);

                return CfgNode::Sequence { nodes: folded };
            }

            // If the adjacent ranges do not prove to be matching alternatives, fold
            // the range that touches the other target as a guard and leave the rest
            // of the sequence in place. This avoids swallowing sequential work.
            let (branch_idx, branch_end, invert) = if then_end == else_idx {
                (then_idx, then_end, false)
            } else {
                (else_idx, else_end, true)
            };

            if invert {
                cond = cond.invert();
            }

            let mut branch_nodes = Vec::new();
            let mut remaining = Vec::with_capacity(nodes.len());
            for (idx, node) in nodes.into_iter().enumerate() {
                if (branch_idx..branch_end).contains(&idx) {
                    branch_nodes.push(node);
                } else {
                    remaining.push(node);
                }
            }

            let mut folded = Vec::with_capacity(remaining.len() + 2);
            folded.push(head_node);
            folded.push(CfgNode::If {
                condition: cond,
                then_branch: Box::new(CfgNode::Sequence {
                    nodes: branch_nodes,
                }),
                else_branch: None,
            });
            folded.extend(remaining);

            return CfgNode::Sequence { nodes: folded };
        }

        let ranges_overlap = then_idx < else_end && else_idx < then_end;
        if ranges_overlap || then_idx == then_end || else_idx == else_end {
            return CfgNode::merge([head_node, CfgNode::Sequence { nodes }]);
        }

        // Non-adjacent flattened branches can be moved into a regular if/else while
        // preserving all unrelated nodes after the conditional.
        let mut then_node_val = None;
        let mut else_node_val = None;

        let mut remaining = Vec::with_capacity(nodes.len());
        for (idx, node) in nodes.into_iter().enumerate() {
            if (then_idx..then_end).contains(&idx) {
                then_node_val.get_or_insert_with(|| CfgNode::Sequence { nodes: Vec::new() });
                if let Some(CfgNode::Sequence { nodes }) = &mut then_node_val {
                    nodes.push(node);
                }
            } else if (else_idx..else_end).contains(&idx) {
                else_node_val.get_or_insert_with(|| CfgNode::Sequence { nodes: Vec::new() });
                if let Some(CfgNode::Sequence { nodes }) = &mut else_node_val {
                    nodes.push(node);
                }
            } else {
                remaining.push(node);
            }
        }

        let mut folded = Vec::with_capacity(remaining.len() + 2);
        folded.push(head_node);
        folded.push(CfgNode::If {
            condition: cond,
            then_branch: Box::new(then_node_val.unwrap()),
            else_branch: Some(Box::new(else_node_val.unwrap())),
        });
        folded.extend(remaining);

        CfgNode::Sequence { nodes: folded }
    }

    fn build_shared_fallback_chain(
        &self,
        nodes: &[CfgNode],
        start_block: usize,
        fallback_block: usize,
    ) -> Option<(CfgNode, CfgNode, Vec<CfgNode>)> {
        let mut guards = Vec::new();
        let mut used_blocks = HashSet::new();
        let mut current = start_block;

        loop {
            if !used_blocks.insert(current) {
                return None;
            }

            let current_node = nodes
                .iter()
                .find(|node| node.starts_with_block(current))?
                .clone();
            let BlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } = &self.cfg.blocks[current].exit
            else {
                let success_node = current_node;
                if !self.node_ends_with_terminal(&success_node) || guards.is_empty() {
                    return None;
                }

                let fallback_node = nodes
                    .iter()
                    .find(|node| node.starts_with_block(fallback_block))?
                    .clone();
                used_blocks.insert(fallback_block);

                let mut branch = success_node;
                for (guard_node, condition) in guards.into_iter().rev() {
                    branch = CfgNode::merge([
                        guard_node,
                        CfgNode::If {
                            condition,
                            then_branch: Box::new(branch),
                            else_branch: None,
                        },
                    ]);
                }

                let remaining = nodes
                    .iter()
                    .filter(|node| {
                        node.first_block()
                            .is_none_or(|block| !used_blocks.contains(&block))
                    })
                    .cloned()
                    .collect();

                return Some((branch, fallback_node, remaining));
            };

            if *else_block == fallback_block {
                guards.push((current_node, cond.clone()));
                current = *then_block;
            } else if *then_block == fallback_block {
                guards.push((current_node, cond.clone().invert()));
                current = *else_block;
            } else {
                return None;
            }
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
                && self.node_ends_with_terminal(&nodes[escape_idx])
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
                && self.node_ends_with_terminal(&nodes[escape_idx])
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
                    condition: cond.invert(),
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

            let then_escape = self.node_ends_with_terminal(&nodes[then_idx]);
            let else_escape = self.node_ends_with_terminal(&nodes[else_idx]);
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

    /// Recursively pulls loop-reentering suffixes back into their infinite loop.
    ///
    /// Some irreducible-looking loop finalization shapes reduce to:
    ///
    /// ```text
    /// while true do
    ///     if done then return ... end
    ///     ...
    ///     if should_continue then break end
    /// end
    /// suffix_that_jumps_back_to_loop_head
    /// ```
    ///
    /// The suffix is not really after the loop; it is the continuation payload for
    /// the final guard. Moving it under that guard preserves the backedge and keeps
    /// the loop body executable in source form.
    fn absorb_reentering_loop_suffixes(&self, node: &mut CfgNode) {
        match node {
            CfgNode::Sequence { nodes } => {
                for node in nodes.iter_mut() {
                    self.absorb_reentering_loop_suffixes(node);
                }

                while self.absorb_reentering_loop_suffix(nodes) {}
            }
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.absorb_reentering_loop_suffixes(then_branch);
                if let Some(else_branch) = else_branch {
                    self.absorb_reentering_loop_suffixes(else_branch);
                }
            }
            CfgNode::While { body, .. }
            | CfgNode::NumericFor { body, .. }
            | CfgNode::GenericFor { body, .. } => {
                self.absorb_reentering_loop_suffixes(body);
            }
            _ => {}
        }
    }

    /// Repairs adjacent loop alternatives that were conservatively folded as a guard.
    ///
    /// `fold_head_escape_guard` prefers one-armed guards when adjacent branch ranges
    /// could be sequential work. In the common nested-loop alternative shape, that
    /// leaves:
    ///
    /// ```text
    /// if not cond then
    ///     else_loop
    /// end
    /// then_loop
    /// ```
    ///
    /// If the following range is a matching numeric-for branch, this pass rewrites it
    /// back into `if cond then then_loop else else_loop end`.
    fn fold_adjacent_loop_branches(&self, node: &mut CfgNode) {
        match node {
            CfgNode::Sequence { nodes } => {
                for node in nodes.iter_mut() {
                    self.fold_adjacent_loop_branches(node);
                }

                let mut idx = 0;
                while idx + 1 < nodes.len() {
                    // Candidate right-hand branch is either the next node alone or a
                    // loop setup block followed by a `NumericFor`.
                    let next_end = if idx + 2 < nodes.len()
                        && matches!(nodes[idx + 2], CfgNode::NumericFor { .. })
                    {
                        idx + 3
                    } else {
                        idx + 2
                    };

                    let should_fold = match &nodes[idx] {
                        CfgNode::If {
                            then_branch,
                            else_branch: None,
                            ..
                        } => {
                            // Require both sides to have the same normalized numeric
                            // loop bounds. This keeps the pass from combining adjacent
                            // loops that merely happen to sit next to each other.
                            let then_shape = self.branch_numeric_for_shape(then_branch);
                            let next_shape = self.numeric_for_range_shape(nodes, idx + 1, next_end);
                            then_shape.is_some_and(|then_shape| {
                                next_shape.is_some_and(|next_shape| then_shape == next_shape)
                            })
                        }
                        _ => false,
                    };

                    if !should_fold {
                        idx += 1;
                        continue;
                    }

                    // Convert `if not C then A end; B` into
                    // `if C then B else A end`. The condition inversion is paired
                    // with swapping the old guarded branch into `else`.
                    let next_nodes: Vec<_> = nodes.drain(idx + 1..next_end).collect();
                    let next_branch = CfgNode::Sequence { nodes: next_nodes };
                    let current =
                        std::mem::replace(&mut nodes[idx], CfgNode::Sequence { nodes: Vec::new() });
                    let CfgNode::If {
                        condition,
                        then_branch,
                        else_branch: None,
                    } = current
                    else {
                        unreachable!();
                    };

                    nodes[idx] = CfgNode::If {
                        condition: condition.invert(),
                        then_branch: Box::new(next_branch),
                        else_branch: Some(then_branch),
                    };
                    idx += 1;
                }
            }
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.fold_adjacent_loop_branches(then_branch);
                if let Some(else_branch) = else_branch {
                    self.fold_adjacent_loop_branches(else_branch);
                }
            }
            CfgNode::While { body, .. }
            | CfgNode::NumericFor { body, .. }
            | CfgNode::GenericFor { body, .. } => self.fold_adjacent_loop_branches(body),
            _ => {}
        }
    }

    /// Absorbs one suffix-after-loop pattern from a sequence.
    ///
    /// Returns true when it moved a suffix, allowing the caller to keep scanning the
    /// same sequence until no more nested suffixes match.
    fn absorb_reentering_loop_suffix(&self, nodes: &mut Vec<CfgNode>) -> bool {
        let Some(loop_idx) = nodes.iter().enumerate().find_map(|(idx, node)| {
            if idx + 1 >= nodes.len() {
                return None;
            }

            let CfgNode::While {
                condition: HilExpr::Bool(true),
                body,
            } = node
            else {
                return None;
            };

            let CfgNode::Sequence { nodes: body_nodes } = body.as_ref() else {
                return None;
            };

            let loop_head = body.first_block()?;

            // This pass is intentionally narrow. A return guard tells us the loop
            // already has source-level exits, and the trailing break guard gives us a
            // concrete place to attach the re-entering suffix.
            let has_return_guard = body_nodes.iter().any(|node| match node {
                CfgNode::If { then_branch, .. } => self.node_has_return_exit(then_branch),
                _ => false,
            });

            let ends_with_break_guard = matches!(
                body_nodes.last(),
                Some(CfgNode::If {
                    then_branch,
                    else_branch: None,
                    ..
                }) if matches!(then_branch.as_ref(), CfgNode::Break)
            );

            // Only absorb suffixes that still contain a raw jump to the loop head;
            // otherwise the nodes really are after the loop.
            let suffix_reenters_loop = nodes[idx + 1..]
                .iter()
                .any(|node| self.node_jumps_to_block(node, loop_head));

            (has_return_guard && ends_with_break_guard && suffix_reenters_loop).then_some(idx)
        }) else {
            return false;
        };

        // Everything after the loop becomes the payload of the final break guard.
        // Later escape resolution turns the retained raw jumps into source-level
        // control flow.
        let suffix = nodes.split_off(loop_idx + 1);
        let CfgNode::While { body, .. } = &mut nodes[loop_idx] else {
            unreachable!();
        };
        let CfgNode::Sequence { nodes: body_nodes } = body.as_mut() else {
            unreachable!();
        };
        let Some(CfgNode::If { then_branch, .. }) = body_nodes.last_mut() else {
            unreachable!();
        };

        **then_branch = CfgNode::Sequence { nodes: suffix };
        true
    }

    /// Returns true when a structured node contains a raw or lowered return exit.
    fn node_has_return_exit(&self, node: &CfgNode) -> bool {
        match node {
            CfgNode::Return { .. } => true,
            CfgNode::BasicBlock { block } => {
                matches!(self.cfg.blocks[*block].exit, BlockExit::Return(_))
            }
            CfgNode::Sequence { nodes } => nodes.iter().any(|node| self.node_has_return_exit(node)),
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.node_has_return_exit(then_branch)
                    || else_branch
                        .as_ref()
                        .is_some_and(|branch| self.node_has_return_exit(branch))
            }
            CfgNode::While { body, .. }
            | CfgNode::NumericFor { body, .. }
            | CfgNode::GenericFor { body, .. } => self.node_has_return_exit(body),
            _ => false,
        }
    }

    /// Returns true when a structured node still contains a raw edge to `target`.
    ///
    /// This is used only by post-structuring cleanup passes that need to detect
    /// whether a seemingly external suffix is actually part of a loop.
    fn node_jumps_to_block(&self, node: &CfgNode, target: usize) -> bool {
        match node {
            CfgNode::BasicBlock { block } => match &self.cfg.blocks[*block].exit {
                BlockExit::Jump(block) | BlockExit::Fallthrough(block) => *block == target,
                BlockExit::CondJump {
                    then_block,
                    else_block,
                    ..
                } => *then_block == target || *else_block == target,
                _ => false,
            },
            CfgNode::Sequence { nodes } => nodes
                .iter()
                .any(|node| self.node_jumps_to_block(node, target)),
            CfgNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.node_jumps_to_block(then_branch, target)
                    || else_branch
                        .as_ref()
                        .is_some_and(|branch| self.node_jumps_to_block(branch, target))
            }
            CfgNode::While { body, .. }
            | CfgNode::NumericFor { body, .. }
            | CfgNode::GenericFor { body, .. } => self.node_jumps_to_block(body, target),
            _ => false,
        }
    }

    /// Returns whether `dom` dominates `node`.
    #[must_use]
    pub fn dominates(&mut self, dom: usize, node: usize) -> bool {
        let idoms = self.get_or_calc_idoms();
        idoms.dominates(dom, node)
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
                let Some(tail) = self.get_or_calc_postidoms().idom(head) else {
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
                    cond = cond.invert();
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
                    cond = cond.invert();
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

    fn collapse_acyclic_conditional(&mut self) -> bool {
        let mut work = self.post_order();
        work.reverse();

        while let Some(head) = work.pop() {
            if !self.nodes.contains_key(&head) || self.exact_successors::<2>(head).is_none() {
                continue;
            }

            let Some(tail) = self.get_or_calc_postidoms().idom(head) else {
                continue;
            };

            let Some((mut cond, raw_then, raw_else)) = self.extract_cond_jump(&self.nodes[&head])
            else {
                continue;
            };

            let active_then = self.region_for_block[&raw_then];
            let active_else = self.region_for_block[&raw_else];
            let Some([left, right]) = self.exact_successors(head) else {
                continue;
            };

            let (then_start, else_start) = if left == active_then && right == active_else {
                (left, right)
            } else if left == active_else && right == active_then {
                cond = cond.invert();
                (right, left)
            } else {
                continue;
            };

            if let Some((then_branch, then_used)) =
                self.build_one_armed_branch(head, then_start, else_start)
            {
                self.collapse_one_armed_conditional(head, else_start, then_branch, then_used, cond);
                return true;
            }

            if let Some((else_branch, else_used)) =
                self.build_one_armed_branch(head, else_start, then_start)
            {
                self.collapse_one_armed_conditional(
                    head,
                    then_start,
                    else_branch,
                    else_used,
                    cond.invert(),
                );
                return true;
            }

            let mut then_seen = HashSet::new();
            let Some((then_branch, then_used)) =
                self.build_acyclic_branch(then_start, tail, &mut then_seen)
            else {
                continue;
            };

            let mut else_seen = HashSet::new();
            let Some((else_branch, else_used)) =
                self.build_acyclic_branch(else_start, tail, &mut else_seen)
            else {
                continue;
            };

            if then_used.is_empty() && else_used.is_empty() {
                continue;
            }

            let mut used = then_used;
            used.extend(else_used);
            used.remove(&tail);
            used.remove(&head);

            if !self.is_closed_conditional_region(head, tail, &used) {
                continue;
            }

            let new_id = self.next_id();
            let header_node = self.nodes.remove(&head).unwrap();
            for node in &used {
                self.nodes.remove(node);
            }

            let if_node = build_if_node(cond, then_branch, else_branch)
                .expect("empty conditional region was skipped");

            self.nodes
                .insert(new_id, CfgNode::merge([header_node, if_node]));

            self.update_regionmap(|val| val == head || used.contains(&val), new_id);
            self.transfer_predecessors(head, new_id);

            for node in &used {
                self.successors.remove(node);
                self.predecessors.remove(node);
            }
            self.successors.remove(&head);

            if let Some(tail_preds) = self.predecessors.get_mut(&tail) {
                tail_preds.retain(|&p| p != head && !used.contains(&p));
                tail_preds.push(new_id);
            }
            self.successors.insert(new_id, vec![tail]);

            if head == self.entry_node {
                self.entry_node = new_id;
            }
            self.invalidate_doms();

            return true;
        }

        false
    }

    /// Builds a branch for a conditional where only one side should be folded.
    ///
    /// This is restricted to the current entry node and to branches that end in a
    /// terminal escape. Without those guards, ordinary if/else regions can be
    /// misread as `if cond then ... end; ...`, duplicating the fall-through side.
    fn build_one_armed_branch(
        &mut self,
        head: usize,
        branch_start: usize,
        merge: usize,
    ) -> Option<(CfgNode, HashSet<usize>)> {
        // Keep this fold at the active graph entry. Deeper conditionals are handled
        // by the normal two-arm fold or by the sequence cleanup passes after loops
        // have been recovered.
        if head != self.entry_node {
            return None;
        }

        let mut seen = HashSet::new();
        let (branch, mut used) = self.build_acyclic_branch(branch_start, merge, &mut seen)?;
        if used.is_empty() {
            return None;
        }
        // A one-armed fold is only valid when the branch cannot fall through into
        // the merge path. Otherwise the missing branch would execute both sides.
        if !self.node_ends_with_terminal(&branch) {
            return None;
        }
        used.remove(&merge);
        used.remove(&head);

        if self.is_closed_conditional_region(head, merge, &used) {
            Some((branch, used))
        } else {
            None
        }
    }

    fn collapse_one_armed_conditional(
        &mut self,
        head: usize,
        tail: usize,
        branch: CfgNode,
        used: HashSet<usize>,
        condition: HilExpr,
    ) {
        let new_id = self.next_id();
        let header_node = self.nodes.remove(&head).unwrap();
        for node in &used {
            self.nodes.remove(node);
        }

        self.nodes.insert(
            new_id,
            CfgNode::merge([
                header_node,
                CfgNode::If {
                    condition,
                    then_branch: Box::new(branch),
                    else_branch: None,
                },
            ]),
        );

        self.update_regionmap(|val| val == head || used.contains(&val), new_id);
        self.transfer_predecessors(head, new_id);

        for node in &used {
            self.successors.remove(node);
            self.predecessors.remove(node);
        }
        self.successors.remove(&head);

        if let Some(tail_preds) = self.predecessors.get_mut(&tail) {
            tail_preds.retain(|&p| p != head && !used.contains(&p));
            tail_preds.push(new_id);
        }
        self.successors.insert(new_id, vec![tail]);

        if head == self.entry_node {
            self.entry_node = new_id;
        }
        self.invalidate_doms();
    }

    fn build_acyclic_branch(
        &self,
        node: usize,
        tail: usize,
        seen: &mut HashSet<usize>,
    ) -> Option<(CfgNode, HashSet<usize>)> {
        if node == tail {
            return Some((CfgNode::Sequence { nodes: Vec::new() }, HashSet::new()));
        }
        if !seen.insert(node) {
            return None;
        }

        let current = self.nodes.get(&node)?.clone();
        if matches!(
            self.extract_exit(&current),
            Some(
                BlockExit::FornPrep { .. }
                    | BlockExit::FornLoop { .. }
                    | BlockExit::ForgPrep { .. }
                    | BlockExit::ForgLoop { .. }
            )
        ) {
            return None;
        }

        let mut used = HashSet::from([node]);

        match self.successors.get(&node).map(Vec::as_slice).unwrap_or(&[]) {
            [] => Some((current, used)),
            [next] => {
                let (next_node, next_used) = self.build_acyclic_branch(*next, tail, seen)?;
                used.extend(next_used);
                Some((CfgNode::merge([current, next_node]), used))
            }
            [left, right] => {
                let (mut cond, raw_then, raw_else) = self.extract_cond_jump(&current)?;
                let active_then = self.region_for_block[&raw_then];
                let active_else = self.region_for_block[&raw_else];

                let (then_start, else_start) = if *left == active_then && *right == active_else {
                    (*left, *right)
                } else if *left == active_else && *right == active_then {
                    cond = cond.invert();
                    (*right, *left)
                } else {
                    return None;
                };

                let mut then_seen = seen.clone();
                let (then_branch, then_used) =
                    self.build_acyclic_branch(then_start, tail, &mut then_seen)?;
                let mut else_seen = seen.clone();
                let (else_branch, else_used) =
                    self.build_acyclic_branch(else_start, tail, &mut else_seen)?;

                used.extend(then_used);
                used.extend(else_used);

                let Some(branch) = build_if_node(cond, then_branch, else_branch) else {
                    return Some((current, used));
                };

                Some((CfgNode::merge([current, branch]), used))
            }
            _ => None,
        }
    }

    fn is_closed_conditional_region(
        &self,
        head: usize,
        tail: usize,
        nodes: &HashSet<usize>,
    ) -> bool {
        nodes.iter().all(|node| {
            self.predecessors
                .get(node)
                .into_iter()
                .flatten()
                .all(|pred| *pred == head || nodes.contains(pred))
                && self
                    .successors
                    .get(node)
                    .into_iter()
                    .flatten()
                    .all(|succ| *succ == tail || nodes.contains(succ))
        })
    }

    fn find_backedges(&mut self, node: usize) -> Vec<usize> {
        let mut backedges = Vec::new();
        let Some(preds) = self.predecessors.get(&node).cloned() else {
            return backedges;
        };

        for pred in preds {
            if self.dominates(node, pred) {
                backedges.push(pred);
            }
        }

        backedges
    }

    /// Identifies all nodes belonging to a SESE loop region.
    #[must_use]
    fn get_loop_region(&mut self, head: usize, exit: Option<usize>) -> HashSet<usize> {
        self.post_order()
            .into_iter()
            .filter(|&node| {
                self.dominates(head, node) && exit.is_none_or(|exit| !self.dominates(exit, node))
            })
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
                BlockExit::Jump(raw_target)
                    if self.region_for_block[raw_target] == head
                        && self.extract_cond_jump(&self.nodes[&head]).is_none() =>
                {
                    return Some(Loop::While {
                        cond: HilExpr::Bool(true),
                        exit_block: None,
                        guard: None,
                        absorbed: Vec::new(),
                    });
                }
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

            if let Some(guard) = self.build_loop_guard(head, tail, body_blocks)
                && !guard.absorbed.is_empty()
            {
                return Some(Loop::While {
                    cond: HilExpr::Bool(true),
                    exit_block: guard.exit_block,
                    guard: Some(guard.tree),
                    absorbed: guard.absorbed.into_iter().collect(),
                });
            }

            if then_in_body != else_in_body {
                let (exit_block, invert) = if then_in_body {
                    (active_else, false)
                } else {
                    (active_then, true)
                };

                let final_cond = if invert { cond.invert() } else { cond };
                return Some(Loop::While {
                    cond: final_cond,
                    exit_block: self.nodes.contains_key(&exit_block).then_some(exit_block),
                    guard: None,
                    absorbed: Vec::new(),
                });
            }

            if let Some(guard) = self.build_loop_guard(head, tail, body_blocks) {
                return Some(Loop::While {
                    cond: HilExpr::Bool(true),
                    exit_block: guard.exit_block,
                    guard: Some(guard.tree),
                    absorbed: guard.absorbed.into_iter().collect(),
                });
            }
        }

        None
    }

    fn build_loop_guard(
        &self,
        head: usize,
        tail: usize,
        body_blocks: &HashSet<usize>,
    ) -> Option<GuardBuild> {
        let mut seen = HashSet::new();
        let guard = self.build_guard_tree(head, head, tail, body_blocks, &mut seen)?;

        if guard.has_body && guard.exit_block.is_some() {
            Some(guard)
        } else {
            None
        }
    }

    fn build_guard_tree(
        &self,
        node: usize,
        head: usize,
        tail: usize,
        body_blocks: &HashSet<usize>,
        seen: &mut HashSet<usize>,
    ) -> Option<GuardBuild> {
        if !seen.insert(node) || self.extract_cond_jump(&self.nodes[&node]).is_none() {
            return None;
        }

        let (_, raw_then, raw_else) = self.extract_cond_jump(&self.nodes[&node])?;
        let mut then_seen = seen.clone();
        let mut else_seen = seen.clone();
        let mut then_branch =
            self.build_guard_successor(raw_then, head, tail, body_blocks, &mut then_seen);
        let mut else_branch =
            self.build_guard_successor(raw_else, head, tail, body_blocks, &mut else_seen);

        if then_branch.exit_block.is_none()
            && !then_branch.has_body
            && else_branch.exit_block.is_none()
            && !else_branch.has_body
        {
            return None;
        }

        let exit_block = match (then_branch.exit_block, else_branch.exit_block) {
            (Some(left), Some(right)) if left == right => Some(left),
            (Some(left), None) => Some(left),
            (None, Some(right)) => Some(right),
            (None, None) => None,
            (Some(_), Some(_)) => return None,
        };

        let condition_can_duplicate =
            guard_condition_can_duplicate(&then_branch.tree, &else_branch.tree);
        let condition = self.guard_node_condition(node, !condition_can_duplicate)?;

        let mut absorbed = HashSet::new();
        absorbed.extend(then_branch.absorbed.drain());
        absorbed.extend(else_branch.absorbed.drain());
        if node != head {
            absorbed.insert(node);
        }

        Some(GuardBuild {
            tree: GuardTree::Branch {
                condition,
                then_branch: Box::new(then_branch.tree),
                else_branch: Box::new(else_branch.tree),
            },
            exit_block,
            has_body: then_branch.has_body || else_branch.has_body,
            absorbed,
        })
    }

    fn build_guard_successor(
        &self,
        raw_target: usize,
        head: usize,
        tail: usize,
        body_blocks: &HashSet<usize>,
        seen: &mut HashSet<usize>,
    ) -> GuardBuild {
        let Some(&active) = self.region_for_block.get(&raw_target) else {
            return GuardBuild::exit(raw_target);
        };

        if active == tail || active == head {
            return GuardBuild::body();
        }

        if !body_blocks.contains(&active) {
            return GuardBuild::exit(active);
        }

        if self.extract_cond_jump(&self.nodes[&active]).is_some()
            && let Some(guard) = self.build_guard_tree(active, head, tail, body_blocks, seen)
            && guard.exit_block.is_some()
        {
            return guard;
        }

        if active != raw_target
            && self.nodes.contains_key(&raw_target)
            && self.extract_cond_jump(&self.nodes[&raw_target]).is_some()
            && let Some(guard) = self.build_guard_tree(raw_target, head, tail, body_blocks, seen)
            && guard.exit_block.is_some()
        {
            return guard;
        }

        GuardBuild::body()
    }

    fn guard_node_condition(&self, node: usize, _allow_impure_prelude: bool) -> Option<HilExpr> {
        let (condition, _, _) = self.extract_cond_jump(&self.nodes[&node])?;
        if self.node_has_prelude(&self.nodes[&node]) {
            return None;
        }

        Some(condition)
    }

    fn node_has_prelude(&self, node: &CfgNode) -> bool {
        match node {
            CfgNode::BasicBlock { block } => !self.cfg.blocks[*block].stmts.is_empty(),
            CfgNode::Sequence { nodes } => nodes.iter().any(|node| self.node_has_prelude(node)),
            _ => false,
        }
    }

    fn build_guard_node(&self, guard: &GuardTree, break_payload: &CfgNode) -> Option<CfgNode> {
        match guard {
            GuardTree::Body => None,
            GuardTree::Exit => Some(break_payload.clone()),
            GuardTree::Branch {
                condition,
                then_branch,
                else_branch,
            } => {
                let then_node = self.build_guard_node(then_branch, break_payload);
                let else_node = self.build_guard_node(else_branch, break_payload);

                let guard_if = match (then_node, else_node) {
                    (Some(then_branch), Some(else_branch)) => CfgNode::If {
                        condition: condition.clone(),
                        then_branch: Box::new(then_branch),
                        else_branch: Some(Box::new(else_branch)),
                    },
                    (Some(then_branch), None) => CfgNode::If {
                        condition: condition.clone(),
                        then_branch: Box::new(then_branch),
                        else_branch: None,
                    },
                    (None, Some(else_branch)) => CfgNode::If {
                        condition: condition.clone().invert(),
                        then_branch: Box::new(else_branch),
                        else_branch: None,
                    },
                    (None, None) => return None,
                };

                Some(guard_if)
            }
        }
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
            let mut selected_loop = None;
            for tail in self.find_backedges(head) {
                let natural_body = self.get_natural_loop(head, tail);

                // We can expect two types of a loop here:
                // 1. while: the backedge is an unconditional jump, while the head either jumps to the body or the loop exit
                // 2. repeat..until: the backedge is a conditional jump, the header can be any block
                if let Some(kind) = self.identify_loop(head, tail, &natural_body) {
                    selected_loop = Some((tail, kind));
                    break;
                }
            }

            if let Some((tail, kind)) = selected_loop {
                let loop_exit = kind.exit_block();
                let mut body_blocks_used = self.get_loop_region(head, loop_exit);
                if let Loop::While { absorbed, .. } = &kind {
                    for block in absorbed {
                        body_blocks_used.remove(block);
                    }
                }

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
                let require_empty_continue_target =
                    matches!(&kind, Loop::NumericFor { .. } | Loop::GenericFor { .. });
                body_ast.resolve_escapes(
                    continue_tgt,
                    continue_tgt_alt,
                    loop_exit,
                    self.cfg,
                    &self.region_for_block,
                    require_empty_continue_target,
                );

                let loop_id = self.next_id();
                let head_node = self.nodes.remove(&head).unwrap();

                let mut absorbed_blocks = HashSet::new();
                let (region_entry, loop_node, exit_block) = match kind {
                    Loop::While {
                        cond,
                        exit_block,
                        guard,
                        absorbed,
                    } => {
                        absorbed_blocks.extend(absorbed);
                        let mut effective_exit = exit_block;
                        let mut break_payload = CfgNode::Break;

                        if let Some(exit_block) = exit_block
                            && let Some(exit_node) = self.nodes.get(&exit_block)
                            && let Some(BlockExit::Jump(next_raw)) = self.extract_exit(exit_node)
                            && let Some(&next_block) = self.region_for_block.get(next_raw)
                            && next_block != head
                        {
                            effective_exit = Some(next_block);
                            absorbed_blocks.insert(exit_block);
                            if self.node_emits_statements(exit_node) {
                                break_payload = CfgNode::merge([exit_node.clone(), CfgNode::Break]);
                            }
                        }

                        let loop_node = if let Some(guard) = guard {
                            if matches!(break_payload, CfgNode::Break) {
                                CfgNode::While {
                                    condition: BoolExpr::from(guard).into_hil(),
                                    body: Box::new(body_ast),
                                }
                            } else {
                                let guard_node = self
                                    .build_guard_node(&guard, &break_payload)
                                    .unwrap_or_else(|| CfgNode::If {
                                        condition: cond.invert(),
                                        then_branch: Box::new(break_payload.clone()),
                                        else_branch: None,
                                    });

                                CfgNode::While {
                                    condition: HilExpr::Bool(true),
                                    body: Box::new(CfgNode::merge([guard_node, body_ast])),
                                }
                            }
                        } else if self.node_emits_statements(&head_node)
                            || !matches!(break_payload, CfgNode::Break)
                        {
                            let mut parts = Vec::with_capacity(3);
                            if self.node_emits_statements(&head_node) {
                                parts.push(head_node);
                            }

                            let break_guard = CfgNode::If {
                                condition: cond.invert(),
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
                        Some(exit_block),
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
                            Some(exit_block),
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
                            Some(exit_block),
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

                if let Some(exit_block) = exit_block {
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
                } else {
                    self.successors.insert(loop_id, Vec::new());
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
                if region_entry == self.entry_node || head == self.entry_node {
                    self.entry_node = loop_id;
                }
                self.invalidate_doms();

                work.push(loop_id);
                changed = true;
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
            self.refresh_entry_node();
            self.prune_stale_edges();
            self.refresh_entry_node();

            if self.collapse_sequential() {
                continue;
            }

            if self.collapse_conditional() {
                continue;
            }

            if self.collapse_acyclic_conditional() {
                continue;
            }

            if self.collapse_loops() {
                continue;
            }

            break;
        }
    }
}

fn guard_condition_can_duplicate(then_branch: &GuardTree, else_branch: &GuardTree) -> bool {
    !matches!(then_branch, GuardTree::Body | GuardTree::Exit)
        && !matches!(else_branch, GuardTree::Body | GuardTree::Exit)
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

fn build_if_node(
    condition: HilExpr,
    then_branch: CfgNode,
    else_branch: CfgNode,
) -> Option<CfgNode> {
    match (then_branch.is_empty(), else_branch.is_empty()) {
        (false, false) => Some(CfgNode::If {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: Some(Box::new(else_branch)),
        }),
        (false, true) => Some(CfgNode::If {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: None,
        }),
        (true, false) => Some(CfgNode::If {
            condition: condition.invert(),
            then_branch: Box::new(else_branch),
            else_branch: None,
        }),
        (true, true) => None,
    }
}

pub fn structure(cfg: &ControlFlowGraph) -> (RegionNode, bool) {
    let mut fg = FoldableGraph::new(cfg);

    fg.structure();
    fg.refresh_entry_node();

    let reduced = fg.nodes.iter().len() == 1;

    let mut root = fg
        .nodes
        .remove(&fg.entry_node)
        .expect("entry node should be present after refreshing from the region map");
    root.strip_virtual_exits();

    // These cleanup passes operate on the final tree rather than the foldable graph:
    // they repair shapes that only become obvious after all graph-level regions have
    // been collapsed.
    fg.absorb_reentering_loop_suffixes(&mut root);
    fg.fold_adjacent_loop_branches(&mut root);

    root.resolve_returns(cfg);
    (root.lower(cfg), reduced)
}

#[cfg(test)]
mod tests {
    use id_arena::Arena;
    use smallvec::SmallVec;

    use crate::common::ToSpanned as _;
    use crate::hil::{
        cflow::{
            cfg::{Block, BlockExit, ControlFlowGraph},
            graph::{AdjGraph, GraphView as _},
        },
        ir::{HilExpr, HilStmt},
        lifter::ssa::Symbol,
    };

    use super::{CfgNode, FoldableGraph, RegionNode, structure};

    fn cfg_from_blocks(blocks: Vec<Block>) -> ControlFlowGraph {
        let (successors, predecessors) =
            crate::hil::cflow::graph::build_graph(blocks.iter().map(Block::exit_targets));
        let idoms = AdjGraph::new(0, &successors, &predecessors).build_idoms();

        ControlFlowGraph {
            blocks,
            entry_block: 0,
            successors,
            predecessors,
            idoms,
            params: Vec::new(),
            upvalues: Vec::new(),
        }
    }

    // This is an exception to the rule of verifying by integration testing over unit testing, as naturally
    // this would not only force a timeout but put a lot of work on the CPU. Resolving the shape of the loop
    // is still tested extensively in the integration tests, but this "edge case" is here only because it's
    // simpler to manually build and check it over testing it in the test suite.
    #[test]
    fn structures_exitless_self_loop() {
        let cfg = cfg_from_blocks(vec![Block {
            stmts: Vec::new(),
            exit: BlockExit::Jump(0),
        }]);

        let (root, reduced) = structure(&cfg);

        assert!(reduced);
        assert!(matches!(
            root,
            RegionNode::While {
                condition: HilExpr::Bool(true),
                ..
            }
        ));
    }

    #[test]
    fn guard_prelude_rejects_impure_single_read() {
        let mut symbols: Arena<_> = Arena::new();
        let tmp = symbols.alloc(Symbol::reg(0));

        let cfg = cfg_from_blocks(vec![
            Block {
                stmts: vec![
                    HilStmt::Assign {
                        left: HilExpr::Symbol(tmp),
                        value: HilExpr::Call {
                            fun: Box::new(HilExpr::Global("make".into())),
                            args: Vec::new(),
                        },
                    }
                    .to_spanned(0),
                ],
                exit: BlockExit::CondJump {
                    cond: HilExpr::Symbol(tmp),
                    then_block: 1,
                    else_block: 2,
                },
            },
            Block {
                stmts: Vec::new(),
                exit: BlockExit::Return(SmallVec::new()),
            },
            Block {
                stmts: Vec::new(),
                exit: BlockExit::Return(SmallVec::new()),
            },
        ]);
        let graph = FoldableGraph::new(&cfg);

        assert_eq!(graph.guard_node_condition(0, false), None);
    }

    #[test]
    fn shared_fallback_chain_rejects_cycles() {
        let cfg = cfg_from_blocks(vec![
            Block {
                stmts: Vec::new(),
                exit: BlockExit::CondJump {
                    cond: HilExpr::Bool(true),
                    then_block: 0,
                    else_block: 1,
                },
            },
            Block {
                stmts: Vec::new(),
                exit: BlockExit::Return(SmallVec::new()),
            },
        ]);
        let graph = FoldableGraph::new(&cfg);
        let nodes = vec![
            CfgNode::BasicBlock { block: 0 },
            CfgNode::BasicBlock { block: 1 },
        ];

        assert!(graph.build_shared_fallback_chain(&nodes, 0, 1).is_none());
    }
}
