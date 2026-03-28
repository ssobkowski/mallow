use std::collections::HashSet;

use smallvec::SmallVec;

use crate::ast::UnOp;
use crate::hil::ir::HilExpr;
use crate::hil::lifter::symbol::SymbolId;

use super::analysis::{
    branch_has_plain_backedge, find_if_else_join, find_loop_exit_block, resolve_generic_for_tail,
    resolve_numeric_for_tail,
};
use super::graph::{BlockExit, ControlFlowGraph};

/// Ordered list of structured region nodes.
#[derive(Debug, Clone, Default)]
pub struct RegionBlock {
    pub nodes: Vec<RegionNode>,
}

/// One structured control-flow node in the intermediate region tree.
#[derive(Debug, Clone)]
pub enum RegionNode {
    /// A plain basic block payload that does not by itself decide control transfer.
    BasicBlock { block: usize },
    /// A structured if/else split with optional merge block.
    If {
        condition: HilExpr,
        then_branch: RegionBlock,
        else_branch: RegionBlock,
    },
    /// A structured while loop recovered from backedges.
    While {
        condition: HilExpr,
        body: RegionBlock,
    },
    /// A structured repeat/until loop recovered from backedges.
    RepeatUntil {
        condition: HilExpr,
        body: RegionBlock,
    },
    /// A structured numeric `for` loop recovered from `FORNPREP/FORNLOOP`.
    NumericFor {
        body: RegionBlock,
        start: SymbolId,
        end: SymbolId,
        step: SymbolId,
    },
    /// A structured generic `for` loop recovered from `FORGPREP/FORGLOOP`.
    GenericFor {
        body: RegionBlock,
        vars: SmallVec<[SymbolId; 3]>,
        exprs: [SymbolId; 3],
    },
    /// Explicit `continue` edge for a recovered loop.
    Continue,
    /// Explicit `break` edge from a loop body.
    Break,
    /// Explicit return.
    Return { values: Vec<HilExpr> },
}

/// Stateful region builder used to avoid recursive region expansion loops.
pub struct RegionBuilder<'a> {
    cfg: &'a ControlFlowGraph,
    active_regions: HashSet<(usize, Option<usize>, Option<usize>)>,
}

impl<'a> RegionBuilder<'a> {
    /// Creates a new builder for one CFG.
    pub fn new(cfg: &'a ControlFlowGraph) -> Self {
        Self {
            cfg,
            active_regions: HashSet::new(),
        }
    }

    /// Structures a linear CFG region into canonical region nodes.
    pub fn build_region(&mut self, current: usize, stop_at: Option<usize>) -> RegionBlock {
        self.build_region_with_loop(current, stop_at, None)
    }

    fn build_region_with_loop(
        &mut self,
        current: usize,
        stop_at: Option<usize>,
        loop_exit: Option<usize>,
    ) -> RegionBlock {
        let key = (current, stop_at, loop_exit);
        if !self.active_regions.insert(key) {
            return RegionBlock::default();
        }

        let mut nodes = Vec::new();
        let mut curr_id = current;
        let mut visited_in_region = HashSet::new();

        while Some(curr_id) != stop_at && curr_id < self.cfg.blocks.len() {
            if !visited_in_region.insert(curr_id) {
                break;
            }

            let block = &self.cfg.blocks[curr_id];
            if !block.stmts.is_empty() {
                nodes.push(RegionNode::BasicBlock { block: curr_id });
            }

            match &block.exit {
                BlockExit::Fallthrough(next) | BlockExit::Jump(next) => {
                    if *next < curr_id && self.cfg.dominates(*next, curr_id) {
                        nodes.push(RegionNode::Continue);
                        break;
                    }
                    if Some(*next) == loop_exit {
                        nodes.push(RegionNode::Break);
                        break;
                    }
                    curr_id = *next;
                }
                BlockExit::CondJump {
                    cond,
                    then_block,
                    else_block,
                } => {
                    let then_backedges = branch_has_plain_backedge(*then_block, curr_id, self.cfg);
                    let else_backedges = branch_has_plain_backedge(*else_block, curr_id, self.cfg);

                    if then_backedges != else_backedges {
                        let (loop_block, exit_branch, loop_branch_is_then) = if then_backedges {
                            (*then_block, *else_block, true)
                        } else {
                            (*else_block, *then_block, false)
                        };
                        let exit_block =
                            find_loop_exit_block(curr_id, exit_branch, loop_block, self.cfg);

                        let mut body = self.build_region_with_loop(
                            loop_block,
                            Some(curr_id),
                            Some(exit_block),
                        );

                        if loop_branch_is_then {
                            // while
                            nodes.push(RegionNode::While {
                                condition: cond.clone(),
                                body,
                            });
                        } else {
                            // repeat..until
                            if matches!(nodes.last(), Some(RegionNode::BasicBlock { block: b }) if *b == curr_id)
                            {
                                nodes.pop();
                                body.nodes
                                    .insert(0, RegionNode::BasicBlock { block: curr_id });
                            }

                            nodes.push(RegionNode::RepeatUntil {
                                condition: cond.clone(),
                                body,
                            });
                        }

                        curr_id = exit_block;
                        continue;
                    }

                    let merge_block = find_if_else_join(*then_block, *else_block, self.cfg);
                    let mut then_branch =
                        self.build_branch_region(*then_block, merge_block, loop_exit);
                    let mut else_branch =
                        self.build_branch_region(*else_block, merge_block, loop_exit);

                    // Invert then-branch and else-branch if then-branch is empty, and else-branch isn't
                    // (CFG's short circuit folding leaves if's like that.) It also simply looks better.
                    let mut condition = cond.clone();
                    if !else_branch.nodes.is_empty() && then_branch.nodes.is_empty() {
                        std::mem::swap(&mut then_branch, &mut else_branch);
                        condition = invert_condition(condition);
                    }

                    nodes.push(RegionNode::If {
                        condition,
                        then_branch,
                        else_branch,
                    });

                    if let Some(merge_block) = merge_block {
                        curr_id = merge_block;
                    } else {
                        break;
                    }
                }
                BlockExit::FornPrep {
                    base,
                    body_block,
                    start,
                    end,
                    step,
                    ..
                } => {
                    if let Some(tail) =
                        resolve_numeric_for_tail(curr_id, *base, *body_block, self.cfg)
                    {
                        let body = self.build_region_with_loop(
                            tail.body,
                            Some(tail.exit),
                            Some(tail.exit),
                        );
                        nodes.push(RegionNode::NumericFor {
                            body,
                            start: *start,
                            end: *end,
                            step: *step,
                        });
                        curr_id = tail.exit;
                    } else {
                        panic!(
                            "failed to resolve numeric for tail: curr_id = {}, body_block = {}",
                            curr_id, body_block
                        )
                    }
                }
                BlockExit::ForgPrep {
                    base,
                    body_block,
                    exprs,
                    ..
                } => {
                    if let Some(tail) =
                        resolve_generic_for_tail(curr_id, *base, *body_block, self.cfg)
                    {
                        let body = self.build_region_with_loop(
                            tail.body,
                            Some(tail.exit),
                            Some(tail.exit),
                        );
                        nodes.push(RegionNode::GenericFor {
                            vars: tail.vars.clone(),
                            exprs: *exprs,
                            body,
                        });
                        curr_id = tail.exit;
                    } else {
                        panic!(
                            "failed to resolve numeric for tail: curr_id = {}, body_block = {}",
                            curr_id, body_block
                        )
                    }
                }
                BlockExit::Return(values) => {
                    nodes.push(RegionNode::Return {
                        values: values.clone(),
                    });
                    break;
                }
                BlockExit::FornLoop { .. } | BlockExit::ForgLoop { .. } => {
                    break;
                }
            }
        }

        self.active_regions.remove(&key);
        RegionBlock { nodes }
    }

    fn build_branch_region(
        &mut self,
        branch_start: usize,
        stop_at: Option<usize>,
        loop_exit: Option<usize>,
    ) -> RegionBlock {
        if Some(branch_start) == loop_exit {
            return RegionBlock {
                nodes: vec![RegionNode::Break],
            };
        }

        self.build_region_with_loop(branch_start, stop_at, loop_exit)
    }
}

// todo: this is really basic
#[must_use]
fn invert_condition(expr: HilExpr) -> HilExpr {
    HilExpr::Unary {
        op: UnOp::Not,
        expr: Box::new(expr),
    }
}
