use std::collections::HashSet;

use smallvec::SmallVec;

use crate::hil::cflow::common::invert_condition;
use crate::hil::ir::HilExpr;
use crate::hil::lifter::ssa::SymbolId;

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
        var: SymbolId,
        start: HilExpr,
        end: HilExpr,
        step: HilExpr,
    },
    /// A structured generic `for` loop recovered from `FORGPREP/FORGLOOP`.
    GenericFor {
        body: RegionBlock,
        vars: SmallVec<[SymbolId; 3]>,
        exprs: [HilExpr; 3],
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
                        if let Some(loop_header) = stop_at
                            && *next != loop_header
                        {
                            nodes.push(RegionNode::Continue);
                        }
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

                    let then_is_continue = Some(*then_block) == stop_at;
                    let else_is_continue = Some(*else_block) == stop_at;

                    if then_backedges != else_backedges && !then_is_continue && !else_is_continue {
                        let (loop_block, exit_branch, loop_branch_is_then) = if then_backedges {
                            (*then_block, *else_block, true)
                        } else {
                            (*else_block, *then_block, false)
                        };

                        let exit_block =
                            find_loop_exit_block(curr_id, exit_branch, loop_block, self.cfg);

                        // We already know this is a loop header (either then or else is a backedge
                        // to the current block), the way to distinguish a while from a repeat..until
                        // is that repeat..until will have already been visited - repeat..until's CondJump
                        // is at the bottom, while while's CondJump is at the top.
                        let is_repeat =
                            loop_block < curr_id || visited_in_region.contains(&loop_block);

                        // until <cond> is inverse of while <cond> - but the logic for `loop_branch_is_then`
                        // still stands, so we flip it with a XOR if it's a repeat loop
                        let condition = if loop_branch_is_then ^ is_repeat {
                            cond.clone()
                        } else {
                            invert_condition(cond.clone())
                        };

                        if is_repeat {
                            // We have already inserted the loop's body as regular region nodes. The loop body
                            // is essentially everything up to block 'loop_block'.

                            // We find the "split point" between what is our body and what is not.
                            let split = nodes
                                .iter()
                                .rposition(|node| matches!(node, RegionNode::BasicBlock { block } if *block < loop_block))
                                .map_or(0, |i| i + 1);
                            // Then remove everything up to that point that we have added previously.
                            let loop_body: Vec<_> = nodes.drain(split..).collect();
                            nodes.push(RegionNode::RepeatUntil {
                                condition,
                                body: RegionBlock { nodes: loop_body },
                            })
                        } else if exit_branch == exit_block {
                            // A standard while loop - the exit branch doesn't contain any hidden
                            // statements we care about, so we can safely extract the condition.
                            let body = self.build_region_with_loop(
                                loop_block,
                                Some(curr_id),
                                Some(exit_block),
                            );
                            nodes.push(RegionNode::While { condition, body });
                        } else {
                            // The exit branch is an early break containing statements (like `found = index; break`).
                            // If we extract this as a `while cond` loop, we will set `curr_id = exit_block` and
                            // completely skip processing the exit branch, deleting its statements.
                            // To preserve them, we emit a `while true do` loop and treat the condition as an `If`.
                            let header_node = if !block.stmts.is_empty() {
                                Some(nodes.pop().unwrap())
                            } else {
                                None
                            };

                            let break_cond = if loop_branch_is_then {
                                invert_condition(cond.clone())
                            } else {
                                cond.clone()
                            };

                            let break_node = RegionNode::If {
                                condition: break_cond,
                                // Safely parse the exit branch so we don't lose the statements.
                                then_branch: self.build_branch_region(
                                    exit_branch,
                                    Some(exit_block),
                                    Some(exit_block),
                                ),
                                else_branch: RegionBlock::default(),
                            };

                            let mut loop_body = Vec::new();
                            if let Some(node) = header_node {
                                loop_body.push(node);
                            }
                            loop_body.push(break_node);

                            let rest = self.build_region_with_loop(
                                loop_block,
                                Some(curr_id),
                                Some(exit_block),
                            );
                            loop_body.extend(rest.nodes);

                            nodes.push(RegionNode::While {
                                condition: HilExpr::Bool(true),
                                body: RegionBlock { nodes: loop_body },
                            });
                        }

                        curr_id = exit_block;
                        continue;
                    }

                    // Detect if either branch immediately jumps to the loop boundaries.
                    // stop_at = loop header (Continue), loop_exit = loop end (Break)
                    let then_is_break = Some(*then_block) == loop_exit;
                    let else_is_break = Some(*else_block) == loop_exit;

                    let then_terminal = then_is_continue || then_is_break;
                    let else_terminal = else_is_continue || else_is_break;

                    let merge_block;
                    let mut then_branch = RegionBlock::default();
                    let mut else_branch = RegionBlock::default();

                    if then_terminal && else_terminal {
                        // Case 1: Both branches exit the loop, (e.g. if <cond> then break else continue end),
                        // there is no merge point because control flow never survives this block
                        merge_block = None;
                        if then_is_continue {
                            then_branch.nodes.push(RegionNode::Continue);
                        }
                        if then_is_break {
                            then_branch.nodes.push(RegionNode::Break);
                        }
                        if else_is_continue {
                            else_branch.nodes.push(RegionNode::Continue);
                        }
                        if else_is_break {
                            else_branch.nodes.push(RegionNode::Break);
                        }
                    } else if then_terminal {
                        // Case 2: `then` is an early exit.
                        // We do NOT want to put the rest of the loop inside the `else` block.
                        // By setting `merge_block = else_block` and leaving `else_branch` empty,
                        // we force the structurer to emit `if cond then break end`, and then
                        // naturally process `else_block` as the next sequential statements.
                        merge_block = Some(*else_block);
                        if then_is_continue {
                            then_branch.nodes.push(RegionNode::Continue);
                        }
                        if then_is_break {
                            then_branch.nodes.push(RegionNode::Break);
                        }
                    } else if else_terminal {
                        // Case 3: `else` is an early exit.
                        // Exact same logic as above, but flipped. `then_branch` is deliberately empty.
                        merge_block = Some(*then_block);
                        if else_is_continue {
                            else_branch.nodes.push(RegionNode::Continue);
                        }
                        if else_is_break {
                            else_branch.nodes.push(RegionNode::Break);
                        }
                    } else {
                        // Case 4: Standard if/else
                        // Neither branch is a loop exit. We safely find where they rejoin in the CFG,
                        // and recursively build both branches up to that point.
                        merge_block = find_if_else_join(*then_block, *else_block, self.cfg);
                        then_branch = self.build_branch_region(*then_block, merge_block, loop_exit);
                        else_branch = self.build_branch_region(*else_block, merge_block, loop_exit);
                    }

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
                    var,
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
                            var: *var,
                            start: start.clone(),
                            end: end.clone(),
                            step: step.clone(),
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
                            exprs: exprs.clone(),
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
