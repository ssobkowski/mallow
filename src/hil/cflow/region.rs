use std::collections::HashSet;

use crate::ast::UnOp;
use crate::hil::ir::HilExpr;

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
        header: usize,
        condition: HilExpr,
        then_branch: RegionBlock,
        else_branch: RegionBlock,
        merge_block: Option<usize>,
    },
    /// A structured while loop recovered from backedges.
    While {
        header: usize,
        condition: HilExpr,
        body: RegionBlock,
        exit_block: usize,
    },
    /// A structured numeric `for` loop recovered from `FORNPREP/FORNLOOP`.
    NumericFor {
        /// Preheader block containing `ForNPrep` and any synthetic bound/step/current setup.
        header: usize,
        /// Base register of Luau's numeric-for tuple:
        /// `base` = limit, `base + 1` = step, `base + 2` = visible loop variable/current value.
        base: usize,
        /// Structured loop body, already sliced to stop before `exit_block`.
        body: RegionBlock,
        /// First block reached when the loop terminates normally.
        exit_block: usize,
    },
    /// A structured generic `for` loop recovered from `FORGPREP/FORGLOOP`.
    GenericFor {
        /// Preheader block containing `ForGPrep` and any synthetic iterator-state setup.
        header: usize,
        /// Base register of Luau's generic-for tuple:
        /// `base..=base+2` are iterator/state/control, yielded variables start at `base + 3`.
        base: usize,
        /// Number of visible loop variables yielded by each iteration.
        result_count: usize,
        /// Structured loop body, already sliced to stop before `exit_block`.
        body: RegionBlock,
        /// First block reached when the loop terminates normally.
        exit_block: usize,
    },
    /// Explicit `continue` edge for a recovered loop.
    Continue {
        from_block: usize,
        target_loop_header: usize,
    },
    /// Explicit `break` edge from a loop body.
    Break {
        from_block: usize,
        target_exit: usize,
    },
    /// Explicit return.
    Return {
        from_block: usize,
        values: Vec<HilExpr>,
    },
    /// Fallback edge for shapes not yet fully structured.
    Jump { from_block: usize, target: usize },
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
                        nodes.push(RegionNode::Continue {
                            from_block: curr_id,
                            target_loop_header: *next,
                        });
                        break;
                    }
                    if Some(*next) == loop_exit {
                        nodes.push(RegionNode::Break {
                            from_block: curr_id,
                            target_exit: *next,
                        });
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

                        let body = self.build_region_with_loop(
                            loop_block,
                            Some(curr_id),
                            Some(exit_block),
                        );
                        let condition = if loop_branch_is_then {
                            cond.clone()
                        } else {
                            invert_condition(cond.clone())
                        };

                        nodes.push(RegionNode::While {
                            header: curr_id,
                            condition,
                            body,
                            exit_block,
                        });

                        curr_id = exit_block;
                        continue;
                    }

                    let merge_block = find_if_else_join(*then_block, *else_block, self.cfg);
                    let then_branch =
                        self.build_branch_region(curr_id, *then_block, merge_block, loop_exit);
                    let else_branch =
                        self.build_branch_region(curr_id, *else_block, merge_block, loop_exit);

                    nodes.push(RegionNode::If {
                        header: curr_id,
                        condition: cond.clone(),
                        then_branch,
                        else_branch,
                        merge_block,
                    });

                    if let Some(merge_block) = merge_block {
                        curr_id = merge_block;
                    } else {
                        break;
                    }
                }
                BlockExit::ForNPrep { base, loop_block } => {
                    if let Some((_tail_block, body_block, exit_block)) =
                        resolve_numeric_for_tail(curr_id, *base, *loop_block, self.cfg)
                    {
                        let body = self.build_region_with_loop(
                            body_block,
                            Some(exit_block),
                            Some(exit_block),
                        );
                        nodes.push(RegionNode::NumericFor {
                            header: curr_id,
                            base: *base,
                            body,
                            exit_block,
                        });
                        curr_id = exit_block;
                    } else {
                        nodes.push(RegionNode::Jump {
                            from_block: curr_id,
                            target: *loop_block,
                        });
                        curr_id = *loop_block;
                    }
                }
                BlockExit::ForGPrep { base, loop_block } => {
                    if let Some((_tail_block, body_block, exit_block, result_count)) =
                        resolve_generic_for_tail(curr_id, *base, *loop_block, self.cfg)
                    {
                        let body = self.build_region_with_loop(
                            body_block,
                            Some(exit_block),
                            Some(exit_block),
                        );
                        nodes.push(RegionNode::GenericFor {
                            header: curr_id,
                            base: *base,
                            result_count,
                            body,
                            exit_block,
                        });
                        curr_id = exit_block;
                    } else {
                        nodes.push(RegionNode::Jump {
                            from_block: curr_id,
                            target: *loop_block,
                        });
                        curr_id = *loop_block;
                    }
                }
                BlockExit::Return(values) => {
                    nodes.push(RegionNode::Return {
                        from_block: curr_id,
                        values: values.clone(),
                    });
                    break;
                }
                BlockExit::ForNLoop { .. } => {
                    break;
                }
                BlockExit::ForGLoop { .. } => break,
            }
        }

        self.active_regions.remove(&key);
        RegionBlock { nodes }
    }

    fn build_branch_region(
        &mut self,
        from_block: usize,
        branch_start: usize,
        stop_at: Option<usize>,
        loop_exit: Option<usize>,
    ) -> RegionBlock {
        if Some(branch_start) == loop_exit {
            return RegionBlock {
                nodes: vec![RegionNode::Break {
                    from_block,
                    target_exit: branch_start,
                }],
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

#[cfg(test)]
mod tests {
    use crate::hil::{
        cflow::graph::{Block, BlockExit, ControlFlowGraph},
        ir::{HilExpr, HilStmt, Spanned},
    };

    use super::{RegionBuilder, RegionNode};

    #[test]
    fn build_region_omits_synthetic_generic_for_tail_nodes() {
        let cfg = ControlFlowGraph::new(
            vec![
                Block::new(
                    0,
                    Vec::new(),
                    BlockExit::ForGPrep {
                        base: 1,
                        loop_block: 2,
                    },
                ),
                Block::new(
                    1,
                    vec![Spanned::new(
                        HilStmt::Assign {
                            left: HilExpr::Local(4),
                            value: HilExpr::Local(2),
                        },
                        0,
                    )],
                    BlockExit::Fallthrough(2),
                ),
                Block::new(
                    2,
                    Vec::new(),
                    BlockExit::ForGLoop {
                        base: 1,
                        body_block: 1,
                        exit_block: 3,
                        result_count: 2,
                    },
                ),
                Block::new(3, Vec::new(), BlockExit::Return(Vec::new())),
            ],
            0,
        );

        let mut builder = RegionBuilder::new(&cfg);
        let region = builder.build_region(0, None);

        let RegionNode::GenericFor { body, .. } = &region.nodes[0] else {
            panic!("expected generic for");
        };

        assert!(matches!(
            body.nodes.as_slice(),
            [RegionNode::BasicBlock { block: 1 }]
        ));
    }

    #[test]
    fn build_region_emits_break_for_direct_loop_exit_branch() {
        let cfg = ControlFlowGraph::new(
            vec![
                Block::new(
                    0,
                    Vec::new(),
                    BlockExit::CondJump {
                        cond: HilExpr::Local(0),
                        then_block: 1,
                        else_block: 3,
                    },
                ),
                Block::new(
                    1,
                    Vec::new(),
                    BlockExit::CondJump {
                        cond: HilExpr::Local(1),
                        then_block: 3,
                        else_block: 2,
                    },
                ),
                Block::new(2, Vec::new(), BlockExit::Jump(0)),
                Block::new(3, Vec::new(), BlockExit::Return(Vec::new())),
            ],
            0,
        );

        let mut builder = RegionBuilder::new(&cfg);
        let region = builder.build_region(0, None);

        let RegionNode::While {
            body, exit_block, ..
        } = &region.nodes[0]
        else {
            panic!("expected while");
        };
        assert_eq!(*exit_block, 3);

        let RegionNode::If {
            then_branch,
            else_branch,
            ..
        } = &body.nodes[0]
        else {
            panic!("expected break-if inside while");
        };

        assert!(matches!(
            then_branch.nodes.as_slice(),
            [RegionNode::Break {
                from_block: 1,
                target_exit: 3
            }]
        ));
        assert!(matches!(
            else_branch.nodes.as_slice(),
            [RegionNode::Continue {
                from_block: 2,
                target_loop_header: 0
            }]
        ));
    }
}
