//! Cleans up explicit `continue` nodes that are equivalent to structured
//! fallthrough in the current loop.
//!
//! Region recovery deliberately emits CFG-faithful control transfers. This pass
//! only removes a `continue` when the enclosing structured position already
//! falls through to the same loop continuation, or extracts a plain
//! `else continue`/`then continue` branch into an early guard.

use crate::hil::{
    StructuredFunction,
    cflow::region::RegionNode,
    visitor::{VisitorMut, walk_region_mut},
};

#[derive(Default)]
struct ContinueCleanup {
    changed: bool,
}

impl ContinueCleanup {
    fn simplify_loop_body(&mut self, body: &mut RegionNode) {
        self.visit_inside_loop(body);
        self.simplify_loop_tail(body);
    }

    fn visit_inside_loop(&mut self, region: &mut RegionNode) {
        match region {
            RegionNode::BasicBlock { .. }
            | RegionNode::Continue
            | RegionNode::Break
            | RegionNode::Return { .. } => {}
            RegionNode::Sequence { nodes } => {
                for node in nodes.iter_mut() {
                    self.visit_inside_loop(node);
                }

                self.extract_continue_guards(nodes);
            }
            RegionNode::If {
                condition: _,
                then_branch,
                else_branch,
            } => {
                self.visit_inside_loop(then_branch);
                if let Some(else_branch) = else_branch {
                    self.visit_inside_loop(else_branch);
                }
            }
            RegionNode::While { .. }
            | RegionNode::RepeatUntil { .. }
            | RegionNode::NumericFor { .. }
            | RegionNode::GenericFor { .. } => self.visit_region(region),
        }
    }

    fn extract_continue_guards(&mut self, nodes: &mut Vec<RegionNode>) {
        self.changed |= remove_empty_nodes(nodes);

        let mut index = 0;
        while index + 1 < nodes.len() {
            let Some(fallthrough) = extract_continue_guard(&mut nodes[index]) else {
                index += 1;
                continue;
            };

            if !fallthrough.is_empty() {
                nodes.insert(index + 1, fallthrough);
            }

            self.changed = true;
            index += 1;
        }
    }

    fn simplify_loop_tail(&mut self, region: &mut RegionNode) -> bool {
        let mut changed = false;

        match region {
            RegionNode::Continue => {
                *region = RegionNode::empty();
                changed = true;
            }
            RegionNode::Sequence { nodes } => {
                changed |= self.simplify_sequence_tail(nodes);
            }
            RegionNode::If {
                condition,
                then_branch,
                else_branch,
            } => {
                changed |= self.simplify_loop_tail(then_branch);
                if let Some(else_branch) = else_branch {
                    changed |= self.simplify_loop_tail(else_branch);
                }

                if else_branch.as_deref().is_some_and(RegionNode::is_empty) {
                    *else_branch = None;
                    changed = true;
                }

                if then_branch.is_empty()
                    && let Some(promoted_else) = else_branch.take()
                    && !promoted_else.is_empty()
                {
                    *condition = condition.clone().invert();
                    *then_branch = promoted_else;
                    changed = true;
                }
            }
            RegionNode::BasicBlock { .. }
            | RegionNode::While { .. }
            | RegionNode::RepeatUntil { .. }
            | RegionNode::NumericFor { .. }
            | RegionNode::GenericFor { .. }
            | RegionNode::Break
            | RegionNode::Return { .. } => {}
        }

        self.changed |= changed;
        changed
    }

    fn simplify_sequence_tail(&mut self, nodes: &mut Vec<RegionNode>) -> bool {
        let mut changed = false;

        changed |= remove_empty_nodes(nodes);

        loop {
            let Some(last) = nodes.last_mut() else {
                return changed;
            };

            let tail_changed = self.simplify_loop_tail(last);
            changed |= remove_empty_nodes(nodes);
            changed |= tail_changed;

            if !tail_changed {
                break;
            }
        }

        changed
    }
}

impl VisitorMut for ContinueCleanup {
    fn visit_region(&mut self, region: &mut RegionNode) {
        match region {
            RegionNode::While { condition, body } => {
                self.visit_expr(condition);
                self.simplify_loop_body(body);
            }
            RegionNode::RepeatUntil { body, condition } => {
                self.simplify_loop_body(body);
                self.visit_expr(condition);
            }
            RegionNode::NumericFor {
                var,
                start,
                end,
                step,
                body,
            } => {
                self.visit_symbol(var);
                self.visit_expr(start);
                self.visit_expr(end);
                self.visit_expr(step);
                self.simplify_loop_body(body);
            }
            RegionNode::GenericFor { vars, exprs, body } => {
                self.visit_value_pack(exprs);
                for var in vars {
                    self.visit_symbol(var);
                }
                self.simplify_loop_body(body);
            }
            _ => walk_region_mut(self, region),
        }
    }
}

fn extract_continue_guard(node: &mut RegionNode) -> Option<RegionNode> {
    let RegionNode::If {
        then_branch,
        else_branch: Some(else_branch),
        ..
    } = node
    else {
        return None;
    };

    let then_continues = is_plain_continue(then_branch);
    let else_continues = is_plain_continue(else_branch);
    if then_continues == else_continues {
        return None;
    }

    let original = std::mem::replace(node, RegionNode::empty());
    let RegionNode::If {
        condition,
        then_branch,
        else_branch: Some(else_branch),
    } = original
    else {
        unreachable!("candidate was checked before moving the node");
    };

    let (guard_condition, fallthrough) = match (then_continues, else_continues) {
        (true, false) => (condition, *else_branch),
        (false, true) => (condition.invert(), *then_branch),
        _ => unreachable!("candidate must have exactly one continuing branch"),
    };

    *node = RegionNode::If {
        condition: guard_condition,
        then_branch: Box::new(RegionNode::Continue),
        else_branch: None,
    };
    Some(fallthrough)
}

fn is_plain_continue(region: &RegionNode) -> bool {
    match region {
        RegionNode::Continue => true,
        RegionNode::Sequence { nodes } => {
            let mut meaningful = nodes.iter().filter(|node| !node.is_empty());
            meaningful.next().is_some_and(is_plain_continue) && meaningful.next().is_none()
        }
        _ => false,
    }
}

fn remove_empty_nodes(nodes: &mut Vec<RegionNode>) -> bool {
    let len_before = nodes.len();
    nodes.retain(|node| !node.is_empty());
    nodes.len() != len_before
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut cleanup = ContinueCleanup::default();
    cleanup.visit_function(fun);
    cleanup.changed
}
