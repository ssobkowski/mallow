//! Flattens `if`/`else` branches when one side always exits the current flow.
//!
//! The pass rewrites shapes such as `if cond then break else body end` into
//! `if cond then break end; body`. This keeps condition evaluation intact while
//! removing indentation that only exists because region recovery preserved the
//! original CFG split.

use crate::hil::StructuredFunction;
use crate::hil::cflow::region::RegionNode;
use crate::hil::visitor::{VisitorMut, walk_region_mut};

#[derive(Default)]
struct TerminatorCleanup {
    changed: bool,
}

impl VisitorMut for TerminatorCleanup {
    fn visit_region(&mut self, region: &mut RegionNode) {
        walk_region_mut(self, region);

        if let RegionNode::Sequence { nodes } = region {
            self.changed |= flatten_terminating_branches(nodes);
        }
    }
}

fn flatten_terminating_branches(nodes: &mut Vec<RegionNode>) -> bool {
    let mut changed = false;
    let mut index = 0;

    while index < nodes.len() {
        let Some(fallthrough) = extract_terminating_guard(&mut nodes[index]) else {
            index += 1;
            continue;
        };

        if !fallthrough.is_empty() {
            nodes.insert(index + 1, fallthrough);
        }

        changed = true;
        index += 1;
    }

    changed
}

fn extract_terminating_guard(node: &mut RegionNode) -> Option<RegionNode> {
    let RegionNode::If {
        then_branch,
        else_branch: Some(else_branch),
        ..
    } = node
    else {
        return None;
    };

    let then_terminates = always_exits_current_flow(then_branch);
    let else_terminates = always_exits_current_flow(else_branch);
    if then_terminates == else_terminates {
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

    let (guard_condition, terminator, fallthrough) = match (then_terminates, else_terminates) {
        (true, false) => (condition, then_branch, else_branch),
        (false, true) => (condition.invert(), else_branch, then_branch),
        _ => unreachable!("candidate must have exactly one terminating branch"),
    };

    *node = RegionNode::If {
        condition: guard_condition,
        then_branch: terminator,
        else_branch: None,
    };
    Some(*fallthrough)
}

fn always_exits_current_flow(region: &RegionNode) -> bool {
    match region {
        RegionNode::Continue | RegionNode::Break | RegionNode::Return { .. } => true,
        RegionNode::Sequence { nodes } => nodes
            .iter()
            .rev()
            .find(|node| !node.is_empty())
            .is_some_and(always_exits_current_flow),
        RegionNode::If {
            then_branch,
            else_branch: Some(else_branch),
            ..
        } => always_exits_current_flow(then_branch) && always_exits_current_flow(else_branch),
        RegionNode::BasicBlock { .. }
        | RegionNode::If {
            else_branch: None, ..
        }
        | RegionNode::While { .. }
        | RegionNode::RepeatUntil { .. }
        | RegionNode::NumericFor { .. }
        | RegionNode::GenericFor { .. } => false,
    }
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut cleanup = TerminatorCleanup::default();
    cleanup.visit_function(fun);
    cleanup.changed
}
