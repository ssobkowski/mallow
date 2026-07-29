//! Folds nested guard-only `if` statements into short-circuit conditions.
//!
//! This recognizes `if a then if b then body end end` and rewrites it to
//! `if a and b then body end`.

// TODO: Support `elseif`-shaped folds once `RegionNode` can represent them directly.

use crate::hil::{
    StructuredFunction,
    cflow::region::RegionNode,
    ir::Expr,
    visitor::{VisitorMut, walk_region_mut},
};

#[derive(Default)]
struct NestedIfFolding {
    changed: bool,
}

impl VisitorMut for NestedIfFolding {
    fn visit_region(&mut self, region: &mut RegionNode) {
        walk_region_mut(self, region);

        if fold_nested_if(region) {
            self.changed = true;
        }
    }
}

fn fold_nested_if(region: &mut RegionNode) -> bool {
    let RegionNode::If {
        condition,
        then_branch,
        else_branch: None,
    } = region
    else {
        return false;
    };

    let Some(inner) = single_non_empty_node_mut(then_branch) else {
        return false;
    };
    let RegionNode::If {
        condition: inner_condition,
        then_branch: inner_then,
        else_branch: None,
    } = inner
    else {
        return false;
    };

    *condition = Expr::and(condition.clone(), inner_condition.clone());
    *then_branch = std::mem::replace(inner_then, Box::new(RegionNode::empty()));
    true
}

fn single_non_empty_node_mut(node: &mut RegionNode) -> Option<&mut RegionNode> {
    if !matches!(node, RegionNode::Sequence { .. }) {
        return (!node.is_empty()).then_some(node);
    }

    let RegionNode::Sequence { nodes } = node else {
        unreachable!("checked above");
    };

    let mut non_empty = nodes.iter_mut().filter(|node| !node.is_empty());
    let node = non_empty.next()?;
    non_empty.next().is_none().then_some(node)
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut folding = NestedIfFolding::default();
    folding.visit_function(fun);
    folding.changed
}
