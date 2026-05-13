//! Normalizes If-Else conditionals where the *then block* is empty and *else block* is not
//! by swapping the *then* and *else* branches and inverting the condition.

use crate::hil::{
    StructuredFunction,
    cflow::region::RegionNode,
    visitor::{VisitorMut, walk_region_mut},
};

#[derive(Default)]
struct IfNormalizer {
    changed: bool,
}

impl VisitorMut for IfNormalizer {
    fn visit_region(&mut self, region: &mut RegionNode) {
        if let RegionNode::If {
            condition,
            then_branch,
            else_branch,
        } = region
            && then_branch.is_empty()
            && else_branch.as_ref().is_some_and(|b| !b.is_empty())
        {
            *then_branch = else_branch.take().expect("checked above");
            *condition = condition.clone().invert();
            self.changed = true;
        }

        walk_region_mut(self, region);
    }
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut changed = false;
    loop {
        let mut rewriter = IfNormalizer::default();
        rewriter.visit_function(fun);

        if !rewriter.changed {
            break;
        }

        changed = true;
    }
    changed
}
