//! Folds short-circuit assignment guards of the form `v = a; if not v then v = b end` into `v = a or b`.
//!
//! This is an optimization pass that eliminates simple conditional fallback patterns
//! by replacing them with a logical `or` expression. It is not a normalization pass
//! because it changes the structure of the IR rather than canonicalizing it.

use crate::hil::{
    StructuredFunction,
    cflow::region::RegionNode,
    ir::{HilExpr, HilStmt},
    lifter::ssa::SymbolId,
    visitor::{VisitorMut, walk_region_mut},
};

#[derive(Default)]
struct ShortCircuitFolding {
    changed: bool,
}

impl VisitorMut for ShortCircuitFolding {
    fn visit_region(&mut self, region: &mut RegionNode) {
        walk_region_mut(self, region);

        if let RegionNode::Sequence { nodes } = region {
            self.changed |= fold_short_circuit_assignments(nodes);
        }
    }
}

fn fold_short_circuit_assignments(nodes: &mut Vec<RegionNode>) -> bool {
    let mut changed = false;
    let mut index = 0;

    while index + 1 < nodes.len() {
        let Some((sym, value)) = trailing_symbol_assignment(&nodes[index]) else {
            index += 1;
            continue;
        };
        let Some(fallback) = guarded_fallback_assignment(&nodes[index + 1], sym) else {
            index += 1;
            continue;
        };

        if !fallback.is_pure() || fallback.reads_symbol(&sym) {
            index += 1;
            continue;
        }

        replace_trailing_assignment_value(&mut nodes[index], HilExpr::or(value, fallback));
        nodes.remove(index + 1);
        changed = true;
    }

    changed
}

fn trailing_symbol_assignment(node: &RegionNode) -> Option<(SymbolId, HilExpr)> {
    if let RegionNode::Sequence { nodes } = node
        && let [node] = nodes.as_slice()
    {
        return trailing_symbol_assignment(node);
    }

    let RegionNode::BasicBlock { stmts } = node else {
        return None;
    };
    let HilStmt::Assign { left, value } = stmts.last()? else {
        return None;
    };
    let HilExpr::Symbol(sym) = left else {
        return None;
    };

    Some((*sym, value.clone()))
}

fn replace_trailing_assignment_value(node: &mut RegionNode, value: HilExpr) {
    if let RegionNode::Sequence { nodes } = node
        && let [node] = nodes.as_mut_slice()
    {
        replace_trailing_assignment_value(node, value);
        return;
    }

    let RegionNode::BasicBlock { stmts } = node else {
        unreachable!("caller checked that this node has a trailing assignment");
    };
    let Some(HilStmt::Assign {
        value: old_value, ..
    }) = stmts.last_mut()
    else {
        unreachable!("caller checked that this node has a trailing assignment");
    };
    *old_value = value;
}

fn guarded_fallback_assignment(node: &RegionNode, sym: SymbolId) -> Option<HilExpr> {
    let RegionNode::If {
        condition,
        then_branch,
        else_branch: None,
    } = node
    else {
        return None;
    };

    (condition == &HilExpr::Symbol(sym).invert())
        .then(|| single_symbol_assignment(then_branch, sym))?
}

fn single_symbol_assignment(node: &RegionNode, sym: SymbolId) -> Option<HilExpr> {
    if let RegionNode::Sequence { nodes } = node
        && let [node] = nodes.as_slice()
    {
        return single_symbol_assignment(node, sym);
    }

    let RegionNode::BasicBlock { stmts } = node else {
        return None;
    };
    let [HilStmt::Assign { left, value }] = stmts.as_slice() else {
        return None;
    };
    (left == &HilExpr::Symbol(sym)).then(|| value.clone())
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut folding = ShortCircuitFolding::default();
    folding.visit_function(fun);
    folding.changed
}
