//! Folds short-circuit assignment guards into logical expressions.
//!
//! This recognizes `v = a; if not v then v = b end` as `v = a or b` and
//! `v = a; if v then v = b end` as `v = a and b`.
//!
//! This is an optimization pass that eliminates simple conditional fallback patterns
//! by replacing them with a logical expression. It is not a normalization pass
//! because it changes the structure of the IR rather than canonicalizing it.

use crate::{
    hil::{
        StructuredFunction,
        cflow::region::RegionNode,
        ir::{Expr, Stmt},
        lifter::ssa::SymbolId,
        visitor::{VisitorMut, walk_region_mut},
    },
    operator::BinOp,
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
        let Some((op, fallback)) = guarded_fallback_assignment(&nodes[index + 1], sym) else {
            index += 1;
            continue;
        };

        if !fallback.is_pure() || fallback.reads_symbol(&sym) {
            index += 1;
            continue;
        }

        let folded = match op {
            BinOp::And => Expr::and(value, fallback),
            BinOp::Or => Expr::or(value, fallback),
            _ => unreachable!("short-circuit assignment only folds logical operators"),
        };
        replace_trailing_assignment_value(&mut nodes[index], folded);
        nodes.remove(index + 1);
        changed = true;
    }

    changed
}

fn trailing_symbol_assignment(node: &RegionNode) -> Option<(SymbolId, Expr)> {
    if let RegionNode::Sequence { nodes } = node
        && let [node] = nodes.as_slice()
    {
        return trailing_symbol_assignment(node);
    }

    let RegionNode::BasicBlock { stmts } = node else {
        return None;
    };
    let Stmt::Assign { left, value } = stmts.last()? else {
        return None;
    };
    let Expr::Symbol(sym) = left else {
        return None;
    };

    Some((*sym, value.clone()))
}

fn replace_trailing_assignment_value(node: &mut RegionNode, value: Expr) {
    if let RegionNode::Sequence { nodes } = node
        && let [node] = nodes.as_mut_slice()
    {
        replace_trailing_assignment_value(node, value);
        return;
    }

    let RegionNode::BasicBlock { stmts } = node else {
        unreachable!("caller checked that this node has a trailing assignment");
    };
    let Some(Stmt::Assign {
        value: old_value, ..
    }) = stmts.last_mut()
    else {
        unreachable!("caller checked that this node has a trailing assignment");
    };
    *old_value = value;
}

fn guarded_fallback_assignment(node: &RegionNode, sym: SymbolId) -> Option<(BinOp, Expr)> {
    let RegionNode::If {
        condition,
        then_branch,
        else_branch: None,
    } = node
    else {
        return None;
    };

    let op = if condition == &Expr::Symbol(sym).invert() {
        BinOp::Or
    } else if condition == &Expr::Symbol(sym) {
        BinOp::And
    } else {
        return None;
    };

    single_symbol_assignment(then_branch, sym).map(|value| (op, value))
}

fn single_symbol_assignment(node: &RegionNode, sym: SymbolId) -> Option<Expr> {
    if let RegionNode::Sequence { nodes } = node
        && let [node] = nodes.as_slice()
    {
        return single_symbol_assignment(node, sym);
    }

    let RegionNode::BasicBlock { stmts } = node else {
        return None;
    };
    let [Stmt::Assign { left, value }] = stmts.as_slice() else {
        return None;
    };
    (left == &Expr::Symbol(sym)).then(|| value.clone())
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut folding = ShortCircuitFolding::default();
    folding.visit_function(fun);
    folding.changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hil::lifter::ssa::Symbol;

    use id_arena::Arena;

    fn assign(sym: SymbolId, value: Expr) -> RegionNode {
        RegionNode::BasicBlock {
            stmts: vec![Stmt::Assign {
                left: Expr::Symbol(sym),
                value,
            }],
        }
    }

    fn guard(condition: Expr, sym: SymbolId, value: Expr) -> RegionNode {
        RegionNode::If {
            condition,
            then_branch: Box::new(assign(sym, value)),
            else_branch: None,
        }
    }

    fn folded_assignment_value(nodes: &[RegionNode]) -> &Expr {
        let [RegionNode::BasicBlock { stmts }] = nodes else {
            panic!("expected one folded basic block");
        };
        let [Stmt::Assign { value, .. }] = stmts.as_slice() else {
            panic!("expected one folded assignment");
        };
        value
    }

    #[test]
    fn folds_or_assignment_guard() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let lhs = Expr::Symbol(symbols.alloc(Symbol::reg(1)));
        let rhs = Expr::Symbol(symbols.alloc(Symbol::reg(2)));
        let mut nodes = vec![
            assign(target, lhs.clone()),
            guard(Expr::Symbol(target).invert(), target, rhs.clone()),
        ];

        assert!(fold_short_circuit_assignments(&mut nodes));
        assert_eq!(nodes.len(), 1);
        assert_eq!(folded_assignment_value(&nodes), &Expr::or(lhs, rhs));
    }

    #[test]
    fn folds_and_assignment_guard() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let lhs = Expr::Symbol(symbols.alloc(Symbol::reg(1)));
        let rhs = Expr::Symbol(symbols.alloc(Symbol::reg(2)));
        let mut nodes = vec![
            assign(target, lhs.clone()),
            guard(Expr::Symbol(target), target, rhs.clone()),
        ];

        assert!(fold_short_circuit_assignments(&mut nodes));
        assert_eq!(nodes.len(), 1);
        assert_eq!(folded_assignment_value(&nodes), &Expr::and(lhs, rhs));
    }
}
