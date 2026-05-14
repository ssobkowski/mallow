//! Folds if/else branches that assign the same target into a single assignment.
//!
//! Recognizes:
//!
//! ```luau
//! if cond then var = true else var = false end
//! ```
//! and folds it to `var = cond`.
//!
//! The inverse (`then = false`, `else = true`) folds to `var = not cond`.
//!
//! For any other pair of values assigned to the same target in both branches:
//!
//! ```luau
//! if cond then var = a else var = b end
//! ```
//! is folded to `var = if cond then a else b`.

use crate::hil::{
    StructuredFunction,
    cflow::region::RegionNode,
    ir::{HilExpr, HilStmt},
    visitor::{VisitorMut, walk_region_mut},
};

#[derive(Default)]
struct BoolAssignFolding {
    changed: bool,
}

impl VisitorMut for BoolAssignFolding {
    fn visit_region(&mut self, region: &mut RegionNode) {
        walk_region_mut(self, region);

        let fold_result = if let RegionNode::If {
            condition,
            then_branch,
            else_branch: Some(else_branch),
        } = &*region
        {
            extract_matching_assignments(then_branch, else_branch).map(
                |(lhs, then_val, else_val)| {
                    (lhs, fold_to_expr(condition.clone(), then_val, else_val))
                },
            )
        } else {
            None
        };

        if let Some((lhs, new_value)) = fold_result {
            *region = RegionNode::BasicBlock {
                stmts: vec![HilStmt::Assign {
                    left: lhs,
                    value: new_value,
                }],
            };
            self.changed = true;
        }
    }
}

/// Extracts `(lhs, then_value, else_value)` if both branches consist of exactly
/// one assignment to the same lhs expression. Returns `None` otherwise.
fn extract_matching_assignments(
    then_branch: &RegionNode,
    else_branch: &RegionNode,
) -> Option<(HilExpr, HilExpr, HilExpr)> {
    let (then_lhs, then_val) = single_assign(then_branch)?;
    let (else_lhs, else_val) = single_assign(else_branch)?;
    (then_lhs == else_lhs).then_some((then_lhs, then_val, else_val))
}

/// Extracts the single `(lhs, value)` pair from a node that consists of exactly
/// one assignment statement. Transparently unwraps single-element sequences.
fn single_assign(node: &RegionNode) -> Option<(HilExpr, HilExpr)> {
    if let RegionNode::Sequence { nodes } = node
        && let [node] = nodes.as_slice()
    {
        return single_assign(node);
    }

    let RegionNode::BasicBlock { stmts } = node else {
        return None;
    };
    let [HilStmt::Assign { left, value }] = stmts.as_slice() else {
        return None;
    };

    Some((left.clone(), value.clone()))
}

/// Produces the replacement expression for an if/else assignment pair.
fn fold_to_expr(condition: HilExpr, then_val: HilExpr, else_val: HilExpr) -> HilExpr {
    match (&then_val, &else_val) {
        (HilExpr::Bool(true), HilExpr::Bool(false)) => condition,
        (HilExpr::Bool(false), HilExpr::Bool(true)) => HilExpr::not(condition),
        _ => HilExpr::IfElse {
            condition: Box::new(condition),
            then_expr: Box::new(then_val),
            else_expr: Box::new(else_val),
        },
    }
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut folding = BoolAssignFolding::default();
    folding.visit_function(fun);
    folding.changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hil::{
        cflow::region::RegionNode,
        ir::{HilExpr, HilStmt},
        lifter::ssa::Symbol,
    };
    use id_arena::Arena;

    fn assign(lhs: HilExpr, value: HilExpr) -> RegionNode {
        RegionNode::BasicBlock {
            stmts: vec![HilStmt::Assign { left: lhs, value }],
        }
    }

    fn if_else(condition: HilExpr, then_branch: RegionNode, else_branch: RegionNode) -> RegionNode {
        RegionNode::If {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: Some(Box::new(else_branch)),
        }
    }

    fn folded_value(node: &RegionNode) -> &HilExpr {
        let RegionNode::BasicBlock { stmts } = node else {
            panic!("expected a basic block after folding");
        };
        let [HilStmt::Assign { value, .. }] = stmts.as_slice() else {
            panic!("expected a single assignment after folding");
        };
        value
    }

    #[test]
    fn folds_true_false_to_condition() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let cond = HilExpr::Symbol(symbols.alloc(Symbol::reg(1)));

        let mut region = if_else(
            cond.clone(),
            assign(HilExpr::Symbol(target), HilExpr::Bool(true)),
            assign(HilExpr::Symbol(target), HilExpr::Bool(false)),
        );

        let changed = run_on_region(&mut region);
        assert!(changed);
        assert_eq!(folded_value(&region), &cond);
    }

    #[test]
    fn folds_false_true_to_inverted_condition() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let cond = HilExpr::Symbol(symbols.alloc(Symbol::reg(1)));

        let mut region = if_else(
            cond.clone(),
            assign(HilExpr::Symbol(target), HilExpr::Bool(false)),
            assign(HilExpr::Symbol(target), HilExpr::Bool(true)),
        );

        let changed = run_on_region(&mut region);
        assert!(changed);
        assert_eq!(folded_value(&region), &cond.clone().invert());
    }

    #[test]
    fn folds_false_true_with_lt_condition_uses_not_not_invert() {
        // not (a < b) is not equivalent to a >= b when NaN is
        // involved. The fold must produce `not (a < b)`, not `a >= b`.
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let a = HilExpr::Symbol(symbols.alloc(Symbol::reg(1)));
        let b = HilExpr::Symbol(symbols.alloc(Symbol::reg(2)));

        let cond = HilExpr::Binary {
            lhs: Box::new(a),
            op: crate::ast::BinOp::Lt,
            rhs: Box::new(b),
        };

        let mut region = if_else(
            cond.clone(),
            assign(HilExpr::Symbol(target), HilExpr::Bool(false)),
            assign(HilExpr::Symbol(target), HilExpr::Bool(true)),
        );

        let changed = run_on_region(&mut region);
        assert!(changed);
        assert_eq!(
            folded_value(&region),
            &HilExpr::Unary {
                op: crate::ast::UnOp::Not,
                expr: Box::new(cond),
            }
        );
    }

    #[test]
    fn folds_general_values_to_if_expression() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let cond = HilExpr::Symbol(symbols.alloc(Symbol::reg(1)));
        let a = HilExpr::Symbol(symbols.alloc(Symbol::reg(2)));
        let b = HilExpr::Symbol(symbols.alloc(Symbol::reg(3)));

        let mut region = if_else(
            cond.clone(),
            assign(HilExpr::Symbol(target), a.clone()),
            assign(HilExpr::Symbol(target), b.clone()),
        );

        let changed = run_on_region(&mut region);
        assert!(changed);
        assert_eq!(
            folded_value(&region),
            &HilExpr::IfElse {
                condition: Box::new(cond),
                then_expr: Box::new(a),
                else_expr: Box::new(b),
            }
        );
    }

    #[test]
    fn does_not_fold_mismatched_lhs() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let a = symbols.alloc(Symbol::reg(0));
        let b = symbols.alloc(Symbol::reg(1));
        let cond = HilExpr::Symbol(symbols.alloc(Symbol::reg(2)));

        let mut region = if_else(
            cond,
            assign(HilExpr::Symbol(a), HilExpr::Bool(true)),
            assign(HilExpr::Symbol(b), HilExpr::Bool(false)),
        );

        let changed = run_on_region(&mut region);
        assert!(!changed);
        assert!(matches!(region, RegionNode::If { .. }));
    }

    #[test]
    fn does_not_fold_without_else_branch() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let cond = HilExpr::Symbol(symbols.alloc(Symbol::reg(1)));

        let mut region = RegionNode::If {
            condition: cond,
            then_branch: Box::new(assign(HilExpr::Symbol(target), HilExpr::Bool(true))),
            else_branch: None,
        };

        let changed = run_on_region(&mut region);
        assert!(!changed);
        assert!(matches!(region, RegionNode::If { .. }));
    }

    #[test]
    fn does_not_fold_multi_statement_branch() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let other = symbols.alloc(Symbol::reg(1));
        let cond = HilExpr::Symbol(symbols.alloc(Symbol::reg(2)));

        let then_branch = RegionNode::BasicBlock {
            stmts: vec![
                HilStmt::Assign {
                    left: HilExpr::Symbol(target),
                    value: HilExpr::Bool(true),
                },
                HilStmt::Assign {
                    left: HilExpr::Symbol(other),
                    value: HilExpr::Bool(true),
                },
            ],
        };

        let mut region = RegionNode::If {
            condition: cond,
            then_branch: Box::new(then_branch),
            else_branch: Some(Box::new(assign(
                HilExpr::Symbol(target),
                HilExpr::Bool(false),
            ))),
        };

        let changed = run_on_region(&mut region);
        assert!(!changed);
        assert!(matches!(region, RegionNode::If { .. }));
    }

    /// Helper: runs the pass against a single `RegionNode` wrapped in a dummy function.
    fn run_on_region(region: &mut RegionNode) -> bool {
        let mut folding = BoolAssignFolding::default();
        folding.visit_region(region);
        folding.changed
    }
}
