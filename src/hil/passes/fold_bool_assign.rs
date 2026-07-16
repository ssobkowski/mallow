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
    ir::{Expr, Stmt},
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
                stmts: vec![Stmt::Assign {
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
) -> Option<(Expr, Expr, Expr)> {
    let (then_lhs, then_val) = single_assign(then_branch)?;
    let (else_lhs, else_val) = single_assign(else_branch)?;
    (then_lhs == else_lhs).then_some((then_lhs, then_val, else_val))
}

/// Extracts the single `(lhs, value)` pair from a node that consists of exactly
/// one assignment statement. Transparently unwraps single-element sequences.
fn single_assign(node: &RegionNode) -> Option<(Expr, Expr)> {
    if let RegionNode::Sequence { nodes } = node
        && let [node] = nodes.as_slice()
    {
        return single_assign(node);
    }

    let RegionNode::BasicBlock { stmts } = node else {
        return None;
    };
    let [Stmt::Assign { left, value }] = stmts.as_slice() else {
        return None;
    };

    Some((left.clone(), value.clone()))
}

/// Produces the replacement expression for an if/else assignment pair.
fn fold_to_expr(condition: Expr, then_val: Expr, else_val: Expr) -> Expr {
    match (&then_val, &else_val) {
        (Expr::Bool(true), Expr::Bool(false)) => condition,
        (Expr::Bool(false), Expr::Bool(true)) => Expr::not(condition),
        _ => Expr::IfElse {
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
        ir::{Expr, Stmt},
        lifter::ssa::Symbol,
    };
    use id_arena::Arena;

    fn assign(lhs: Expr, value: Expr) -> RegionNode {
        RegionNode::BasicBlock {
            stmts: vec![Stmt::Assign { left: lhs, value }],
        }
    }

    fn if_else(condition: Expr, then_branch: RegionNode, else_branch: RegionNode) -> RegionNode {
        RegionNode::If {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: Some(Box::new(else_branch)),
        }
    }

    fn folded_value(node: &RegionNode) -> &Expr {
        let RegionNode::BasicBlock { stmts } = node else {
            panic!("expected a basic block after folding");
        };
        let [Stmt::Assign { value, .. }] = stmts.as_slice() else {
            panic!("expected a single assignment after folding");
        };
        value
    }

    #[test]
    fn folds_true_false_to_condition() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let cond = Expr::Symbol(symbols.alloc(Symbol::reg(1)));

        let mut region = if_else(
            cond.clone(),
            assign(Expr::Symbol(target), Expr::Bool(true)),
            assign(Expr::Symbol(target), Expr::Bool(false)),
        );

        let changed = run_on_region(&mut region);
        assert!(changed);
        assert_eq!(folded_value(&region), &cond);
    }

    #[test]
    fn folds_false_true_to_inverted_condition() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let cond = Expr::Symbol(symbols.alloc(Symbol::reg(1)));

        let mut region = if_else(
            cond.clone(),
            assign(Expr::Symbol(target), Expr::Bool(false)),
            assign(Expr::Symbol(target), Expr::Bool(true)),
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
        let a = Expr::Symbol(symbols.alloc(Symbol::reg(1)));
        let b = Expr::Symbol(symbols.alloc(Symbol::reg(2)));

        let cond = Expr::Binary {
            lhs: Box::new(a),
            op: crate::operator::BinOp::Lt,
            rhs: Box::new(b),
        };

        let mut region = if_else(
            cond.clone(),
            assign(Expr::Symbol(target), Expr::Bool(false)),
            assign(Expr::Symbol(target), Expr::Bool(true)),
        );

        let changed = run_on_region(&mut region);
        assert!(changed);
        assert_eq!(
            folded_value(&region),
            &Expr::Unary {
                op: crate::operator::UnOp::Not,
                expr: Box::new(cond),
            }
        );
    }

    #[test]
    fn folds_general_values_to_if_expression() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let cond = Expr::Symbol(symbols.alloc(Symbol::reg(1)));
        let a = Expr::Symbol(symbols.alloc(Symbol::reg(2)));
        let b = Expr::Symbol(symbols.alloc(Symbol::reg(3)));

        let mut region = if_else(
            cond.clone(),
            assign(Expr::Symbol(target), a.clone()),
            assign(Expr::Symbol(target), b.clone()),
        );

        let changed = run_on_region(&mut region);
        assert!(changed);
        assert_eq!(
            folded_value(&region),
            &Expr::IfElse {
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
        let cond = Expr::Symbol(symbols.alloc(Symbol::reg(2)));

        let mut region = if_else(
            cond,
            assign(Expr::Symbol(a), Expr::Bool(true)),
            assign(Expr::Symbol(b), Expr::Bool(false)),
        );

        let changed = run_on_region(&mut region);
        assert!(!changed);
        assert!(matches!(region, RegionNode::If { .. }));
    }

    #[test]
    fn does_not_fold_without_else_branch() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let cond = Expr::Symbol(symbols.alloc(Symbol::reg(1)));

        let mut region = RegionNode::If {
            condition: cond,
            then_branch: Box::new(assign(Expr::Symbol(target), Expr::Bool(true))),
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
        let cond = Expr::Symbol(symbols.alloc(Symbol::reg(2)));

        let then_branch = RegionNode::BasicBlock {
            stmts: vec![
                Stmt::Assign {
                    left: Expr::Symbol(target),
                    value: Expr::Bool(true),
                },
                Stmt::Assign {
                    left: Expr::Symbol(other),
                    value: Expr::Bool(true),
                },
            ],
        };

        let mut region = RegionNode::If {
            condition: cond,
            then_branch: Box::new(then_branch),
            else_branch: Some(Box::new(assign(Expr::Symbol(target), Expr::Bool(false)))),
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
