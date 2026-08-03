use crate::hil::{
    ir::{Expr, Stmt, TableItem, ValuePack},
    lifter::ssa::SymbolId,
};

use super::common::count_symbol_reads_in_expr;

/// Returns whether a statement can receive the replacement safely.
pub(super) fn can_substitute_in_stmt(stmt: &Stmt, sym: SymbolId, rhs: &Expr) -> bool {
    rhs.is_pure() || matches!(rhs, Expr::Symbol(_)) || is_call_consumer(stmt, sym, rhs)
}

/// Returns whether an expression can receive the replacement safely.
pub(super) fn can_substitute_in_expr(expr: &Expr, sym: SymbolId, rhs: &Expr) -> bool {
    rhs.is_pure()
        || matches!(rhs, Expr::Symbol(_))
        || can_inline_effectful_at_occurrence(expr, sym, rhs)
}

/// Returns whether an adjacent assignment evaluates the replacement in place.
pub(super) fn is_adjacent_assignment_consumer(
    stmt: &Stmt,
    sym: SymbolId,
    rhs: &Expr,
    source_idx: usize,
    use_idx: usize,
) -> bool {
    if use_idx != source_idx + 1 {
        return false;
    }

    match stmt {
        Stmt::Assign { left, value } => {
            if left.reads_symbol(&sym) {
                // A closure only allocates its value. Moving it into an
                // adjacent key keeps the assignment's reads and calls intact.
                matches!(rhs, Expr::Closure { .. })
                    && value.is_pure()
                    && can_inline_effectful_at_occurrence(left, sym, rhs)
            } else {
                left.is_pure() && can_inline_effectful_at_occurrence(value, sym, rhs)
            }
        }
        Stmt::SetList { table, values, .. } => {
            *table != sym
                && value_pack_occurrence_has_no_prior_effect(values, sym)
                && !values.tail().is_some_and(|tail| {
                    tail.reads_symbol(&sym) && rhs.can_produce_multiple_values()
                })
        }
        _ => false,
    }
}

/// Returns whether a call statement evaluates the replacement in place.
fn is_call_consumer(stmt: &Stmt, sym: SymbolId, rhs: &Expr) -> bool {
    matches!(stmt, Stmt::Call(expr) if can_substitute_in_expr(expr, sym, rhs))
}

/// Returns whether one effectful replacement preserves expression evaluation order.
fn can_inline_effectful_at_occurrence(expr: &Expr, sym: SymbolId, rhs: &Expr) -> bool {
    count_symbol_reads_in_expr(expr, sym) == 1
        && occurrence_has_no_prior_effect(expr, sym)
        && !occurrence_is_final_multiret_position(expr, sym, rhs)
}

/// Returns whether the symbol occurs before every effect in an expression.
fn occurrence_has_no_prior_effect(expr: &Expr, sym: SymbolId) -> bool {
    match expr {
        Expr::Symbol(target) => *target == sym,
        Expr::GetField { obj, .. } => occurrence_has_no_prior_effect(obj, sym),
        Expr::GetIndex { obj, index } => {
            if obj.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(obj, sym)
            } else {
                obj.is_pure() && occurrence_has_no_prior_effect(index, sym)
            }
        }
        Expr::Call { fun, args } => {
            if fun.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(fun, sym)
            } else if !fun.is_pure() {
                false
            } else {
                value_pack_occurrence_has_no_prior_effect(args, sym)
            }
        }
        Expr::MethodCall { object, args, .. } => {
            if object.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(object, sym)
            } else if !object.is_pure() {
                false
            } else {
                value_pack_occurrence_has_no_prior_effect(args, sym)
            }
        }
        Expr::Binary { lhs, rhs, .. } => {
            if lhs.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(lhs, sym)
            } else {
                lhs.is_pure() && occurrence_has_no_prior_effect(rhs, sym)
            }
        }
        Expr::Unary { expr, .. } => occurrence_has_no_prior_effect(expr, sym),
        Expr::IfElse {
            condition,
            then_expr,
            else_expr,
        } => {
            if condition.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(condition, sym)
            } else if !condition.is_pure() {
                false
            } else if then_expr.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(then_expr, sym)
            } else {
                occurrence_has_no_prior_effect(else_expr, sym)
            }
        }
        Expr::Table { items } => {
            let Some(idx) = items.iter().position(|item| match item {
                TableItem::List(values) => values.iter().any(|value| value.reads_symbol(&sym)),
                TableItem::Index(key, value) => key.reads_symbol(&sym) || value.reads_symbol(&sym),
            }) else {
                return false;
            };

            items[..idx].iter().all(|item| match item {
                TableItem::List(values) => values.iter().all(Expr::is_pure),
                TableItem::Index(key, value) => key.is_pure() && value.is_pure(),
            }) && match &items[idx] {
                TableItem::List(values) => value_pack_occurrence_has_no_prior_effect(values, sym),
                TableItem::Index(key, value) => {
                    if key.reads_symbol(&sym) {
                        occurrence_has_no_prior_effect(key, sym)
                    } else {
                        key.is_pure() && occurrence_has_no_prior_effect(value, sym)
                    }
                }
            }
        }
        Expr::Nil
        | Expr::Number(_)
        | Expr::String(_)
        | Expr::Bool(_)
        | Expr::Closure { .. }
        | Expr::Global(_)
        | Expr::VarArgs => false,
    }
}

/// Returns whether replacement would expose a final multi-return expression.
fn occurrence_is_final_multiret_position(expr: &Expr, sym: SymbolId, rhs: &Expr) -> bool {
    if !matches!(
        rhs,
        Expr::Call { .. } | Expr::MethodCall { .. } | Expr::VarArgs
    ) {
        return false;
    }

    match expr {
        Expr::Call { fun, args } => {
            if fun.reads_symbol(&sym) {
                return false;
            }
            args.tail().is_some_and(|arg| arg.reads_symbol(&sym))
        }
        Expr::MethodCall { object, args, .. } => {
            if object.reads_symbol(&sym) {
                return false;
            }
            args.tail().is_some_and(|arg| arg.reads_symbol(&sym))
        }
        _ => false,
    }
}

/// Returns whether a symbol in a value pack precedes every effectful expression.
fn value_pack_occurrence_has_no_prior_effect(values: &ValuePack, sym: SymbolId) -> bool {
    let mut prior_expressions_are_pure = true;
    for value in values.iter() {
        if value.reads_symbol(&sym) {
            return prior_expressions_are_pure && occurrence_has_no_prior_effect(value, sym);
        }
        prior_expressions_are_pure &= value.is_pure();
    }
    false
}
