//! Concrete NIR inlining with evaluation-order checks.

use std::collections::HashMap;

use super::*;

/// Inlines adjacent definitions into control consumers until stable.
pub(super) fn inline_control_values(region: &mut Region) {
    loop {
        let counts = UseCounts::collect(region);
        if !inline_region_once(region, &counts) {
            break;
        }
    }
}

/// Number of reads of every NIR value and pack local.
#[derive(Default)]
struct UseCounts {
    /// Reads of source-representable locals.
    locals: HashMap<LocalId, usize>,
    /// Reads of first-class pack locals.
    packs: HashMap<PackLocalId, usize>,
}

impl UseCounts {
    /// Collects all reads in one region tree.
    fn collect(region: &Region) -> Self {
        let mut counts = Self::default();
        counts.region(region);
        counts
    }

    /// Records reads in one expression.
    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Local(local) => *self.locals.entry(*local).or_default() += 1,
            ExprKind::Closure { captures, .. } => {
                for capture in captures {
                    if let Capture::Copy(local) = capture {
                        *self.locals.entry(*local).or_default() += 1;
                    }
                }
            }
            ExprKind::GetTable { table, key } => {
                self.expr(table);
                self.expr(key);
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                self.expr(lhs);
                self.expr(rhs);
            }
            ExprKind::Unary { value, .. } => self.expr(value),
            ExprKind::Concat(values) => {
                for value in values {
                    self.expr(value);
                }
            }
            ExprKind::Select {
                condition,
                then_value,
                else_value,
            } => {
                self.expr(condition);
                self.expr(then_value);
                self.expr(else_value);
            }
            ExprKind::Project { pack, .. } => self.pack_expr(pack),
            ExprKind::Constant(_)
            | ExprKind::GetGlobal(_)
            | ExprKind::NewTable
            | ExprKind::LoadCell(_) => {}
        }
    }

    /// Records reads in one pack expression.
    fn pack_expr(&mut self, pack: &PackExpr) {
        match &pack.kind {
            PackExprKind::Local(local) => *self.packs.entry(*local).or_default() += 1,
            PackExprKind::Values { head, tail } => {
                for value in head {
                    self.expr(value);
                }
                if let Some(tail) = tail {
                    self.pack_expr(tail);
                }
            }
            PackExprKind::Call { function, args } => {
                self.expr(function);
                self.pack_expr(args);
            }
            PackExprKind::MethodCall { object, args, .. } => {
                self.expr(object);
                self.pack_expr(args);
            }
            PackExprKind::VarArgs => {}
        }
    }

    /// Records reads in one writable place.
    fn place(&mut self, place: &Place) {
        match place {
            Place::Local(_) => {}
            Place::Table { table, key } => {
                self.expr(table);
                self.expr(key);
            }
            Place::Cell(_) | Place::Global(_) => {}
        }
    }

    /// Records reads in one statement.
    fn stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { value, .. } => self.expr(value),
            Stmt::LetPack { value, .. } => self.pack_expr(value),
            Stmt::Assign { target, value, .. } => {
                self.place(target);
                self.expr(value);
            }
            Stmt::OpenCell { value, .. } => self.expr(value),
            Stmt::SetList { table, values, .. } => {
                self.expr(table);
                self.pack_expr(values);
            }
        }
    }

    /// Records reads in one control region.
    fn region(&mut self, region: &Region) {
        match region {
            Region::Block { stmts, .. } => {
                for stmt in stmts {
                    self.stmt(stmt);
                }
            }
            Region::Sequence(nodes) => {
                for node in nodes {
                    self.region(node);
                }
            }
            Region::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition);
                self.region(then_branch);
                if let Some(else_branch) = else_branch {
                    self.region(else_branch);
                }
            }
            Region::While { condition, body } | Region::RepeatUntil { condition, body } => {
                self.expr(condition);
                self.region(body);
            }
            Region::NumericFor {
                start,
                end,
                step,
                body,
                ..
            } => {
                self.expr(start);
                self.expr(end);
                self.expr(step);
                self.region(body);
            }
            Region::GenericFor { values, body, .. } => {
                for value in values {
                    self.expr(value);
                }
                self.region(body);
            }
            Region::Return(values) => self.pack_expr(values),
            Region::Continue | Region::Break => {}
        }
    }
}

/// Performs one concrete inlining rewrite.
fn inline_region_once(region: &mut Region, counts: &UseCounts) -> bool {
    match region {
        Region::Block { .. } | Region::Continue | Region::Break | Region::Return(_) => false,
        Region::Sequence(nodes) => {
            for node in nodes.iter_mut() {
                if inline_region_once(node, counts) {
                    return true;
                }
            }

            for index in 0..nodes.len().saturating_sub(1) {
                let (left, right) = nodes.split_at_mut(index + 1);
                if inline_edge_once(&mut left[index], &mut right[0], counts) {
                    return true;
                }
            }
            false
        }
        Region::If {
            then_branch,
            else_branch,
            ..
        } => {
            inline_region_once(then_branch, counts)
                || else_branch
                    .as_deref_mut()
                    .is_some_and(|branch| inline_region_once(branch, counts))
        }
        Region::While { body, .. }
        | Region::NumericFor { body, .. }
        | Region::GenericFor { body, .. } => inline_region_once(body, counts),
        Region::RepeatUntil { condition, body } => {
            if inline_region_once(body, counts) {
                return true;
            }
            inline_tail_into_expr_once(body, condition, counts)
        }
    }
}

/// Inlines the trailing definition of one block into the next region.
fn inline_edge_once(source: &mut Region, target: &mut Region, counts: &UseCounts) -> bool {
    let Region::Block { stmts, .. } = source else {
        return false;
    };
    inline_stmts_into_region_once(stmts, target, counts)
}

/// Inlines one trailing statement into a control region.
fn inline_stmts_into_region_once(
    stmts: &mut Vec<Stmt>,
    target: &mut Region,
    counts: &UseCounts,
) -> bool {
    let Some(source) = stmts.last().cloned() else {
        return false;
    };

    let changed = match source {
        Stmt::Let { local, value } if counts.locals.get(&local) == Some(&1) => {
            replace_local_in_region_target(target, local, value)
        }
        Stmt::LetPack { local, value } if counts.packs.get(&local) == Some(&1) => {
            replace_pack_in_region_target(target, local, value)
        }
        _ => false,
    };
    if changed {
        stmts.pop();
    }
    changed
}

/// Inlines a body-tail definition into a post-test condition.
fn inline_tail_into_expr_once(body: &mut Region, condition: &mut Expr, counts: &UseCounts) -> bool {
    let Some(stmts) = last_block_stmts(body) else {
        return false;
    };
    let Some(source) = stmts.last().cloned() else {
        return false;
    };
    let changed = match source {
        Stmt::Let { local, value } if counts.locals.get(&local) == Some(&1) => {
            replace_local(condition, local, value)
        }
        Stmt::LetPack { local, value } if counts.packs.get(&local) == Some(&1) => {
            replace_pack_in_expr(condition, local, value)
        }
        _ => false,
    };
    if changed {
        stmts.pop();
    }
    changed
}

/// Returns statements in the lexically last block of one region.
fn last_block_stmts(region: &mut Region) -> Option<&mut Vec<Stmt>> {
    match region {
        Region::Block { stmts, .. } => Some(stmts),
        Region::Sequence(nodes) => nodes.last_mut().and_then(last_block_stmts),
        _ => None,
    }
}

/// Replaces one local in the immediate consumer of a source block.
fn replace_local_in_region_target(target: &mut Region, local: LocalId, value: Expr) -> bool {
    match target {
        Region::If { condition, .. }
        | Region::While { condition, .. }
        | Region::RepeatUntil { condition, .. } => replace_local(condition, local, value),
        Region::NumericFor {
            start, end, step, ..
        } => replace_local_in_exprs([start, end, step], local, value),
        Region::GenericFor { values, .. } => {
            replace_local_in_exprs(values.iter_mut(), local, value)
        }
        Region::Return(values) => replace_local_in_pack(values, local, value),
        _ => false,
    }
}

/// Replaces one pack in the immediate consumer of a source block.
fn replace_pack_in_region_target(target: &mut Region, local: PackLocalId, value: PackExpr) -> bool {
    match target {
        Region::If { condition, .. }
        | Region::While { condition, .. }
        | Region::RepeatUntil { condition, .. } => replace_pack_in_expr(condition, local, value),
        Region::NumericFor {
            start, end, step, ..
        } => replace_pack_in_exprs([start, end, step], local, value),
        Region::GenericFor { values, .. } => replace_pack_in_exprs(values.iter_mut(), local, value),
        Region::Return(values) => replace_pack(values, local, value),
        _ => false,
    }
}

/// Replaces one local in a sequence of expressions while preserving order.
fn replace_local_in_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a mut Expr>,
    local: LocalId,
    value: Expr,
) -> bool {
    let can_delay = expr_can_delay(&value);
    let mut prior_effect = false;
    for expr in exprs {
        if let Some(changed) =
            replace_local_inner(expr, local, &value, can_delay, &mut prior_effect, false)
        {
            return changed;
        }
    }
    false
}

/// Replaces one pack in a sequence of expressions while preserving order.
fn replace_pack_in_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a mut Expr>,
    local: PackLocalId,
    value: PackExpr,
) -> bool {
    let can_delay = pack_can_delay(&value);
    let mut prior_effect = false;
    for expr in exprs {
        if let Some(changed) =
            replace_pack_in_expr_inner(expr, local, &value, can_delay, &mut prior_effect, false)
        {
            return changed;
        }
    }
    false
}

/// Replaces one local in an expression when movement is legal.
fn replace_local(expr: &mut Expr, local: LocalId, value: Expr) -> bool {
    let can_delay = expr_can_delay(&value);
    replace_local_inner(expr, local, &value, can_delay, &mut false, false).unwrap_or(false)
}

/// Replaces one pack in an expression when movement is legal.
fn replace_pack_in_expr(expr: &mut Expr, local: PackLocalId, value: PackExpr) -> bool {
    let can_delay = pack_can_delay(&value);
    replace_pack_in_expr_inner(expr, local, &value, can_delay, &mut false, false).unwrap_or(false)
}

/// Replaces one local in a pack expression when movement is legal.
fn replace_local_in_pack(pack: &mut PackExpr, local: LocalId, value: Expr) -> bool {
    let can_delay = expr_can_delay(&value);
    replace_local_in_pack_inner(pack, local, &value, can_delay, &mut false, false).unwrap_or(false)
}

/// Replaces one pack in a pack expression when movement is legal.
fn replace_pack(pack: &mut PackExpr, local: PackLocalId, value: PackExpr) -> bool {
    let can_delay = pack_can_delay(&value);
    replace_pack_inner(pack, local, &value, can_delay, &mut false, false).unwrap_or(false)
}

/// Attempts one ordered local substitution.
///
/// `None` means the local was not found. `Some(false)` means movement was unsafe.
fn replace_local_inner(
    expr: &mut Expr,
    local: LocalId,
    value: &Expr,
    can_delay: bool,
    prior_effect: &mut bool,
    conditional: bool,
) -> Option<bool> {
    if matches!(expr.kind, ExprKind::Local(found) if found == local) {
        if can_delay || (!*prior_effect && !conditional) {
            *expr = value.clone();
            return Some(true);
        }
        return Some(false);
    }

    let result = match &mut expr.kind {
        ExprKind::GetTable { table, key } => {
            replace_local_inner(table, local, value, can_delay, prior_effect, conditional).or_else(
                || replace_local_inner(key, local, value, can_delay, prior_effect, conditional),
            )
        }
        ExprKind::Binary { lhs, op, rhs } => {
            replace_local_inner(lhs, local, value, can_delay, prior_effect, conditional).or_else(
                || {
                    replace_local_inner(
                        rhs,
                        local,
                        value,
                        can_delay,
                        prior_effect,
                        conditional || matches!(op, BinOp::And | BinOp::Or),
                    )
                },
            )
        }
        ExprKind::Unary { value: inner, .. } => {
            replace_local_inner(inner, local, value, can_delay, prior_effect, conditional)
        }
        ExprKind::Concat(values) => {
            for inner in values {
                if let Some(result) =
                    replace_local_inner(inner, local, value, can_delay, prior_effect, conditional)
                {
                    return Some(result);
                }
            }
            None
        }
        ExprKind::Select {
            condition: test,
            then_value,
            else_value,
        } => replace_local_inner(test, local, value, can_delay, prior_effect, conditional)
            .or_else(|| {
                replace_local_inner(then_value, local, value, can_delay, prior_effect, true)
            })
            .or_else(|| {
                replace_local_inner(else_value, local, value, can_delay, prior_effect, true)
            }),
        ExprKind::Project { pack, .. } => {
            replace_local_in_pack_inner(pack, local, value, can_delay, prior_effect, conditional)
        }
        ExprKind::Local(_)
        | ExprKind::Constant(_)
        | ExprKind::Closure { .. }
        | ExprKind::GetGlobal(_)
        | ExprKind::NewTable
        | ExprKind::LoadCell(_) => None,
    };

    if result.is_none() && expr_has_effect(expr) {
        *prior_effect = true;
    }
    result
}

/// Attempts one ordered pack substitution inside an expression.
fn replace_pack_in_expr_inner(
    expr: &mut Expr,
    local: PackLocalId,
    value: &PackExpr,
    can_delay: bool,
    prior_effect: &mut bool,
    conditional: bool,
) -> Option<bool> {
    let result = match &mut expr.kind {
        ExprKind::GetTable { table, key } => {
            replace_pack_in_expr_inner(table, local, value, can_delay, prior_effect, conditional)
                .or_else(|| {
                    replace_pack_in_expr_inner(
                        key,
                        local,
                        value,
                        can_delay,
                        prior_effect,
                        conditional,
                    )
                })
        }
        ExprKind::Binary { lhs, op, rhs } => {
            replace_pack_in_expr_inner(lhs, local, value, can_delay, prior_effect, conditional)
                .or_else(|| {
                    replace_pack_in_expr_inner(
                        rhs,
                        local,
                        value,
                        can_delay,
                        prior_effect,
                        conditional || matches!(op, BinOp::And | BinOp::Or),
                    )
                })
        }
        ExprKind::Unary { value: inner, .. } => {
            replace_pack_in_expr_inner(inner, local, value, can_delay, prior_effect, conditional)
        }
        ExprKind::Concat(values) => {
            for inner in values {
                if let Some(result) = replace_pack_in_expr_inner(
                    inner,
                    local,
                    value,
                    can_delay,
                    prior_effect,
                    conditional,
                ) {
                    return Some(result);
                }
            }
            None
        }
        ExprKind::Select {
            condition: test,
            then_value,
            else_value,
        } => replace_pack_in_expr_inner(test, local, value, can_delay, prior_effect, conditional)
            .or_else(|| {
                replace_pack_in_expr_inner(then_value, local, value, can_delay, prior_effect, true)
            })
            .or_else(|| {
                replace_pack_in_expr_inner(else_value, local, value, can_delay, prior_effect, true)
            }),
        ExprKind::Project { pack, .. } => {
            replace_pack_inner(pack, local, value, can_delay, prior_effect, conditional)
        }
        ExprKind::Local(_)
        | ExprKind::Constant(_)
        | ExprKind::Closure { .. }
        | ExprKind::GetGlobal(_)
        | ExprKind::NewTable
        | ExprKind::LoadCell(_) => None,
    };
    if result.is_none() && expr_has_effect(expr) {
        *prior_effect = true;
    }
    result
}

/// Attempts one ordered local substitution inside a pack expression.
fn replace_local_in_pack_inner(
    pack: &mut PackExpr,
    local: LocalId,
    value: &Expr,
    can_delay: bool,
    prior_effect: &mut bool,
    conditional: bool,
) -> Option<bool> {
    let result = match &mut pack.kind {
        PackExprKind::Values { head, tail } => {
            for expr in head {
                if let Some(result) =
                    replace_local_inner(expr, local, value, can_delay, prior_effect, conditional)
                {
                    return Some(result);
                }
            }
            tail.as_deref_mut().and_then(|tail| {
                replace_local_in_pack_inner(
                    tail,
                    local,
                    value,
                    can_delay,
                    prior_effect,
                    conditional,
                )
            })
        }
        PackExprKind::Call { function, args } => {
            replace_local_inner(function, local, value, can_delay, prior_effect, conditional)
                .or_else(|| {
                    replace_local_in_pack_inner(
                        args,
                        local,
                        value,
                        can_delay,
                        prior_effect,
                        conditional,
                    )
                })
        }
        PackExprKind::MethodCall { object, args, .. } => replace_local_inner(
            object,
            local,
            value,
            can_delay,
            prior_effect,
            conditional,
        )
        .or_else(|| {
            replace_local_in_pack_inner(args, local, value, can_delay, prior_effect, conditional)
        }),
        PackExprKind::Local(_) | PackExprKind::VarArgs => None,
    };
    if result.is_none() && pack_has_effect(pack) {
        *prior_effect = true;
    }
    result
}

/// Attempts one ordered pack substitution inside a pack expression.
fn replace_pack_inner(
    pack: &mut PackExpr,
    local: PackLocalId,
    value: &PackExpr,
    can_delay: bool,
    prior_effect: &mut bool,
    conditional: bool,
) -> Option<bool> {
    if matches!(pack.kind, PackExprKind::Local(found) if found == local) {
        if can_delay || (!*prior_effect && !conditional) {
            *pack = value.clone();
            return Some(true);
        }
        return Some(false);
    }

    let result = match &mut pack.kind {
        PackExprKind::Values { head, tail } => {
            for expr in head {
                if let Some(result) = replace_pack_in_expr_inner(
                    expr,
                    local,
                    value,
                    can_delay,
                    prior_effect,
                    conditional,
                ) {
                    return Some(result);
                }
            }
            tail.as_deref_mut().and_then(|tail| {
                replace_pack_inner(tail, local, value, can_delay, prior_effect, conditional)
            })
        }
        PackExprKind::Call { function, args } => {
            replace_pack_in_expr_inner(function, local, value, can_delay, prior_effect, conditional)
                .or_else(|| {
                    replace_pack_inner(args, local, value, can_delay, prior_effect, conditional)
                })
        }
        PackExprKind::MethodCall { object, args, .. } => {
            replace_pack_in_expr_inner(object, local, value, can_delay, prior_effect, conditional)
                .or_else(|| {
                    replace_pack_inner(args, local, value, can_delay, prior_effect, conditional)
                })
        }
        PackExprKind::Local(_) | PackExprKind::VarArgs => None,
    };
    if result.is_none() && pack_has_effect(pack) {
        *prior_effect = true;
    }
    result
}

/// Returns whether delaying an expression cannot change observable behavior.
fn expr_can_delay(expr: &Expr) -> bool {
    matches!(expr.kind, ExprKind::Local(_) | ExprKind::Constant(_))
}

/// Returns whether delaying a pack cannot change observable behavior.
fn pack_can_delay(pack: &PackExpr) -> bool {
    match &pack.kind {
        PackExprKind::Local(_) => true,
        PackExprKind::Values { head, tail } => {
            head.iter().all(expr_can_delay) && tail.as_deref().is_none_or(pack_can_delay)
        }
        PackExprKind::Call { .. } | PackExprKind::MethodCall { .. } | PackExprKind::VarArgs => {
            false
        }
    }
}

/// Returns whether evaluating an expression may be observable.
fn expr_has_effect(expr: &Expr) -> bool {
    !matches!(expr.kind, ExprKind::Local(_) | ExprKind::Constant(_))
}

/// Returns whether evaluating a pack may be observable.
fn pack_has_effect(pack: &PackExpr) -> bool {
    !pack_can_delay(pack)
}

#[cfg(test)]
mod tests {
    use id_arena::Arena;

    use super::*;
    use crate::ir::Value;

    /// Creates one local identity for substitution tests.
    fn locals() -> (LocalId, LocalId) {
        let mut values = Arena::<Value>::new();
        let first_source = values.alloc(Value);
        let second_source = values.alloc(Value);
        let mut locals = Arena::<Local>::new();
        (
            locals.alloc(Local {
                source: first_source,
            }),
            locals.alloc(Local {
                source: second_source,
            }),
        )
    }

    /// Keeps unconditional work outside a short-circuit right operand.
    #[test]
    fn rejects_effectful_source_in_short_circuit_rhs() {
        let (source, other) = locals();
        let mut target = Expr {
            origin: None,
            kind: ExprKind::Binary {
                lhs: Box::new(Expr::local(other)),
                op: BinOp::And,
                rhs: Box::new(Expr::local(source)),
            },
        };
        let value = Expr {
            origin: None,
            kind: ExprKind::GetGlobal("effectful".into()),
        };

        assert!(!replace_local(&mut target, source, value));
        assert!(matches!(
            target.kind,
            ExprKind::Binary { rhs, .. } if matches!(rhs.kind, ExprKind::Local(local) if local == source)
        ));
    }

    /// Keeps source evaluation before an earlier observable target operand.
    #[test]
    fn rejects_effectful_source_after_target_effect() {
        let (source, _) = locals();
        let mut target = Expr {
            origin: None,
            kind: ExprKind::Binary {
                lhs: Box::new(Expr {
                    origin: None,
                    kind: ExprKind::GetGlobal("first".into()),
                }),
                op: BinOp::Add,
                rhs: Box::new(Expr::local(source)),
            },
        };
        let value = Expr {
            origin: None,
            kind: ExprKind::GetGlobal("source".into()),
        };

        assert!(!replace_local(&mut target, source, value));
    }

    /// Replaces an immediate control condition at the same evaluation point.
    #[test]
    fn inlines_effectful_root_condition() {
        let (source, _) = locals();
        let mut target = Expr::local(source);
        let value = Expr {
            origin: None,
            kind: ExprKind::GetGlobal("condition".into()),
        };

        assert!(replace_local(&mut target, source, value));
        assert!(matches!(target.kind, ExprKind::GetGlobal(_)));
    }
}
