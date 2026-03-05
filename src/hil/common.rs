use crate::{
    hil::ir::HilExpr,
    il::{Constant, Count},
};

/// Decodes constants into condition-compatible HIL expressions.
#[must_use]
pub fn const_expr(consts: &[Constant], index: usize) -> HilExpr {
    match consts.get(index) {
        Some(Constant::String(value)) => HilExpr::String(value.clone()),
        Some(Constant::Number(value)) => HilExpr::Number(*value),
        Some(Constant::Boolean(value)) => HilExpr::Bool(*value),
        Some(Constant::Nil) => HilExpr::Nil,
        _ => panic!("unsupported const at {index}"),
    }
}

/// Decodes a Luau call/return sentinel count field into a [`Count`](crate::il::Count).
pub fn decoded_count(encoded: u8) -> Count {
    match encoded {
        0 => Count::Variadic,
        n => Count::Number(n - 1),
    }
}

/// Produces a list of local-register expressions for a half-open register range.
///
/// # Returns
/// A vector of `HilExpr::Local` expressions for registers `[start, start + count)`.
#[must_use]
pub fn local_range(start: u8, count: u8) -> Vec<HilExpr> {
    debug_assert!(
        start.checked_add(count).is_some(),
        "local_range overflow: start={start} count={count}"
    );

    (0..count)
        .map(|i| HilExpr::Local(start + i))
        .collect()
}

/// Produces return expressions for one `RETURN` opcode.
///
/// # Returns
/// - fixed list of locals for fixed-arity returns.
/// - one base local for MULTRET returns.
#[must_use]
pub fn return_values(base: u8, count: u8) -> Vec<HilExpr> {
    match decoded_count(count) {
        Count::Number(n) => local_range(base, n),
        _ => vec![HilExpr::Local(base)],
    }
}
