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

/// Decodes a Luau call/return sentinel count field into a [`Count`].
pub const fn decoded_count(encoded: u8) -> Count {
    match encoded {
        0 => Count::Variadic,
        n => Count::Number(n - 1),
    }
}

pub const fn reg_add(reg: u8, offset: u8) -> u8 {
    reg.checked_add(offset).expect("register overflow")
}

pub const fn reg_range(start: u8, count: u8) -> impl Iterator<Item = u8> {
    let end = start.checked_add(count).expect("register range overflow");
    start..end
}
