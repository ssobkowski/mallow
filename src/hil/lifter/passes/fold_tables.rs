//! Folds scattered table-building HIL statements back into a single [`HilExpr::Table`] constructor.
//!
//! The Luau compiler lowers table constructors into a `NEWTABLE` followed by a sequence of
//! `SETTABLEKS` and `SETLIST` instructions, with arbitrary intermediate computation inbetween.
//! The lifter preserves this faithfully as [`HilStmt::SetField`] and [`HilStmt::SetList`] nodes.
//!
//! This pass scans for a local assigned an empty [`HilExpr::Table`], then walks forward collecting
//! consecutive field and list writes targeting that register — stopping at any instruction that
//! reads or writes the register for any other purpose. If the entire write sequence is clean, the
//! statements are collapsed in-place into the initial table expression and removed.
//!
//! A [`HilTableItem::Tail`] is emitted for any [`HilStmt::SetList`] with `has_variadic_tail` set,
//! preserving multiret semantics. This variant must remain the final item in the constructor;
//! downstream passes (notably inlining) may dissolve it into a direct call expression before
//! codegen, otherwise the lowerer will emit a `table.unpack` with explicit `.n` bounds.

use std::collections::HashMap;

use smol_str::{SmolStr, format_smolstr};

use crate::hil::ir::{HilCapture, HilExpr, HilStmt, HilTableItem, Spanned, ToSpanned};

struct PendingTable {
    items: Vec<HilTableItem>,
    // Index of the last builder instruction that wrote to this table
    last_builder_index: usize,
}

pub fn fold_table_constructors(stmts: Vec<Spanned<HilStmt>>) -> Vec<Spanned<HilStmt>> {
    let mut pending: HashMap<u8, PendingTable> = HashMap::new();
    let mut completed: Vec<(u8, PendingTable)> = Vec::new();

    let mut new_stmts = Vec::new();
    for (i, stmt) in stmts.into_iter().enumerate() {
        let mut to_remove = Vec::new();
        for &reg in pending.keys() {
            if interferes_with_build(&stmt.inner, reg) {
                to_remove.push(reg);
            }
        }

        // Move broken tables to the completed list
        for reg in to_remove {
            if let Some(finished) = pending.remove(&reg) {
                completed.push((reg, finished));
            }
        }

        let table_reg = match &stmt.inner {
            HilStmt::Assign {
                left: HilExpr::Reg(reg),
                value: HilExpr::Table { items },
            } if items.is_empty() => {
                pending.insert(
                    *reg,
                    PendingTable {
                        items: Vec::new(),
                        last_builder_index: i,
                    },
                );
                new_stmts.push(
                    HilStmt::Assign {
                        left: HilExpr::Reg(*reg),
                        value: HilExpr::Nil,
                    }
                    .to_spanned(stmt.pc),
                );
                Some(*reg)
            }
            HilStmt::SetList {
                table,
                index,
                values,
                has_variadic_tail,
            } if pending.contains_key(table) => {
                let pending = pending.get_mut(table).unwrap();
                pending.last_builder_index = i;
                if *has_variadic_tail {
                    let loc_name = HilExpr::Local(list_element_name(*table, *index, true));
                    pending.items.push(HilTableItem::Packed(loc_name.clone()));
                    new_stmts.push(
                        HilStmt::Assign {
                            left: loc_name,
                            // table.pack(value)
                            value: HilExpr::Call {
                                fun: Box::new(HilExpr::GetField {
                                    obj: Box::new(HilExpr::Global("table".into())),
                                    field: "pack".into(),
                                }),
                                args: values.clone(),
                            },
                        }
                        .to_spanned(stmt.pc),
                    );
                } else {
                    debug_assert!(!values.is_empty());

                    let loc_name = HilExpr::Local(list_element_name(*table, *index, false));
                    let value = if values.len() == 1 {
                        pending.items.push(HilTableItem::List(loc_name.clone()));
                        values[0].clone()
                    } else {
                        pending.items.push(HilTableItem::Packed(loc_name.clone()));
                        HilExpr::Table {
                            items: values
                                .iter()
                                .map(|e| HilTableItem::List(e.clone()))
                                .collect(),
                        }
                    };
                    new_stmts.push(
                        HilStmt::Assign {
                            left: loc_name,
                            value,
                        }
                        .to_spanned(stmt.pc),
                    );
                }

                Some(*table)
            }
            HilStmt::SetField { table, key, value } if pending.contains_key(table) => {
                let pending = pending.get_mut(table).unwrap();
                pending.last_builder_index = i;

                let loc_name = HilExpr::Local(field_element_name(*table, key));
                pending.items.push(HilTableItem::Index(
                    HilExpr::String(key.to_string()),
                    loc_name.clone(),
                ));
                new_stmts.push(
                    HilStmt::Assign {
                        left: loc_name.clone(),
                        value: value.clone(),
                    }
                    .to_spanned(stmt.pc),
                );

                Some(*table)
            }
            _ => None,
        };

        if table_reg.is_none() {
            new_stmts.push(stmt);
        }
    }

    // Sort in reverse order by statement index to account for shifting when inserting
    // the table constructor
    completed.extend(pending);
    completed.sort_by(|a, b| b.1.last_builder_index.cmp(&a.1.last_builder_index));

    for (reg, table) in completed {
        new_stmts.insert(
            table.last_builder_index + 1,
            HilStmt::Assign {
                left: HilExpr::Reg(reg),
                value: HilExpr::Table { items: table.items },
            }
            .to_spanned(0),
        );
    }

    new_stmts
}

/// Returns whether the given statement reads the given register.
fn reads_register(stmt: &HilStmt, reg: u8) -> bool {
    match stmt {
        HilStmt::Assign { left, value } => {
            reads_register_expr(left, reg) || reads_register_expr(value, reg)
        }
        HilStmt::AssignMany { left, value } => {
            left.iter().any(|e| reads_register_expr(e, reg)) || reads_register_expr(value, reg)
        }
        HilStmt::SetList { table, values, .. } => {
            *table == reg || values.iter().any(|e| reads_register_expr(e, reg))
        }
        HilStmt::SetField { table, value, .. } => *table == reg || reads_register_expr(value, reg),
        _ => false,
    }
}

fn reads_register_expr(expr: &HilExpr, reg: u8) -> bool {
    match expr {
        HilExpr::Reg(r) => *r == reg,
        HilExpr::Closure { captures, .. } => captures.iter().any(|c| match c {
            HilCapture::Local(r) => *r == reg,
            HilCapture::Upval(_) => false,
        }),
        HilExpr::GetField { obj, .. } => reads_register_expr(obj, reg),
        HilExpr::GetIndex { obj, index } => {
            reads_register_expr(obj, reg) || reads_register_expr(index, reg)
        }
        HilExpr::Call { fun, args } => {
            reads_register_expr(fun, reg) || args.iter().any(|e| reads_register_expr(e, reg))
        }
        HilExpr::MethodCall { object, args, .. } => {
            reads_register_expr(object, reg) || args.iter().any(|e| reads_register_expr(e, reg))
        }
        HilExpr::Binary { lhs, rhs, .. } => {
            reads_register_expr(lhs, reg) || reads_register_expr(rhs, reg)
        }
        HilExpr::Unary { expr, .. } => reads_register_expr(expr, reg),
        HilExpr::Table { items } => items.iter().any(|it| match it {
            HilTableItem::List(expr) => reads_register_expr(expr, reg),
            HilTableItem::Index(key, value) => {
                reads_register_expr(key, reg) || reads_register_expr(value, reg)
            }
            HilTableItem::Packed(expr) => reads_register_expr(expr, reg),
        }),
        _ => false,
    }
}

fn interferes_with_build(stmt: &HilStmt, reg: u8) -> bool {
    match stmt {
        // If it's a builder statement targeting THIS register, it only interferes
        // if the value being assigned reads the register (e.g., self-reference: t.b = t)
        HilStmt::SetList { table, values, .. } if *table == reg => {
            values.iter().any(|e| reads_register_expr(e, reg))
        }
        HilStmt::SetField { table, value, .. } if *table == reg => reads_register_expr(value, reg),
        _ => reads_register(stmt, reg),
    }
}

// For SetList
fn list_element_name(table: u8, index: u32, is_varying: bool) -> SmolStr {
    if is_varying {
        format_smolstr!("_t{}_i{}_varying", table, index)
    } else {
        format_smolstr!("_t{}_i{}", table, index)
    }
}

// For SetField
fn field_element_name(table: u8, key: &str) -> SmolStr {
    let safe_key = key.replace(|c: char| !c.is_ascii_alphanumeric(), "_");
    SmolStr::from(format!("_t{}_k_{}", table, safe_key))
}
