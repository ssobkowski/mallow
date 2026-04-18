//! Attempts to fold table-modifying instructions like SetList, or Assign(GetIndex, ...)
//! into valid table constructors.
//!
//! Such instructions can be folded only if they appear after an assignment to a table expr.

use crate::hil::{
    StructuredFunction,
    ir::{HilExpr, HilStmt, HilTableItem},
    passes::visitor::VisitorMut,
};

#[derive(Default)]
struct Inliner {
    changed: bool,
}

impl VisitorMut for Inliner {
    fn visit_block(&mut self, stmts: &mut Vec<HilStmt>) {
        let mut i = 0;
        while i < stmts.len() {
            let HilStmt::Assign {
                left: HilExpr::Symbol(target_table),
                value: HilExpr::Table {
                    items: original_items,
                },
            } = &stmts[i]
            else {
                i += 1;
                continue;
            };

            let is_target_table =
                |expr: &HilExpr| matches!(expr, HilExpr::Symbol(s) if s == target_table);

            let mut items_to_add = Vec::new();
            let mut stmts_to_remove = Vec::new();

            // These must be right after the initial assignment
            let mut j = i + 1;
            while j < stmts.len() {
                match &stmts[j] {
                    HilStmt::Assign {
                        left: HilExpr::GetField { obj, field },
                        value,
                    } if is_target_table(obj)
                        && !is_target_table(value)
                        && !value.reads_symbol(target_table) =>
                    {
                        stmts_to_remove.push(j);
                        items_to_add.push(HilTableItem::Index(
                            HilExpr::String(field.clone().into()),
                            value.clone(),
                        ));
                    }
                    HilStmt::Assign {
                        left: HilExpr::GetIndex { obj, index },
                        value,
                    } if is_target_table(obj)
                        && !is_target_table(value)
                        && !index.reads_symbol(target_table)
                        && !value.reads_symbol(target_table) =>
                    {
                        stmts_to_remove.push(j);
                        items_to_add
                            .push(HilTableItem::Index(index.as_ref().clone(), value.clone()));
                    }
                    HilStmt::SetList {
                        table,
                        index: base,
                        values,
                        has_variadic_tail,
                    } if table == target_table => {
                        let array_items_size = items_to_add
                            .iter()
                            .chain(original_items.iter())
                            .filter(|item| matches!(item, HilTableItem::List(_)))
                            .count();

                        stmts_to_remove.push(j);
                        items_to_add.extend(values.iter().enumerate().map(|(i, v)| {
                            // If the base relative to how many array items are in the table is 1,
                            // then we can continue building the array. If not, we must explicitly
                            // index it.
                            let needs_index =
                                (*base as usize).saturating_sub(array_items_size) != 1;
                            if needs_index {
                                let index = HilExpr::Number(*base as f64 + i as f64);
                                HilTableItem::Index(index, v.clone())
                            } else {
                                HilTableItem::List(v.clone())
                            }
                        }));
                    }
                    _ => break,
                }

                j += 1;
            }

            if !items_to_add.is_empty() || !stmts_to_remove.is_empty() {
                self.changed = true;
            }

            // Remove in reverse so indices stay valid
            for &idx in stmts_to_remove.iter().rev() {
                stmts.remove(idx);
            }

            if let HilStmt::Assign {
                value: HilExpr::Table { items },
                ..
            } = &mut stmts[i]
            {
                items.extend(items_to_add);
            }

            i += 1;
        }
    }
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut changed = false;
    loop {
        let mut inliner = Inliner::default();
        inliner.visit_function(fun);
        if !inliner.changed {
            break;
        }
        changed = true;
    }
    changed
}
