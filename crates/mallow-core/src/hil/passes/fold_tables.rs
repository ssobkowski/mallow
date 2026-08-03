//! Attempts to fold table-modifying instructions like SetList, or Assign(GetIndex, ...)
//! into valid table constructors.
//!
//! Such instructions can be folded only if they appear after an assignment to a table expr.

use crate::hil::StructuredFunction;
use crate::hil::ir::{Expr, Number, Stmt, TableItem};
use crate::hil::visitor::VisitorMut;

#[derive(Default)]
struct Inliner {
    changed: bool,
}

impl VisitorMut for Inliner {
    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        let mut i = 0;
        while i < stmts.len() {
            let Stmt::Assign {
                left: Expr::Symbol(target_table),
                value: Expr::Table {
                    items: original_items,
                },
            } = &stmts[i]
            else {
                i += 1;
                continue;
            };

            let is_target_table =
                |expr: &Expr| matches!(expr, Expr::Symbol(s) if s == target_table);

            let mut items_to_add = Vec::new();
            let mut stmts_to_remove = Vec::new();

            // These must be right after the initial assignment
            let mut j = i + 1;
            while j < stmts.len() {
                match &stmts[j] {
                    Stmt::Assign {
                        left: Expr::GetField { obj, field },
                        value,
                    } if is_target_table(obj)
                        && !is_target_table(value)
                        && !value.reads_symbol(target_table) =>
                    {
                        stmts_to_remove.push(j);
                        items_to_add.push(TableItem::Index(
                            Expr::String(field.clone().into()),
                            value.clone(),
                        ));
                    }
                    Stmt::Assign {
                        left: Expr::GetIndex { obj, index },
                        value,
                    } if is_target_table(obj)
                        && !is_target_table(value)
                        && !index.reads_symbol(target_table)
                        && !value.reads_symbol(target_table) =>
                    {
                        stmts_to_remove.push(j);
                        items_to_add.push(TableItem::Index(index.as_ref().clone(), value.clone()));
                    }
                    Stmt::SetList {
                        table,
                        index: base,
                        values,
                    } if table == target_table => {
                        let Some(array_items_size) = items_to_add
                            .iter()
                            .chain(original_items.iter())
                            .try_fold(0usize, |count, item| match item {
                                TableItem::List(values) => Some(count + values.fixed_len()?),
                                TableItem::Index(_, _) => Some(count),
                            })
                        else {
                            break;
                        };

                        let is_contiguous = *base as usize == array_items_size + 1;
                        if values.is_open() && !is_contiguous {
                            break;
                        }

                        stmts_to_remove.push(j);
                        if is_contiguous {
                            items_to_add.push(TableItem::List(values.clone()));
                        } else {
                            items_to_add.extend(values.iter().enumerate().map(|(i, value)| {
                                let index = Expr::Number(Number::Float(*base as f64 + i as f64));
                                TableItem::Index(index, value.clone())
                            }));
                        }

                        if values.is_open() {
                            break;
                        }
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

            if let Stmt::Assign {
                value: Expr::Table { items },
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
