//! Attempts to fold table-modifying instructions like SetList, or Assign(GetIndex, ...)
//! into valid table constructors.
//!
//! Such instructions can be folded only if they appear after an assignment to a table expr.

use crate::ir::fir::{Constant, Number};
use crate::ir::nir::visitor::VisitorMut;
use crate::ir::nir::{Expr, Function, Place, Stmt, TableItem};

pub(super) fn run(function: &mut Function) -> bool {
    let mut folder = Folder::default();
    folder.visit_function(function);
    folder.changed
}

#[derive(Default)]
struct Folder {
    changed: bool,
}

impl VisitorMut for Folder {
    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        let mut i = 0;
        while i < stmts.len() {
            let (target_table, mut array_size) = match &stmts[i] {
                Stmt::Bind {
                    target: Place::Local(target),
                    value: Expr::Table { items },
                } => {
                    let initial_len = items.iter().try_fold(0usize, |count, item| match item {
                        TableItem::List(values) => Some(count + values.fixed_len()?),
                        TableItem::Index(_, _) => Some(count),
                    });
                    (*target, initial_len)
                }
                _ => {
                    i += 1;
                    continue;
                }
            };

            let is_target_table =
                |expr: &Expr| matches!(expr, Expr::Local(id) if *id == target_table);

            let mut j = i + 1;
            while j < stmts.len() {
                match &stmts[j] {
                    Stmt::Bind {
                        target: Place::Table { table, key },
                        value,
                    } if is_target_table(table)
                        && !is_target_table(value)
                        && !value.contains_local(target_table)
                        && !key.contains_local(target_table) =>
                    {
                        j += 1;
                    }
                    Stmt::SetList {
                        table: Expr::Local(table),
                        index: base,
                        values,
                    } if *table == target_table => {
                        let Some(curr_size) = array_size else { break };
                        let is_contiguous = *base as usize == curr_size + 1;

                        if values.is_open() && !is_contiguous {
                            break;
                        }

                        if is_contiguous {
                            array_size = values.fixed_len().map(|len| curr_size + len);
                        }

                        j += 1;

                        if values.is_open() {
                            break;
                        }
                    }
                    _ => break,
                }
            }

            if j > i + 1 {
                self.changed = true;

                let mut items = match &mut stmts[i] {
                    Stmt::Bind {
                        value: Expr::Table { items },
                        ..
                    } => std::mem::take(items),
                    _ => unreachable!("this statement is a table bind"),
                };

                // Re-calculate running array size for constructing TableItem::List vs Index
                let mut current_array_len =
                    items.iter().try_fold(0usize, |count, item| match item {
                        TableItem::List(values) => Some(count + values.fixed_len()?),
                        TableItem::Index(_, _) => Some(count),
                    });

                for stmt in stmts.drain(i + 1..j) {
                    match stmt {
                        Stmt::Bind {
                            target: Place::Table { key, .. },
                            value,
                        } => items.push(TableItem::Index(key, value)),
                        Stmt::SetList {
                            index: base,
                            values,
                            ..
                        } => {
                            let is_contiguous =
                                current_array_len.is_some_and(|len| base as usize == len + 1);

                            if is_contiguous {
                                current_array_len = values
                                    .fixed_len()
                                    .and_then(|len| current_array_len.map(|c| c + len));
                                items.push(TableItem::List(values));
                            } else {
                                items.extend(values.into_iter().enumerate().map(|(k, val)| {
                                    let idx_expr = Expr::Constant(Constant::Number(Number::Float(
                                        base as f64 + k as f64,
                                    )));
                                    TableItem::Index(idx_expr, val.clone())
                                }));
                            }
                        }
                        _ => unreachable!("other statements cannot appear here"),
                    }
                }

                let Stmt::Bind {
                    value: Expr::Table { items: table_items },
                    ..
                } = &mut stmts[i]
                else {
                    unreachable!("this statement is a table bind");
                };

                *table_items = items;
            }

            i += 1;
        }
    }
}
