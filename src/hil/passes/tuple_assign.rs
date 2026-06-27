use crate::hil::{
    StructuredFunction,
    ir::{HilExpr, HilStmt},
    lifter::ssa::SymbolId,
    visitor::{VisitorMut, walk_stmts_mut},
};

#[derive(Default)]
struct Rewriter {
    changed: bool,
}

impl Rewriter {
    fn try_rewrite_stmts(&mut self, stmts: &mut Vec<HilStmt>) {
        let mut i = 0;
        while i < stmts.len() {
            let HilStmt::AssignMany { left, value } = &stmts[i] else {
                i += 1;
                continue;
            };

            let tuple_symbols: Vec<_> = left
                .iter()
                .filter_map(|lvalue| match lvalue {
                    HilExpr::Symbol(sym) => Some(*sym),
                    _ => None,
                })
                .collect();

            if tuple_symbols.is_empty() || tuple_symbols.len() != left.len() {
                i += 1;
                continue;
            }

            let mut tuple_lvalues = Vec::new();
            let mut consumed = 0usize;

            for (offset, sym) in tuple_symbols.iter().enumerate() {
                let idx = i + 1 + offset;
                if idx >= stmts.len() {
                    break;
                }

                let HilStmt::Assign {
                    left: target,
                    value: HilExpr::Symbol(src),
                } = &stmts[idx]
                else {
                    break;
                };

                if src != sym || !is_safe_tuple_lvalue_target(target, &tuple_symbols) {
                    break;
                }

                tuple_lvalues.push(target.clone());
                consumed += 1;
            }

            if consumed == 0 {
                i += 1;
                continue;
            }

            if stmts[i + 1 + consumed..].iter().any(|stmt| {
                tuple_symbols
                    .iter()
                    .any(|sym| stmt_mentions_symbol(stmt, *sym))
            }) {
                i += 1;
                continue;
            }

            let rhs = value.clone();
            stmts[i] = HilStmt::AssignMany {
                left: tuple_lvalues,
                value: rhs,
            };

            stmts.drain(i + 1..i + 1 + consumed);
            self.changed = true;
            i += 1;
        }
    }
}

impl VisitorMut for Rewriter {
    fn visit_stmts(&mut self, stmts: &mut Vec<HilStmt>) {
        self.try_rewrite_stmts(stmts);
        walk_stmts_mut(self, stmts);
    }
}

fn is_safe_tuple_lvalue_target(target: &HilExpr, tuple_symbols: &[SymbolId]) -> bool {
    if tuple_symbols.iter().any(|sym| target.reads_symbol(sym)) {
        return false;
    }

    match target {
        HilExpr::GetField { obj, .. } => obj.is_pure(),
        HilExpr::GetIndex { obj, index } => obj.is_pure() && index.is_pure(),
        _ => false,
    }
}

fn stmt_mentions_symbol(stmt: &HilStmt, sym: SymbolId) -> bool {
    match stmt {
        HilStmt::Assign { left, value } => left.reads_symbol(&sym) || value.reads_symbol(&sym),
        HilStmt::AssignMany { left, value } => {
            left.iter().any(|lvalue| lvalue.reads_symbol(&sym)) || value.reads_symbol(&sym)
        }
        HilStmt::SetList { table, values, .. } => {
            *table == sym || values.iter().any(|expr| expr.reads_symbol(&sym))
        }
        HilStmt::Call(expr) => expr.reads_symbol(&sym),
        HilStmt::Phi(node) => {
            node.target == sym || node.operands.iter().any(|(_, operand)| *operand == sym)
        }
    }
}

pub fn run(fun: &mut StructuredFunction) -> bool {
    let mut rewriter = Rewriter::default();
    rewriter.visit_function(fun);
    rewriter.changed
}
