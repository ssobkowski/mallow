//! Folds conditional assignments into value expressions.
//!
//! A local assignment followed by a conditional assignment to the same source
//! storage can be represented by one `and` or `or` expression. An if-else whose
//! branches assign the same source storage can be represented by a select expression.
//! A short-circuit fallback must not read that storage because its fold delays the
//! write until the complete expression has been evaluated.

use id_arena::Arena;

use crate::ir::fir::ValueId;
use crate::ir::nir::visitor::{Visitor, VisitorMut, walk_expr, walk_region_mut};
use crate::ir::nir::{Expr, Function, Local, LocalId, Place, Region, Stmt};
use crate::operator::{BinOp, UnOp};

pub(super) fn run(function: &mut Function) -> bool {
    let Function { locals, body, .. } = function;
    let mut folder = Folder {
        locals,
        changed: false,
    };
    folder.visit_region(body);
    folder.changed
}

struct StorageUse<'a> {
    locals: &'a Arena<Local>,
    source: ValueId,
    found: bool,
}

impl Visitor for StorageUse<'_> {
    fn visit_expr(&mut self, expr: &Expr) {
        if !self.found {
            walk_expr(self, expr);
        }
    }

    fn visit_local(&mut self, local: LocalId) {
        self.found |= self.locals[local].source == self.source;
    }
}

struct LocalBind<'a> {
    origin: usize,
    target: LocalId,
    value: &'a Expr,
}

fn local_bind(region: &Region) -> Option<LocalBind<'_>> {
    let Region::Block { origin, stmts } = region else {
        return None;
    };
    let [
        Stmt::Bind {
            target: Place::Local(target),
            value,
        },
    ] = stmts.as_slice()
    else {
        return None;
    };

    Some(LocalBind {
        origin: *origin,
        target: *target,
        value,
    })
}

struct Folder<'a> {
    locals: &'a Arena<Local>,
    changed: bool,
}

impl Folder<'_> {
    fn is_same(&self, left: LocalId, right: LocalId) -> bool {
        self.locals[left].source == self.locals[right].source
    }

    fn is_used_by(&self, local: LocalId, value: &Expr) -> bool {
        let mut finder = StorageUse {
            locals: self.locals,
            source: self.locals[local].source,
            found: false,
        };
        finder.visit_expr(value);
        finder.found
    }

    fn fold_pair(&self, first: &mut Region, second: &Region) -> bool {
        let Region::Block { stmts, .. } = first else {
            return false;
        };
        let Some(Stmt::Bind {
            target: Place::Local(initial_target),
            value: initial_value,
        }) = stmts.last_mut()
        else {
            return false;
        };
        let Region::If {
            condition,
            then_branch,
            else_branch: None,
        } = second
        else {
            return false;
        };

        let (condition_local, op) = match condition {
            Expr::Local(local) => (*local, BinOp::And),
            Expr::Unary {
                op: UnOp::Not,
                value,
            } => {
                let Expr::Local(local) = value.as_ref() else {
                    return false;
                };
                (*local, BinOp::Or)
            }
            _ => return false,
        };
        let Some(branch) = local_bind(then_branch) else {
            return false;
        };

        if !self.is_same(*initial_target, condition_local)
            || !self.is_same(*initial_target, branch.target)
            || self.is_used_by(*initial_target, branch.value)
        {
            return false;
        }

        *initial_value = Expr::Binary {
            lhs: Box::new(initial_value.clone()),
            op,
            rhs: Box::new(branch.value.clone()),
        };
        true
    }

    fn fold_select(&self, region: &mut Region) -> bool {
        let Region::If {
            condition,
            then_branch,
            else_branch: Some(else_branch),
        } = region
        else {
            return false;
        };
        let Some(then_bind) = local_bind(then_branch) else {
            return false;
        };
        let Some(else_bind) = local_bind(else_branch) else {
            return false;
        };
        if !self.is_same(then_bind.target, else_bind.target) {
            return false;
        }

        *region = Region::Block {
            origin: then_bind.origin,
            stmts: vec![Stmt::Bind {
                target: Place::Local(then_bind.target),
                value: Expr::Select {
                    condition: Box::new(condition.clone()),
                    then_value: Box::new(then_bind.value.clone()),
                    else_value: Box::new(else_bind.value.clone()),
                },
            }],
        };
        true
    }

    fn fold_sequence(&self, nodes: &mut Vec<Region>) -> bool {
        let input = std::mem::take(nodes);
        let mut output = Vec::with_capacity(input.len());
        let mut changed = false;

        for node in input {
            let folded = output
                .last_mut()
                .is_some_and(|previous| self.fold_pair(previous, &node));
            if folded {
                changed = true;
            } else {
                output.push(node);
            }
        }

        *nodes = output;
        changed
    }
}

impl VisitorMut for Folder<'_> {
    fn visit_region(&mut self, region: &mut Region) {
        walk_region_mut(self, region);
        self.changed |= self.fold_select(region);

        if let Region::Sequence(nodes) = region {
            self.changed |= self.fold_sequence(nodes);
        }
    }
}
