//! Removes dead nil initializers.
//!
//! A nil initializer which is overwritten before its storage is read is removed,
//! so the overwriting assignment becomes the only definition of the storage.

use std::collections::HashSet;

use id_arena::Arena;

use super::StorageUse;
use crate::ir::fir::{Constant, ValueId};
use crate::ir::nir::visitor::{VisitorMut, walk_stmts_mut};
use crate::ir::nir::{Expr, Function, Local, Place, Region, Stmt};

pub(super) fn run(function: &mut Function) -> bool {
    let Function {
        locals,
        cell_locals,
        body,
        ..
    } = function;

    let dead = {
        let cell_sources: HashSet<_> = cell_locals
            .values()
            .map(|local| locals[*local].source)
            .collect();
        let mut finder = DeadInitializers {
            locals,
            cell_sources: &cell_sources,
            dead: HashSet::new(),
        };
        finder.root(body);
        finder.dead
    };
    if dead.is_empty() {
        return false;
    }

    let mut remover = InitializerRemover { dead: &dead };
    remover.visit_region(body);
    true
}

/// First access to a storage along a straight-line path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Access {
    /// The storage is assigned without being read first.
    Overwrite,
    /// The storage may be read, or the path may leave the scope.
    Other,
}

/// Finds nil initializers which are overwritten before their storage is read.
struct DeadInitializers<'a> {
    locals: &'a Arena<Local>,
    /// Storage backing a cell, whose accesses are not explicit local uses.
    cell_sources: &'a HashSet<ValueId>,
    /// Addresses of the dead initializers.
    dead: HashSet<*const Stmt>,
}

impl DeadInitializers<'_> {
    /// Scans one lexical scope and every scope nested in it.
    ///
    /// An initializer is only matched against writes later in its own sequence,
    /// including writes inside nested sequences.
    fn root(&mut self, region: &Region) {
        let nodes = match region {
            Region::Sequence(children) => children.as_slice(),
            region => std::slice::from_ref(region),
        };
        for (index, node) in nodes.iter().enumerate() {
            match node {
                Region::Block { stmts, .. } => {
                    for (position, stmt) in stmts.iter().enumerate() {
                        let Stmt::Bind {
                            target: Place::Local(local),
                            value: Expr::Constant(Constant::Nil),
                        } = stmt
                        else {
                            continue;
                        };
                        let source = self.locals[*local].source;
                        if self.cell_sources.contains(&source) {
                            continue;
                        }
                        let access =
                            self.stmts_access(source, &stmts[position + 1..])
                                .or_else(|| {
                                    nodes[index + 1..]
                                        .iter()
                                        .find_map(|node| self.region_access(source, node))
                                });
                        if access == Some(Access::Overwrite) {
                            self.dead.insert(stmt);
                        }
                    }
                }
                Region::Sequence(_) => self.root(node),
                Region::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    self.root(then_branch);
                    if let Some(else_branch) = else_branch {
                        self.root(else_branch);
                    }
                }
                Region::While { body, .. }
                | Region::RepeatUntil { body, .. }
                | Region::NumericFor { body, .. }
                | Region::GenericFor { body, .. } => self.root(body),
                Region::Continue | Region::Break | Region::Return(_) => {}
            }
        }
    }

    /// Returns the first access to the storage in a statement list.
    fn stmts_access(&self, source: ValueId, stmts: &[Stmt]) -> Option<Access> {
        stmts.iter().find_map(|stmt| match stmt {
            Stmt::Bind {
                target: Place::Local(local),
                value,
            } if self.locals[*local].source == source => {
                Some(if StorageUse::in_expr(self.locals, source, value) {
                    Access::Other
                } else {
                    Access::Overwrite
                })
            }
            stmt => StorageUse::in_stmt(self.locals, source, stmt).then_some(Access::Other),
        })
    }

    /// Returns the first access to the storage in one flattened region.
    fn region_access(&self, source: ValueId, region: &Region) -> Option<Access> {
        match region {
            Region::Block { stmts, .. } => self.stmts_access(source, stmts),
            Region::Sequence(nodes) => nodes
                .iter()
                .find_map(|node| self.region_access(source, node)),
            Region::Continue | Region::Break | Region::Return(_) => Some(Access::Other),
            region => StorageUse::in_region(self.locals, source, region).then_some(Access::Other),
        }
    }
}

/// Removes the initializers found by [`DeadInitializers`].
struct InitializerRemover<'a> {
    dead: &'a HashSet<*const Stmt>,
}

impl VisitorMut for InitializerRemover<'_> {
    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        stmts.retain(|stmt| !self.dead.contains(&std::ptr::from_ref(stmt)));
        walk_stmts_mut(self, stmts);
    }
}
