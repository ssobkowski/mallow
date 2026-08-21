//! NIR identity and FIR ownership verification.

use std::collections::{HashMap, HashSet};

use anyhow::{Result, bail, ensure};

use super::*;
use crate::ir;

impl Function {
    /// Verifies NIR identities and exact reachable FIR instruction ownership.
    pub(crate) fn verify(&self, fir: &ir::Function) -> Result<()> {
        ensure!(
            self.id == fir.proto,
            "NIR function prototype does not match FIR"
        );
        ensure!(
            self.upvalues == fir.upvalues,
            "NIR upvalue order does not match FIR"
        );
        ensure!(
            self.is_vararg == fir.is_vararg,
            "NIR vararg metadata does not match FIR"
        );
        for parameter in &self.params {
            ensure!(
                self.locals.get(*parameter).is_some(),
                "invalid parameter local"
            );
        }

        let mut verifier = Verifier {
            function: self,
            fir,
            origins: HashMap::new(),
        };
        for stmt in &self.prologue {
            verifier.stmt(stmt)?;
        }
        verifier.region(&self.body)?;

        for block in reachable_blocks(fir) {
            for (instr, value) in fir.blocks[block].instrs.iter().enumerate() {
                if matches!(value, ir::Instr::Phi { .. }) {
                    continue;
                }
                let origin = InstrOrigin { block, instr };
                let count = verifier.origins.get(&origin).copied().unwrap_or_default();
                ensure!(
                    count == 1,
                    "FIR bb{block} instruction {instr} has {count} NIR owners"
                );
            }
        }

        Ok(())
    }
}

/// NIR verifier state.
struct Verifier<'a> {
    /// NIR function being checked.
    function: &'a Function,
    /// FIR function providing provenance.
    fir: &'a ir::Function,
    /// Number of NIR owners for each FIR instruction.
    origins: HashMap<InstrOrigin, usize>,
}

impl Verifier<'_> {
    /// Records one FIR instruction owner.
    fn origin(&mut self, origin: InstrOrigin) -> Result<()> {
        let instr = self
            .fir
            .blocks
            .get(origin.block)
            .and_then(|block| block.instrs.get(origin.instr));
        ensure!(
            instr.is_some(),
            "NIR references invalid FIR instruction bb{}:{}",
            origin.block,
            origin.instr
        );
        ensure!(
            !matches!(instr, Some(ir::Instr::Phi { .. })),
            "NIR cannot claim ownership of a Phi instruction bb{}:{}",
            origin.block,
            origin.instr
        );
        *self.origins.entry(origin).or_default() += 1;
        Ok(())
    }

    /// Verifies one local reference.
    fn local(&self, local: LocalId) -> Result<()> {
        ensure!(
            self.function.locals.get(local).is_some(),
            "invalid NIR local"
        );
        Ok(())
    }

    /// Verifies one pack-local reference.
    fn pack_local(&self, pack: PackLocalId) -> Result<()> {
        ensure!(self.function.packs.get(pack).is_some(), "invalid NIR pack");
        Ok(())
    }

    /// Verifies one cell reference.
    fn cell(&self, cell: CellId) -> Result<()> {
        ensure!(self.fir.cells.get(cell).is_some(), "invalid NIR cell");
        Ok(())
    }

    /// Verifies one expression tree.
    fn expr(&mut self, expr: &Expr) -> Result<()> {
        if let Some(origin) = expr.origin {
            self.origin(origin)?;
        }
        match &expr.kind {
            ExprKind::Local(local) => self.local(*local)?,
            ExprKind::Closure { captures, .. } => {
                for capture in captures {
                    match capture {
                        Capture::Copy(local) => self.local(*local)?,
                        Capture::Share(cell) => self.cell(*cell)?,
                    }
                }
            }
            ExprKind::GetTable { table, key } => {
                self.expr(table)?;
                self.expr(key)?;
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                self.expr(lhs)?;
                self.expr(rhs)?;
            }
            ExprKind::Unary { value, .. } => self.expr(value)?,
            ExprKind::Concat(values) => {
                for value in values {
                    self.expr(value)?;
                }
            }
            ExprKind::Select {
                condition,
                then_value,
                else_value,
            } => {
                self.expr(condition)?;
                self.expr(then_value)?;
                self.expr(else_value)?;
            }
            ExprKind::Project { pack, .. } => self.pack_expr(pack)?,
            ExprKind::LoadCell(cell) => self.cell(*cell)?,
            ExprKind::Constant(_) | ExprKind::GetGlobal(_) | ExprKind::NewTable => {}
        }
        Ok(())
    }

    /// Verifies one pack expression tree.
    fn pack_expr(&mut self, pack: &PackExpr) -> Result<()> {
        if let Some(origin) = pack.origin {
            self.origin(origin)?;
        }
        match &pack.kind {
            PackExprKind::Local(local) => self.pack_local(*local)?,
            PackExprKind::Values { head, tail } => {
                for value in head {
                    self.expr(value)?;
                }
                if let Some(tail) = tail {
                    self.pack_expr(tail)?;
                }
            }
            PackExprKind::Call { function, args } => {
                self.expr(function)?;
                self.pack_expr(args)?;
            }
            PackExprKind::MethodCall { object, args, .. } => {
                self.expr(object)?;
                self.pack_expr(args)?;
            }
            PackExprKind::VarArgs => {}
        }
        Ok(())
    }

    /// Verifies one writable place.
    fn place(&mut self, place: &Place) -> Result<()> {
        match place {
            Place::Local(local) => self.local(*local)?,
            Place::Cell(cell) => self.cell(*cell)?,
            Place::Table { table, key } => {
                self.expr(table)?;
                self.expr(key)?;
            }
            Place::Global(_) | Place::Discard => {}
        }
        Ok(())
    }

    /// Verifies one statement.
    fn stmt(&mut self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Bind {
                origin,
                target,
                value,
            } => {
                if let Some(origin) = origin {
                    self.origin(*origin)?;
                }
                self.place(target)?;
                self.expr(value)?;
            }
            Stmt::BindMany { .. } => {
                bail!("BindMany is constructed by NIR passes after verification")
            }
            Stmt::Eval { .. } => {
                bail!("Eval is constructed by NIR passes after verification")
            }
            Stmt::BindPack { local, value } => {
                self.pack_local(*local)?;
                self.pack_expr(value)?;
            }
            Stmt::OpenCell {
                origin,
                cell,
                value,
            } => {
                self.origin(*origin)?;
                self.cell(*cell)?;
                self.expr(value)?;
            }
            Stmt::SetList {
                origin,
                table,
                values,
                ..
            } => {
                self.origin(*origin)?;
                self.expr(table)?;
                self.pack_expr(values)?;
            }
        }
        Ok(())
    }

    /// Verifies one nested control region.
    fn region(&mut self, region: &Region) -> Result<()> {
        match region {
            Region::Block { origin, stmts } => {
                ensure!(
                    self.fir.blocks.get(*origin).is_some(),
                    "invalid block origin"
                );
                for stmt in stmts {
                    self.stmt(stmt)?;
                }
            }
            Region::Sequence(nodes) => {
                for node in nodes {
                    self.region(node)?;
                }
            }
            Region::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition)?;
                self.region(then_branch)?;
                if let Some(else_branch) = else_branch {
                    self.region(else_branch)?;
                }
            }
            Region::While { condition, body } | Region::RepeatUntil { condition, body } => {
                self.expr(condition)?;
                self.region(body)?;
            }
            Region::NumericFor {
                variable,
                start,
                end,
                step,
                body,
            } => {
                self.local(*variable)?;
                self.expr(start)?;
                self.expr(end)?;
                self.expr(step)?;
                self.region(body)?;
            }
            Region::GenericFor {
                variables,
                values,
                body,
            } => {
                for variable in variables {
                    self.local(*variable)?;
                }
                for value in values {
                    self.expr(value)?;
                }
                self.region(body)?;
            }
            Region::Return(values) => self.pack_expr(values)?,
            Region::Continue | Region::Break => {}
        }
        Ok(())
    }
}

/// Returns all FIR blocks reachable from the function entry.
fn reachable_blocks(function: &ir::Function) -> HashSet<usize> {
    let mut reachable = HashSet::new();
    let mut pending = vec![0];
    while let Some(block) = pending.pop() {
        if !reachable.insert(block) {
            continue;
        }
        pending.extend(exit_targets(&function.blocks[block].exit));
    }
    reachable
}

/// Returns successor targets of one FIR block exit.
fn exit_targets(exit: &ir::BlockExit) -> Vec<usize> {
    match exit {
        ir::BlockExit::Fallthrough(target) | ir::BlockExit::Jump(target) => vec![*target],
        ir::BlockExit::Branch {
            then_block,
            else_block,
            ..
        }
        | ir::BlockExit::NumericFor {
            body_block: then_block,
            exit_block: else_block,
            ..
        }
        | ir::BlockExit::NumericForLoop {
            body_block: then_block,
            exit_block: else_block,
        }
        | ir::BlockExit::GenericForLoop {
            body_block: then_block,
            exit_block: else_block,
            ..
        } => vec![*then_block, *else_block],
        ir::BlockExit::GenericFor { body_block, .. } => vec![*body_block],
        ir::BlockExit::Return(_) => Vec::new(),
    }
}
