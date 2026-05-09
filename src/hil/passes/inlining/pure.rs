use std::collections::{HashSet, VecDeque};

use crate::{
    common::Spanned,
    hil::{
        cflow::cfg::{Block, BlockExit, ControlFlowGraph},
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
        passes::inlining::common::{Analyzer, Var},
        visitor::{VisitorMut, walk_block_mut, walk_expr_mut},
    },
    scopes::Scope,
};

struct Inliner {
    vars: Scope<SymbolId, Var>,
    inlined_symbols: HashSet<SymbolId>,
    was_changed: bool,
}

struct SymbolSubstituter<'a> {
    sym: SymbolId,
    replacement: &'a HilExpr,
    change_count: usize,
}

impl VisitorMut for SymbolSubstituter<'_> {
    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Symbol(sym) = expr
            && *sym == self.sym
        {
            *expr = self.replacement.clone();
            self.change_count += 1;
            return;
        }

        walk_expr_mut(self, expr);
    }
}

impl Inliner {
    fn with_vars(vars: Scope<SymbolId, Var>) -> Self {
        Self {
            vars,
            inlined_symbols: HashSet::new(),
            was_changed: false,
        }
    }

    fn can_inline(&self, var: &Var) -> bool {
        !var.disqualified
            && var.write_count == 1
            && var.read_count == 1
            && self.is_inlinable_rhs(&var.expr)
            && var.expr.truthiness().is_none()
    }

    fn is_inlinable_rhs(&self, expr: &HilExpr) -> bool {
        match expr {
            // A symbol can be inlined only when its value is stable for the whole function.
            // Otherwise a copied temporary can capture an old value and become wrong after
            // substitutions (for example, when doing a swap via a temporary).
            HilExpr::Symbol(sym) => self
                .vars
                .get(sym)
                .is_some_and(|v| !v.disqualified && v.write_count == 1),
            HilExpr::Number(_)
            | HilExpr::String(_)
            | HilExpr::Bool(_)
            | HilExpr::Global(_)
            | HilExpr::Import(_)
            | HilExpr::Nil => true,
            HilExpr::Binary { lhs, rhs, .. }
                if self.is_inlinable_rhs(lhs) && self.is_inlinable_rhs(rhs) =>
            {
                true
            }
            HilExpr::Unary { expr, .. } if self.is_inlinable_rhs(expr) => true,
            _ => false,
        }
    }

    fn visit_cfg(&mut self, cfg: &mut ControlFlowGraph) {
        let guard_blocks = self.loop_guard_blocks(cfg);

        for (block_idx, block) in cfg.blocks.iter_mut().enumerate() {
            if guard_blocks.contains(&block_idx) {
                self.visit_cfg_guard_block(block);
            } else {
                self.visit_cfg_exit(&mut block.exit);
            }
        }

        for block in &mut cfg.blocks {
            self.remove_inlined_cfg_assigns(&mut block.stmts);
        }
    }

    fn visit_cfg_guard_block(&mut self, block: &mut Block) {
        self.visit_cfg_exit(&mut block.exit);

        let Some((inlined, inlined_symbols)) = self.inline_condition_prelude(block) else {
            return;
        };

        if let BlockExit::CondJump { cond, .. } = &mut block.exit
            && *cond != inlined
        {
            *cond = inlined;
            self.inlined_symbols.extend(inlined_symbols);
            self.was_changed = true;
        }
    }

    fn loop_guard_blocks(&self, cfg: &ControlFlowGraph) -> HashSet<usize> {
        let mut guard_blocks = HashSet::new();
        let mut queue = VecDeque::new();

        for (pred, successors) in cfg.successors.iter().enumerate() {
            for &succ in successors {
                if cfg.idoms.dominates(succ, pred) && self.starts_condition_chain(cfg, succ) {
                    queue.push_back(succ);
                }
            }
        }

        while let Some(block_idx) = queue.pop_front() {
            if !guard_blocks.insert(block_idx) {
                continue;
            }

            let block = &cfg.blocks[block_idx];
            let BlockExit::CondJump { .. } = block.exit else {
                continue;
            };

            if self.inline_condition_prelude(block).is_none() {
                continue;
            }

            for target in block.exit.targets().into_iter().flatten() {
                queue.push_back(target);
            }
        }

        guard_blocks
    }

    fn starts_condition_chain(&self, cfg: &ControlFlowGraph, block_idx: usize) -> bool {
        let block = &cfg.blocks[block_idx];
        let BlockExit::CondJump { .. } = block.exit else {
            return false;
        };

        block.exit.targets().into_iter().flatten().any(|target| {
            let target_block = &cfg.blocks[target];
            matches!(target_block.exit, BlockExit::CondJump { .. })
                && self.inline_condition_prelude(target_block).is_some()
        })
    }

    fn inline_condition_prelude(&self, block: &Block) -> Option<(HilExpr, Vec<SymbolId>)> {
        let BlockExit::CondJump { cond, .. } = &block.exit else {
            return None;
        };

        let mut condition = cond.clone();
        let mut inlined_symbols = Vec::new();

        for stmt in block.stmts.iter().rev() {
            let HilStmt::Assign {
                left: HilExpr::Symbol(symbol),
                value,
            } = &stmt.node
            else {
                return None;
            };

            if value.reads_symbol(symbol) {
                return None;
            }

            let mut inlined = condition;
            let mut substituter = SymbolSubstituter {
                sym: *symbol,
                replacement: value,
                change_count: 0,
            };
            substituter.visit_expr(&mut inlined);
            if substituter.change_count == 0 {
                return None;
            }
            if !value.is_pure() && substituter.change_count > 1 {
                return None;
            }
            if !self.vars.get(symbol).is_some_and(|var| {
                !var.disqualified
                    && var.write_count == 1
                    && var.read_count == substituter.change_count
            }) {
                return None;
            }

            inlined_symbols.push(*symbol);
            condition = inlined;
        }

        Some((condition, inlined_symbols))
    }

    fn remove_inlined_cfg_assigns(&mut self, stmts: &mut Vec<Spanned<HilStmt>>) {
        stmts.retain(|stmt| {
            if let HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                ..
            } = &stmt.node
                && self.inlined_symbols.contains(sym)
            {
                return false;
            }

            true
        });
    }

    fn visit_cfg_exit(&mut self, exit: &mut BlockExit) {
        match exit {
            BlockExit::CondJump { cond, .. } => self.visit_expr(cond),
            // Pre-region pure inlining is deliberately limited to conditional
            // exits. Rewriting loop prep or return exits before structuring can
            // erase shapes the region reducer still relies on.
            BlockExit::Jump(_)
            | BlockExit::Fallthrough(_)
            | BlockExit::FornPrep { .. }
            | BlockExit::FornLoop { .. }
            | BlockExit::ForgPrep { .. }
            | BlockExit::ForgLoop { .. } => {}
            BlockExit::Return(_) => {}
        }
    }
}

impl VisitorMut for Inliner {
    fn visit_block(&mut self, stmts: &mut Vec<HilStmt>) {
        stmts.retain(|stmt| {
            if let HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                ..
            } = &stmt
                && let Some(v) = self.vars.get(sym)
                && self.can_inline(v)
            {
                // Remove the assignment as it's getting inlined
                self.was_changed = true;
                return false;
            }

            true
        });

        walk_block_mut(self, stmts);
    }

    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Symbol(sym) = expr
            && let Some(v) = self.vars.get(sym)
            && self.can_inline(v)
            && !v.expr.reads_symbol(sym)
        {
            self.was_changed = true;
            self.inlined_symbols.insert(*sym);
            *expr = v.expr.clone();

            self.visit_expr(expr);
            return;
        }

        walk_expr_mut(self, expr);
    }
}

pub fn run_cfg(cfg: &mut ControlFlowGraph) -> bool {
    let mut changed = false;
    loop {
        let vars = Analyzer::analyze_cfg(cfg);

        let mut inliner = Inliner::with_vars(vars);
        inliner.visit_cfg(cfg);

        if !inliner.was_changed {
            break;
        }
        changed = true
    }

    changed
}
