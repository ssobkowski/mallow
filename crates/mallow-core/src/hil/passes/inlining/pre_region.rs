use std::collections::{HashMap, HashSet};

use super::common::{expr_read_symbols, replace_symbol_in_expr, stmt_written_symbols};
use crate::hil::cflow::cfg::{Block, BlockExit, ControlFlowGraph};
use crate::hil::cflow::graph::GraphView;
use crate::hil::ir::{Capture, Expr, Stmt};
use crate::hil::lifter::ssa::{FunctionSymbols, SymbolId};
use crate::hil::visitor::{Visitor, walk_expr};
use crate::scopes::Scope;

#[derive(Debug, Clone, Default)]
struct SymbolFacts {
    writes: usize,
    reads: usize,
    /// If true, this symbol is disqualified from pure CFG inlining.
    disqualified: bool,
}

impl SymbolFacts {
    /// Creates facts for a symbol whose value cannot be represented by one plain RHS.
    pub fn disqualified() -> Self {
        Self {
            writes: 0,
            reads: 0,
            disqualified: true,
        }
    }
}

#[derive(Default)]
struct Analyzer {
    facts: Scope<SymbolId, SymbolFacts>,
}

impl Analyzer {
    fn seed_symbols(&mut self, params: &[SymbolId], upvalues: &[SymbolId]) {
        // Parameters are inlined into themselves - essentially they need to be present
        // in the vars array (see `is_inlinable_rhs`) and because they have no underlying
        // value this just allows us to skip bindings like `v{N} = p{N}`.
        for param in params {
            self.facts.declare(*param, SymbolFacts::default());
        }

        for upvalue in upvalues {
            self.facts.declare(*upvalue, SymbolFacts::disqualified());
        }
    }

    fn note_write(&mut self, sym: SymbolId) {
        let fact = self.facts.entry(sym).or_default();
        fact.writes += 1;
    }

    fn disqualify_written_symbol(&mut self, sym: SymbolId) {
        // Loop variables and tuple-assignment targets are real writes, but this
        // pre-region pass cannot model their source value as one reusable RHS.
        let fact = self
            .facts
            .entry(sym)
            .or_insert_with(SymbolFacts::disqualified);
        fact.writes += 1;
        fact.disqualified = true;
    }
}

impl Visitor for Analyzer {
    fn visit_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            match &stmt {
                Stmt::Assign {
                    left: Expr::Symbol(sym),
                    value,
                } => {
                    self.note_write(*sym);
                    self.visit_expr(value);
                    continue;
                }
                Stmt::AssignMany { left, values } => {
                    // Block all tuple-assigns from being inlined. This can only be done in the
                    // post region inlining pass.
                    let symbols = left.iter().filter_map(|lv| {
                        if let Expr::Symbol(sym) = lv {
                            Some(sym)
                        } else {
                            None
                        }
                    });
                    for sym in symbols {
                        self.disqualify_written_symbol(*sym);
                    }

                    self.visit_value_pack(values);
                    continue;
                }
                _ => {
                    self.visit_stmt(stmt);
                }
            }
        }
    }

    fn visit_expr(&mut self, expr: &Expr) {
        if let Expr::Symbol(sym) = expr
            && let Some(fact) = self.facts.get_mut(sym)
        {
            fact.reads += 1;
            return;
        }

        walk_expr(self, expr);
    }

    fn visit_capture(&mut self, _: usize, capture: Capture) {
        if let Capture::Copy(symbol) = capture {
            self.facts
                .entry(symbol)
                .or_insert_with(SymbolFacts::disqualified)
                .disqualified = true;
        }
    }

    fn visit_block_exit(&mut self, exit: &BlockExit) {
        match exit {
            BlockExit::CondJump { cond, .. } => self.visit_expr(cond),
            BlockExit::FornPrep {
                var,
                start,
                end,
                step,
                ..
            } => {
                self.disqualify_written_symbol(*var);
                self.visit_expr(start);
                self.visit_expr(end);
                self.visit_expr(step);
            }
            BlockExit::ForgPrep { exprs, .. } => {
                for expr in exprs {
                    self.visit_expr(expr);
                }
            }
            BlockExit::ForgLoop { vars, .. } => {
                for var in vars {
                    self.disqualify_written_symbol(*var);
                }
            }
            BlockExit::Return(values) => {
                self.visit_value_pack(values);
            }
            BlockExit::Jump(_) | BlockExit::Fallthrough(_) | BlockExit::FornLoop { .. } => {}
        }
    }
}

impl Analyzer {
    pub fn analyze_cfg(
        cfg: &ControlFlowGraph,
        symbols: &FunctionSymbols,
    ) -> Scope<SymbolId, SymbolFacts> {
        let span = tracing::info_span!("pre_region_inlining_analyze", block_count = cfg.len(),);
        let _enter = span.enter();

        let mut analyzer = Analyzer::default();
        analyzer.seed_symbols(symbols.params(), symbols.upvalues());
        analyzer.visit_graph(cfg);

        analyzer.facts
    }
}

/// Rewrites CFG assignments using the facts collected for one function.
struct Inliner {
    facts: Scope<SymbolId, SymbolFacts>,
    was_changed: bool,
}

/// Stores replacements available in one basic block.
///
/// The reverse dependency map makes a write invalidate only the replacements
/// which read that symbol. A full scan after every assignment makes long basic
/// blocks quadratic.
#[derive(Default)]
struct AvailableValues {
    values: HashMap<SymbolId, Expr>,
    dependencies: HashMap<SymbolId, HashSet<SymbolId>>,
    dependents: HashMap<SymbolId, HashSet<SymbolId>>,
}

impl AvailableValues {
    /// Returns the replacements currently available for substitution.
    fn values(&self) -> &HashMap<SymbolId, Expr> {
        &self.values
    }

    /// Adds one replacement and indexes every symbol it reads.
    fn insert(&mut self, sym: SymbolId, value: Expr) {
        debug_assert!(!self.values.contains_key(&sym));

        let dependencies = expr_read_symbols(&value);
        for dependency in &dependencies {
            self.dependents.entry(*dependency).or_default().insert(sym);
        }
        self.dependencies.insert(sym, dependencies);
        self.values.insert(sym, value);
    }

    /// Invalidates replacements affected by the written symbols.
    fn invalidate(&mut self, written: impl IntoIterator<Item = SymbolId>) {
        let mut pending: Vec<_> = written.into_iter().collect();
        let mut visited = HashSet::new();

        while let Some(sym) = pending.pop() {
            if !visited.insert(sym) {
                continue;
            }

            if let Some(dependents) = self.dependents.remove(&sym) {
                pending.extend(dependents);
            }
            self.remove(sym);
        }
    }

    /// Removes one replacement from both dependency directions.
    fn remove(&mut self, sym: SymbolId) {
        if self.values.remove(&sym).is_none() {
            return;
        }

        let Some(dependencies) = self.dependencies.remove(&sym) else {
            return;
        };
        for dependency in dependencies {
            let remove_entry = self
                .dependents
                .get_mut(&dependency)
                .is_some_and(|dependents| {
                    dependents.remove(&sym);
                    dependents.is_empty()
                });
            if remove_entry {
                self.dependents.remove(&dependency);
            }
        }
    }
}

impl Inliner {
    /// Creates an inliner from one function analysis.
    fn with_facts(facts: Scope<SymbolId, SymbolFacts>) -> Self {
        Self {
            facts,
            was_changed: false,
        }
    }

    /// Rewrites every block in one CFG sweep.
    fn visit_cfg(&mut self, cfg: &mut ControlFlowGraph) {
        let span = tracing::info_span!("pre_region_inlining_rewrite", block_count = cfg.len());
        let _enter = span.enter();

        for block in cfg.blocks_mut() {
            self.was_changed |= self.inline_block(block.stmts_mut());
            self.was_changed |= self.fold_trailing_assignments_into_cond_jump(block);
        }
    }

    /// Returns whether one assignment is safe to substitute.
    fn is_inline_candidate(&self, sym: SymbolId, rhs: &Expr) -> bool {
        let Some(fact) = self.facts.get(&sym) else {
            return false;
        };

        if fact.disqualified || fact.writes != 1 || fact.reads != 1 || rhs.reads_symbol(&sym) {
            return false;
        }

        match rhs {
            // A symbol can be inlined only when its value is stable for the whole function.
            // Otherwise a copied temporary can capture an old value and become wrong after
            // substitutions, for example when doing a swap via a temporary.
            Expr::Symbol(sym) => self
                .facts
                .get(sym)
                .is_some_and(|v| !v.disqualified && v.writes == 1),
            other => other.is_pure(),
        }
    }

    /// Rewrites assignments used later in the same block.
    fn inline_block(&mut self, stmts: &mut Vec<Stmt>) -> bool {
        let mut available = AvailableValues::default();
        let mut removable = HashSet::new();

        for stmt in stmts.iter_mut() {
            // Consume currently available aliases before killing lvalues so
            // self-overwriting statements still see the old incoming value.
            substitute_in_stmt_rvalues(stmt, available.values(), &mut removable);
            kill_lvalues(stmt, &mut available);

            if let Stmt::Assign {
                left: Expr::Symbol(sym),
                value,
            } = stmt
                && self.is_inline_candidate(*sym, value)
            {
                available.insert(*sym, value.clone());
            }
        }

        if removable.is_empty() {
            return false;
        }

        let mut changed = false;
        stmts.retain(|stmt| {
            let remove = matches!(
                stmt,
                Stmt::Assign {
                    left: Expr::Symbol(sym),
                    ..
                } if removable.contains(sym)
            );
            if remove {
                changed = true;
            }
            !remove
        });
        changed
    }

    /// Moves trailing assignments into a conditional block exit.
    fn fold_trailing_assignments_into_cond_jump(&mut self, block: &mut Block) -> bool {
        let BlockExit::CondJump { cond, .. } = block.exit() else {
            return false;
        };

        let mut condition = cond.clone();
        let mut removable = HashSet::new();

        for stmt in block.stmts().iter().rev() {
            let Stmt::Assign {
                left: Expr::Symbol(sym),
                value,
            } = stmt
            else {
                return false;
            };

            if !self.is_inline_candidate(*sym, value) {
                return false;
            }

            let replacement_count = replace_symbol_in_expr(&mut condition, *sym, value);
            if replacement_count == 0 {
                return false;
            }
            if !value.is_pure() && replacement_count > 1 {
                return false;
            }

            removable.insert(*sym);
        }

        let BlockExit::CondJump { cond, .. } = block.exit_mut() else {
            return false;
        };
        if *cond == condition {
            return false;
        }
        *cond = condition;

        block.stmts_mut().retain(|stmt| {
            !matches!(
                stmt,
                Stmt::Assign {
                    left: Expr::Symbol(sym),
                    ..
                } if removable.contains(sym)
            )
        });
        true
    }
}

/// Substitutes available values only in statement rvalues.
fn substitute_in_stmt_rvalues(
    stmt: &mut Stmt,
    available: &HashMap<SymbolId, Expr>,
    removable: &mut HashSet<SymbolId>,
) {
    // Lvalues are handled after substitution because reads and writes in one
    // statement have different ordering rules.
    match stmt {
        Stmt::Assign { value, .. } => substitute_available_expr(value, available, removable),
        Stmt::AssignMany { values, .. } | Stmt::SetList { values, .. } => {
            for value in values.iter_mut() {
                substitute_available_expr(value, available, removable);
            }
        }
        Stmt::Call(expr)
        | Stmt::OpenCell { value: expr, .. }
        | Stmt::StoreCell { value: expr, .. } => {
            substitute_available_expr(expr, available, removable)
        }
        Stmt::LoadCell { .. } | Stmt::Phi(_) => {}
    }
}

/// Substitutes available values in one expression until the result is stable.
fn substitute_available_expr(
    expr: &mut Expr,
    available: &HashMap<SymbolId, Expr>,
    removable: &mut HashSet<SymbolId>,
) {
    loop {
        let mut changed = false;
        for sym in expr_read_symbols(expr) {
            let Some(replacement) = available.get(&sym) else {
                continue;
            };

            if replace_symbol_in_expr(expr, sym, replacement) > 0 {
                removable.insert(sym);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }
}

/// Invalidates block-local replacements affected by one statement.
fn kill_lvalues(stmt: &Stmt, available: &mut AvailableValues) {
    // Available expressions capture the value of every symbol they read at the
    // assignment point. Any later write to one of those inputs invalidates the
    // expression, even when the expression itself is pure.
    available.invalidate(stmt_written_symbols(stmt));
}

/// Runs one exhaustive pre-region inlining sweep.
pub fn run(cfg: &mut ControlFlowGraph, symbols: &FunctionSymbols) -> bool {
    // Every candidate has one write and one read. Substitution moves RHS reads
    // to that sole use, so facts for every remaining symbol stay unchanged.
    let facts = Analyzer::analyze_cfg(cfg, symbols);
    let mut inliner = Inliner::with_facts(facts);
    inliner.visit_cfg(cfg);
    inliner.was_changed
}
