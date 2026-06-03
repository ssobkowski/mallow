use std::collections::{HashMap, HashSet};

use crate::{
    hil::{
        cflow::cfg::{Block, BlockExit, ControlFlowGraph},
        cflow::graph::GraphView,
        ir::{HilExpr, HilStmt},
        lifter::ssa::SymbolId,
        visitor::{Visitor, VisitorMut, walk_expr, walk_expr_mut},
    },
    scopes::Scope,
};

#[derive(Debug, Clone, Default)]
pub struct SymbolFacts {
    pub writes: usize,
    pub reads: usize,
    /// If true, this symbol is disqualified from pure CFG inlining.
    pub disqualified: bool,
    /// The expression assigned by the symbol's only plain assignment, if known.
    pub rhs: Option<HilExpr>,
}

impl SymbolFacts {
    /// Creates facts for a symbol seen only through reads or non-assignment metadata so far.
    pub fn unknown() -> Self {
        Self::default()
    }

    /// Creates facts for a plain `sym = rhs` assignment.
    pub fn assigned(rhs: HilExpr) -> Self {
        Self {
            writes: 1,
            reads: 0,
            disqualified: false,
            rhs: Some(rhs),
        }
    }

    /// Creates facts for a symbol whose value cannot be represented by one plain RHS.
    pub fn disqualified() -> Self {
        Self {
            writes: 0,
            reads: 0,
            disqualified: true,
            rhs: None,
        }
    }
}

#[derive(Default)]
pub struct Analyzer {
    facts: Scope<SymbolId, SymbolFacts>,
}

impl Analyzer {
    fn seed_symbols(&mut self, params: &[SymbolId], upvalues: &[SymbolId]) {
        // Parameters are inlined into themselves - essentially they need to be present
        // in the vars array (see `is_inlinable_rhs`) and because they have no underlying
        // value this just allows us to skip bindings like `v{N} = p{N}`.
        for param in params {
            self.facts
                .declare(*param, SymbolFacts::assigned(HilExpr::Symbol(*param)));
        }

        for upvalue in upvalues {
            self.facts.declare(*upvalue, SymbolFacts::disqualified());
        }
    }

    fn note_plain_assignment(&mut self, sym: SymbolId, rhs: &HilExpr) {
        let fact = self.facts.entry(sym).or_insert_with(SymbolFacts::unknown);
        fact.writes += 1;
        fact.rhs = Some(rhs.clone());
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
        fact.rhs = None;
    }

    fn visit_cfg_exit(&mut self, exit: &BlockExit) {
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
                for value in values {
                    self.visit_expr(value);
                }
            }
            BlockExit::Jump(_) | BlockExit::Fallthrough(_) | BlockExit::FornLoop { .. } => {}
        }
    }
}

impl Visitor for Analyzer {
    fn visit_block(&mut self, stmts: &[HilStmt]) {
        for stmt in stmts {
            match &stmt {
                HilStmt::Assign {
                    left: HilExpr::Symbol(sym),
                    value,
                } => {
                    self.note_plain_assignment(*sym, value);
                    self.visit_expr(value);
                    continue;
                }
                HilStmt::AssignMany { left, value } => {
                    // Block all tuple-assigns from being inlined. This can only be done in the
                    // post region inlining pass.
                    let symbols = left.iter().filter_map(|lv| {
                        if let HilExpr::Symbol(sym) = lv {
                            Some(sym)
                        } else {
                            None
                        }
                    });
                    for sym in symbols {
                        self.disqualify_written_symbol(*sym);
                    }

                    self.visit_expr(value);
                    continue;
                }
                _ => {
                    self.visit_stmt(stmt);
                }
            }
        }
    }

    fn visit_expr(&mut self, expr: &HilExpr) {
        if let HilExpr::Symbol(sym) = expr
            && let Some(fact) = self.facts.get_mut(sym)
        {
            fact.reads += 1;
            return;
        }

        walk_expr(self, expr);
    }

    fn visit_capture(&mut self, _: usize, sym: SymbolId) {
        self.facts
            .entry(sym)
            .or_insert_with(SymbolFacts::disqualified)
            .disqualified = true;
    }
}

impl Analyzer {
    pub fn analyze_cfg(cfg: &ControlFlowGraph) -> Scope<SymbolId, SymbolFacts> {
        let span = tracing::info_span!("pre_region_inlining_analyze", block_count = cfg.len(),);
        let _enter = span.enter();

        let mut analyzer = Analyzer::default();
        analyzer.seed_symbols(cfg.params(), cfg.upvalues());

        for block in cfg.blocks() {
            analyzer.visit_block(block.stmts());
            analyzer.visit_cfg_exit(block.exit());
        }

        analyzer.facts
    }
}

struct Inliner {
    facts: Scope<SymbolId, SymbolFacts>,
    was_changed: bool,
    stats: RewriteStats,
}

#[derive(Debug, Default)]
struct RewriteStats {
    blocks_visited: usize,
    statements_visited: usize,
    available_insertions: usize,
    substitution_attempts: usize,
    successful_substitutions: usize,
    removed_statements: usize,
    trailing_condition_checks: usize,
    folded_trailing_conditions: usize,
}

#[derive(Debug, Default)]
struct SubstitutionStats {
    attempts: usize,
    successes: usize,
}

impl SubstitutionStats {
    fn add(&mut self, other: Self) {
        self.attempts += other.attempts;
        self.successes += other.successes;
    }
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
    fn with_facts(facts: Scope<SymbolId, SymbolFacts>) -> Self {
        Self {
            facts,
            was_changed: false,
            stats: RewriteStats::default(),
        }
    }

    fn visit_cfg(&mut self, cfg: &mut ControlFlowGraph) {
        let span = tracing::info_span!(
            "pre_region_inlining_rewrite",
            block_count = cfg.len(),
            blocks_visited = tracing::field::Empty,
            statements_visited = tracing::field::Empty,
            available_insertions = tracing::field::Empty,
            substitution_attempts = tracing::field::Empty,
            successful_substitutions = tracing::field::Empty,
            removed_statements = tracing::field::Empty,
            trailing_condition_checks = tracing::field::Empty,
            folded_trailing_conditions = tracing::field::Empty,
        );
        let _enter = span.enter();

        for block in cfg.blocks_mut() {
            self.was_changed |= self.inline_block(block.stmts_mut());
            self.was_changed |= self.fold_trailing_assignments_into_cond_jump(block);
        }

        span.record("blocks_visited", self.stats.blocks_visited);
        span.record("statements_visited", self.stats.statements_visited);
        span.record("available_insertions", self.stats.available_insertions);
        span.record("substitution_attempts", self.stats.substitution_attempts);
        span.record(
            "successful_substitutions",
            self.stats.successful_substitutions,
        );
        span.record("removed_statements", self.stats.removed_statements);
        span.record(
            "trailing_condition_checks",
            self.stats.trailing_condition_checks,
        );
        span.record(
            "folded_trailing_conditions",
            self.stats.folded_trailing_conditions,
        );
    }

    fn is_inline_candidate(&self, sym: SymbolId, rhs: &HilExpr) -> bool {
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
            HilExpr::Symbol(sym) => self
                .facts
                .get(sym)
                .is_some_and(|v| !v.disqualified && v.writes == 1),
            other => other.is_pure(),
        }
    }

    fn inline_block(&mut self, stmts: &mut Vec<HilStmt>) -> bool {
        self.stats.blocks_visited += 1;
        self.stats.statements_visited += stmts.len();
        let mut available = HashMap::new();
        let mut removable = HashSet::new();

        for stmt in stmts.iter_mut() {
            // Consume currently available aliases before killing lvalues so
            // self-overwriting statements still see the old incoming value.
            let substitution_stats = substitute_in_stmt_rvalues(stmt, &available, &mut removable);
            self.stats.substitution_attempts += substitution_stats.attempts;
            self.stats.successful_substitutions += substitution_stats.successes;
            kill_lvalues(stmt, &mut available);

            if let HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                value,
            } = stmt
                && self.is_inline_candidate(*sym, value)
            {
                available.insert(*sym, value.clone());
                self.stats.available_insertions += 1;
            }
        }

        if removable.is_empty() {
            return false;
        }

        let mut changed = false;
        stmts.retain(|stmt| {
            let remove = matches!(
                stmt,
                HilStmt::Assign {
                    left: HilExpr::Symbol(sym),
                    ..
                } if removable.contains(sym)
            );
            if remove {
                changed = true;
            }
            !remove
        });
        self.stats.removed_statements += removable.len();
        changed
    }

    fn fold_trailing_assignments_into_cond_jump(&mut self, block: &mut Block) -> bool {
        self.stats.trailing_condition_checks += 1;
        let BlockExit::CondJump { cond, .. } = block.exit() else {
            return false;
        };

        let mut condition = cond.clone();
        let mut removable = HashSet::new();

        for stmt in block.stmts().iter().rev() {
            let HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                value,
            } = stmt
            else {
                return false;
            };

            if !self.is_inline_candidate(*sym, value) {
                return false;
            }

            let replacement_count = replace_symbol(&mut condition, *sym, value);
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

        let removed = removable.len();
        block.stmts_mut().retain(|stmt| {
            !matches!(
                stmt,
                HilStmt::Assign {
                    left: HilExpr::Symbol(sym),
                    ..
                } if removable.contains(sym)
            )
        });
        self.stats.removed_statements += removed;
        self.stats.folded_trailing_conditions += 1;

        true
    }
}

fn substitute_in_stmt_rvalues(
    stmt: &mut HilStmt,
    available: &HashMap<SymbolId, HilExpr>,
    removable: &mut HashSet<SymbolId>,
) -> SubstitutionStats {
    // Only rvalues are rewritten. Lvalues are handled separately by
    // `kill_lvalues`, because reads and writes in one statement have different
    // ordering semantics for this local dataflow pass.
    match stmt {
        HilStmt::Assign { value, .. } | HilStmt::AssignMany { value, .. } => {
            substitute_available_expr(value, available, removable)
        }
        HilStmt::SetList { values, .. } => {
            let mut stats = SubstitutionStats::default();
            for value in values {
                stats.add(substitute_available_expr(value, available, removable));
            }
            stats
        }
        HilStmt::Call(expr) => substitute_available_expr(expr, available, removable),
        HilStmt::Phi(_) => SubstitutionStats::default(),
    }
}

fn substitute_available_expr(
    expr: &mut HilExpr,
    available: &HashMap<SymbolId, HilExpr>,
    removable: &mut HashSet<SymbolId>,
) -> SubstitutionStats {
    let mut stats = SubstitutionStats::default();
    // Re-run until stable so chains like `a = 1; b = a; call(b)` collapse in
    // this block without needing another outer pass iteration.
    loop {
        let mut changed = false;

        for (sym, replacement) in available {
            stats.attempts += 1;
            if replace_symbol(expr, *sym, replacement) > 0 {
                removable.insert(*sym);
                stats.successes += 1;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }
    stats
}

fn kill_lvalues(stmt: &HilStmt, available: &mut HashMap<SymbolId, HilExpr>) {
    let written = written_symbols(stmt);
    if written.is_empty() {
        return;
    }

    // Available expressions capture the value of every symbol they read at the
    // assignment point. Any later write to one of those inputs invalidates the
    // expression, even when the expression itself is pure.
    available.retain(|sym, replacement| {
        !written.contains(sym)
            && !written
                .iter()
                .any(|written| replacement.reads_symbol(written))
    });
}

fn written_symbols(stmt: &HilStmt) -> Vec<SymbolId> {
    match stmt {
        HilStmt::Assign {
            left: HilExpr::Symbol(sym),
            ..
        } => vec![*sym],
        HilStmt::Assign { .. } => Vec::new(),
        HilStmt::AssignMany { left, .. } => left
            .iter()
            .filter_map(|lvalue| match lvalue {
                HilExpr::Symbol(sym) => Some(*sym),
                _ => None,
            })
            .collect(),
        HilStmt::SetList { table, .. } => vec![*table],
        HilStmt::Call(_) => Vec::new(),
        HilStmt::Phi(_) => {
            unreachable!("phi nodes should have been unfolded at this point")
        }
    }
}

fn replace_symbol(expr: &mut HilExpr, sym: SymbolId, replacement: &HilExpr) -> usize {
    let mut substituter = SymbolSubstituter {
        sym,
        replacement,
        change_count: 0,
    };
    substituter.visit_expr(expr);
    substituter.change_count
}

pub fn run(cfg: &mut ControlFlowGraph) -> bool {
    let mut changed = false;
    let mut iteration = 0;
    loop {
        iteration += 1;
        let span = tracing::info_span!(
            "pre_region_inlining_iteration",
            iteration,
            changed = tracing::field::Empty,
        );
        let _enter = span.enter();

        let facts = Analyzer::analyze_cfg(cfg);
        let mut inliner = Inliner::with_facts(facts);
        inliner.visit_cfg(cfg);
        span.record("changed", inliner.was_changed);

        if !inliner.was_changed {
            break;
        }
        changed = true
    }

    changed
}
