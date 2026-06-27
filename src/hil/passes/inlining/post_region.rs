use std::collections::{BTreeSet, HashMap, HashSet};

use smallvec::{SmallVec, smallvec};

use crate::hil::{
    ReturnArity, StructuredFunction,
    cflow::region::RegionNode,
    ir::{HilExpr, HilStmt, HilTableItem, PhiNode},
    lifter::ssa::SymbolId,
    passes::return_arity::luau_libfunc_arity,
    visitor::{Visitor, walk_expr},
};

use super::common::{
    count_symbol_reads_in_expr, count_symbol_reads_in_stmt, expr_read_symbols, region_read_symbols,
    replace_symbol_in_expr, replace_symbol_in_stmt, stmt_writes_symbol,
};

#[derive(Debug, Default)]
struct BlockSummary {
    stmt_reads: Vec<HashSet<SymbolId>>,
}

impl BlockSummary {
    fn new(stmts: &[HilStmt]) -> Self {
        let mut summary = Self::default();
        for stmt in stmts {
            let stmt_summary = StmtSummary::new(stmt);
            summary.stmt_reads.push(stmt_summary.reads);
        }
        summary
    }

    fn reads_in_stmt(&self, idx: usize) -> impl Iterator<Item = SymbolId> + '_ {
        self.stmt_reads[idx].iter().copied()
    }
}

#[derive(Debug, Default)]
struct BlockSourceIndex {
    source_positions: HashMap<SymbolId, Vec<usize>>,
}

impl BlockSourceIndex {
    /// Indexes plain assignment sources by symbol while preserving statement order.
    fn new(plain_sources: &[Option<SymbolId>]) -> Self {
        let mut index = Self::default();
        for (idx, sym) in plain_sources.iter().enumerate() {
            let Some(sym) = sym else {
                continue;
            };
            index.source_positions.entry(*sym).or_default().push(idx);
        }
        index
    }

    fn add_sources_in_range(
        &self,
        sym: SymbolId,
        lower_bound: usize,
        upper_bound: usize,
        candidates: &mut BTreeSet<usize>,
    ) {
        let Some(positions) = self.source_positions.get(&sym) else {
            return;
        };
        let start = positions.partition_point(|idx| *idx < lower_bound);
        for idx in &positions[start..] {
            if *idx >= upper_bound {
                break;
            }
            if *idx >= lower_bound {
                candidates.insert(*idx);
            }
        }
    }
}

#[derive(Debug, Default)]
struct StmtSummary {
    reads: HashSet<SymbolId>,
}

impl StmtSummary {
    fn new(stmt: &HilStmt) -> Self {
        let mut summary = Self::default();
        summary.visit_stmt(stmt);
        summary
    }
}

impl Visitor for StmtSummary {
    fn visit_stmt(&mut self, stmt: &HilStmt) {
        match stmt {
            HilStmt::Assign { left, value } => {
                if !matches!(left, HilExpr::Symbol(_)) {
                    self.visit_expr(left);
                }
                self.visit_expr(value);
            }
            HilStmt::AssignMany { left, value } => {
                for expr in left {
                    if !matches!(expr, HilExpr::Symbol(_)) {
                        self.visit_expr(expr);
                    }
                }
                self.visit_expr(value);
            }
            HilStmt::SetList { values, .. } => {
                for value in values {
                    self.visit_expr(value);
                }
            }
            HilStmt::Call(expr) => {
                self.visit_expr(expr);
            }
            HilStmt::Phi(_) => {
                unreachable!("phi nodes should have been unfolded at this point")
            }
        }
    }

    fn visit_expr(&mut self, expr: &HilExpr) {
        if let HilExpr::Symbol(sym) = expr {
            self.reads.insert(*sym);
            return;
        }

        walk_expr(self, expr);
    }

    fn visit_phi(&mut self, _: &PhiNode) {
        unreachable!("phi nodes should have been unfolded at this point")
    }
}

#[derive(Debug, Clone)]
struct TupleSource {
    targets: Vec<SymbolId>,
    value: HilExpr,
    write_pos: usize,
}

#[derive(Debug, Clone, Default)]
struct SymbolFacts {
    writes: usize,
    reads: usize,
    write_pos: Option<usize>,
    write_positions: Vec<usize>,
    read_positions: Vec<usize>,
    rhs: Option<HilExpr>,
    tuple: Option<TupleSource>,
    poisoned: bool,
}

impl SymbolFacts {
    fn note_read(&mut self, pos: usize) {
        self.reads += 1;
        self.read_positions.push(pos);
    }

    fn note_plain_write(&mut self, pos: usize, rhs: &HilExpr) {
        self.writes += 1;
        self.write_pos = Some(pos);
        self.write_positions.push(pos);
        self.rhs = Some(rhs.clone());
        self.tuple = None;
    }

    fn note_tuple_write(&mut self, source: TupleSource) {
        self.writes += 1;
        self.write_pos = Some(source.write_pos);
        self.write_positions.push(source.write_pos);
        self.rhs = None;
        self.tuple = Some(source);
    }

    fn note_unknown_write(&mut self, pos: usize) {
        self.writes += 1;
        self.write_pos = Some(pos);
        self.write_positions.push(pos);
        self.rhs = None;
        self.tuple = None;
        self.poisoned = true;
    }
}

#[derive(Debug, Default)]
struct Analyzer {
    facts: HashMap<SymbolId, SymbolFacts>,
    effect_positions: Vec<usize>,
    next_pos: usize,
}

impl Analyzer {
    fn analyze(fun: &StructuredFunction) -> Self {
        let span = tracing::info_span!(
            "post_region_inlining_analyze",
            proto = fun.proto.0,
            symbol_count = tracing::field::Empty,
            effect_count = tracing::field::Empty,
            position_count = tracing::field::Empty,
        );
        let _enter = span.enter();

        let mut analyzer = Self::default();
        for param in &fun.symbols.params {
            analyzer.facts.entry(*param).or_default().poisoned = true;
        }
        for upvalue in &fun.symbols.upvalues {
            analyzer.facts.entry(*upvalue).or_default().poisoned = true;
        }
        analyzer.visit_region(&fun.root);

        span.record("symbol_count", analyzer.facts.len());
        span.record("effect_count", analyzer.effect_positions.len());
        span.record("position_count", analyzer.next_pos);
        analyzer
    }

    fn alloc_pos(&mut self) -> usize {
        let pos = self.next_pos;
        self.next_pos += 1;
        pos
    }

    fn note_effect_at(&mut self, pos: usize) {
        self.effect_positions.push(pos);
    }

    fn note_write(&mut self, sym: SymbolId) -> usize {
        let pos = self.alloc_pos();
        self.facts.entry(sym).or_default().note_unknown_write(pos);
        pos
    }

    fn note_plain_assignment(&mut self, sym: SymbolId, rhs: &HilExpr) {
        self.visit_expr(rhs);
        let pos = self.alloc_pos();
        self.facts
            .entry(sym)
            .or_default()
            .note_plain_write(pos, rhs);
    }

    fn note_tuple_assignment(&mut self, targets: &[SymbolId], value: &HilExpr) {
        self.visit_expr(value);
        let pos = self.alloc_pos();
        let source = TupleSource {
            targets: targets.to_vec(),
            value: value.clone(),
            write_pos: pos,
        };
        for target in targets {
            self.facts
                .entry(*target)
                .or_default()
                .note_tuple_write(source.clone());
        }
    }

    fn visit_lvalue_write(&mut self, expr: &HilExpr) {
        match expr {
            HilExpr::Symbol(sym) => {
                self.note_write(*sym);
            }
            other => self.visit_expr(other),
        }
    }
}

impl Visitor for Analyzer {
    fn visit_stmt(&mut self, stmt: &HilStmt) {
        match stmt {
            HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                value,
            } => self.note_plain_assignment(*sym, value),
            HilStmt::Assign { left, value } => {
                self.visit_lvalue_write(left);
                self.visit_expr(value);
            }
            HilStmt::AssignMany { left, value } => {
                let targets: Vec<_> = left
                    .iter()
                    .filter_map(|expr| match expr {
                        HilExpr::Symbol(sym) => Some(*sym),
                        _ => None,
                    })
                    .collect();

                if targets.len() == left.len() {
                    self.note_tuple_assignment(&targets, value);
                } else {
                    for lvalue in left {
                        self.visit_lvalue_write(lvalue);
                    }
                    self.visit_expr(value);
                }
            }
            HilStmt::SetList { table, values, .. } => {
                for value in values {
                    self.visit_expr(value);
                }
                let pos = self.note_write(*table);
                self.note_effect_at(pos);
            }
            HilStmt::Call(expr) => {
                self.visit_expr(expr);
            }
            HilStmt::Phi(_) => {
                unreachable!("phi nodes should have been unfolded at this point")
            }
        }
    }

    fn visit_expr(&mut self, expr: &HilExpr) {
        if let HilExpr::Symbol(sym) = expr {
            let pos = self.alloc_pos();
            self.facts.entry(*sym).or_default().note_read(pos);
            return;
        }

        walk_expr(self, expr);
        if !expr.is_pure() {
            let pos = self.alloc_pos();
            self.note_effect_at(pos);
        }
    }

    fn visit_capture(&mut self, _: usize, sym: SymbolId) {
        self.facts.entry(sym).or_default().poisoned = true;
    }
}

struct Inliner<'a> {
    analysis: Analyzer,
    return_arities: &'a [ReturnArity],
    changed: bool,
    stats: RewriteStats,
}

#[derive(Debug, Default)]
struct RewriteStats {
    regions_visited: usize,
    blocks_visited: usize,
    sequences_visited: usize,
    inline_block_inner_calls: usize,
    inline_block_stmt_total: usize,
    tail_read_collections: usize,
    tail_read_node_total: usize,
    tail_read_symbol_total: usize,
    replacement_read_collections: usize,
    replacement_read_symbol_total: usize,
    substitution_attempts: usize,
    successful_substitutions: usize,
    inline_block_source_candidates: usize,
    read_counter_calls: usize,
    removed_statements: usize,
    direct_statement_removals: usize,
    inline_sequence_edge_calls: usize,
    inline_next_block_calls: usize,
    inline_expr_from_block_calls: usize,
    inline_return_calls: usize,
}

impl<'a> Inliner<'a> {
    fn new(fun: &StructuredFunction, return_arities: &'a [ReturnArity]) -> Self {
        Self {
            analysis: Analyzer::analyze(fun),
            return_arities,
            changed: false,
            stats: RewriteStats::default(),
        }
    }

    fn run(&mut self, root: &mut RegionNode) {
        let span = tracing::info_span!(
            "post_region_inlining_rewrite",
            regions_visited = tracing::field::Empty,
            blocks_visited = tracing::field::Empty,
            sequences_visited = tracing::field::Empty,
            inline_block_inner_calls = tracing::field::Empty,
            inline_block_stmt_total = tracing::field::Empty,
            tail_read_collections = tracing::field::Empty,
            tail_read_node_total = tracing::field::Empty,
            tail_read_symbol_total = tracing::field::Empty,
            replacement_read_collections = tracing::field::Empty,
            replacement_read_symbol_total = tracing::field::Empty,
            substitution_attempts = tracing::field::Empty,
            successful_substitutions = tracing::field::Empty,
            inline_block_source_candidates = tracing::field::Empty,
            read_counter_calls = tracing::field::Empty,
            removed_statements = tracing::field::Empty,
            direct_statement_removals = tracing::field::Empty,
            inline_sequence_edge_calls = tracing::field::Empty,
            inline_next_block_calls = tracing::field::Empty,
            inline_expr_from_block_calls = tracing::field::Empty,
            inline_return_calls = tracing::field::Empty,
        );
        let _enter = span.enter();
        self.visit_region(root);
        span.record("regions_visited", self.stats.regions_visited);
        span.record("blocks_visited", self.stats.blocks_visited);
        span.record("sequences_visited", self.stats.sequences_visited);
        span.record(
            "inline_block_inner_calls",
            self.stats.inline_block_inner_calls,
        );
        span.record(
            "inline_block_stmt_total",
            self.stats.inline_block_stmt_total,
        );
        span.record("tail_read_collections", self.stats.tail_read_collections);
        span.record("tail_read_node_total", self.stats.tail_read_node_total);
        span.record("tail_read_symbol_total", self.stats.tail_read_symbol_total);
        span.record(
            "replacement_read_collections",
            self.stats.replacement_read_collections,
        );
        span.record(
            "replacement_read_symbol_total",
            self.stats.replacement_read_symbol_total,
        );
        span.record("substitution_attempts", self.stats.substitution_attempts);
        span.record(
            "successful_substitutions",
            self.stats.successful_substitutions,
        );
        span.record(
            "inline_block_source_candidates",
            self.stats.inline_block_source_candidates,
        );
        span.record("read_counter_calls", self.stats.read_counter_calls);
        span.record("removed_statements", self.stats.removed_statements);
        span.record(
            "direct_statement_removals",
            self.stats.direct_statement_removals,
        );
        span.record(
            "inline_sequence_edge_calls",
            self.stats.inline_sequence_edge_calls,
        );
        span.record(
            "inline_next_block_calls",
            self.stats.inline_next_block_calls,
        );
        span.record(
            "inline_expr_from_block_calls",
            self.stats.inline_expr_from_block_calls,
        );
        span.record("inline_return_calls", self.stats.inline_return_calls);
    }

    fn visit_region(&mut self, node: &mut RegionNode) {
        self.stats.regions_visited += 1;
        match node {
            RegionNode::BasicBlock { stmts } => {
                self.stats.blocks_visited += 1;
                self.inline_block(stmts);
            }
            RegionNode::Sequence { nodes } => {
                self.stats.sequences_visited += 1;
                for node in nodes.iter_mut() {
                    self.visit_region(node);
                }
                self.inline_sequence_edges(nodes);
            }
            RegionNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.visit_region(then_branch);
                if let Some(else_branch) = else_branch {
                    self.visit_region(else_branch);
                }
            }
            RegionNode::While { body, .. }
            | RegionNode::RepeatUntil { body, .. }
            | RegionNode::NumericFor { body, .. }
            | RegionNode::GenericFor { body, .. } => self.visit_region(body),
            RegionNode::Continue | RegionNode::Break | RegionNode::Return { .. } => {}
        }
    }

    fn inline_block_inner(
        &mut self,
        stmts: &mut Vec<HilStmt>,
        tail_reads: Option<&HashSet<SymbolId>>,
    ) {
        self.stats.inline_block_inner_calls += 1;
        self.stats.inline_block_stmt_total += stmts.len();
        let summary = BlockSummary::new(stmts);
        let plain_sources: Vec<_> = stmts
            .iter()
            .map(|stmt| plain_assignment(stmt).map(|(sym, _)| sym))
            .collect();
        let source_index = BlockSourceIndex::new(&plain_sources);
        let mut removable = HashSet::new();
        let mut idx = 0;
        while idx < stmts.len() {
            let mut active_reads: HashSet<_> = summary.reads_in_stmt(idx).collect();
            let mut candidate_sources = BTreeSet::new();
            for sym in active_reads.iter().copied() {
                source_index.add_sources_in_range(sym, 0, idx, &mut candidate_sources);
            }

            let mut next_source_idx = 0;
            while let Some(source_idx) = candidate_sources.pop_first() {
                if source_idx < next_source_idx {
                    continue;
                }
                next_source_idx = source_idx + 1;
                self.stats.inline_block_source_candidates += 1;
                if removable.contains(&source_idx) {
                    continue;
                }
                let Some(sym) = plain_sources[source_idx] else {
                    continue;
                };
                if !active_reads.contains(&sym) {
                    continue;
                }
                let Some((_, rhs)) = plain_assignment(&stmts[source_idx]) else {
                    continue;
                };
                let rhs = rhs.clone();

                let inlineable = match tail_reads {
                    None => {
                        self.can_inline_globally(sym, &rhs)
                            && (can_substitute_in_stmt_context(&stmts[idx], sym, &rhs)
                                || is_adjacent_assignment_consumer(
                                    &stmts[idx],
                                    sym,
                                    &rhs,
                                    source_idx,
                                    idx,
                                ))
                    }
                    Some(tail_reads) => {
                        self.can_inline_locally(stmts, source_idx, idx, sym, &rhs)
                            && !tail_reads.contains(&sym)
                    }
                };

                if inlineable {
                    self.stats.substitution_attempts += 1;
                }

                if inlineable && replace_symbol_in_stmt(&mut stmts[idx], sym, &rhs) > 0 {
                    self.stats.successful_substitutions += 1;
                    let replacement_reads = expr_read_symbols(&rhs);
                    self.stats.replacement_read_collections += 1;
                    self.stats.replacement_read_symbol_total += replacement_reads.len();
                    for sym in replacement_reads {
                        if active_reads.insert(sym) {
                            source_index.add_sources_in_range(
                                sym,
                                next_source_idx,
                                idx,
                                &mut candidate_sources,
                            );
                        }
                    }
                    removable.insert(source_idx);
                }
            }
            idx += 1;
        }
        self.remove_stmts(stmts, &removable);
    }

    fn inline_block(&mut self, stmts: &mut Vec<HilStmt>) {
        self.inline_block_inner(stmts, None);
    }

    fn inline_block_with_tail_reads(
        &mut self,
        stmts: &mut Vec<HilStmt>,
        tail_reads: &HashSet<SymbolId>,
    ) {
        self.inline_block_inner(stmts, Some(tail_reads));
    }

    fn inline_sequence_edges(&mut self, nodes: &mut [RegionNode]) {
        self.stats.inline_sequence_edge_calls += 1;
        let tail_reads = self.collect_sequence_tail_reads(nodes);

        for idx in 0..nodes.len() {
            let left = &mut nodes[..=idx];
            if let RegionNode::BasicBlock { stmts } = &mut left[idx] {
                self.inline_block_with_tail_reads(stmts, &tail_reads[idx + 1]);
            }
        }

        for idx in 0..nodes.len().saturating_sub(1) {
            let (left, right) = nodes.split_at_mut(idx + 1);
            let RegionNode::BasicBlock { stmts } = &mut left[idx] else {
                continue;
            };

            match &mut right[0] {
                RegionNode::BasicBlock { stmts: next_stmts } => {
                    self.inline_next_block(stmts, next_stmts);
                }
                RegionNode::Return { values } => self.inline_return(stmts, values),
                RegionNode::If { condition, .. } => {
                    self.inline_expr_from_block(stmts, condition);
                }
                RegionNode::GenericFor { exprs, .. } => self.inline_generic_for(stmts, exprs),
                RegionNode::NumericFor {
                    start, end, step, ..
                } => self.inline_numeric_for(stmts, start, end, step),
                _ => {}
            }
        }
    }

    fn collect_sequence_tail_reads(&mut self, nodes: &[RegionNode]) -> Vec<HashSet<SymbolId>> {
        self.stats.tail_read_collections += 1;
        self.stats.tail_read_node_total += nodes.len();

        let mut tail_reads = vec![HashSet::new(); nodes.len() + 1];
        for idx in (0..nodes.len()).rev() {
            let mut reads = region_read_symbols(&nodes[idx]);
            self.stats.tail_read_symbol_total += reads.len();
            reads.extend(tail_reads[idx + 1].iter().copied());
            tail_reads[idx] = reads;
        }

        tail_reads
    }

    fn inline_next_block(&mut self, source_stmts: &mut Vec<HilStmt>, next_stmts: &mut [HilStmt]) {
        self.stats.inline_next_block_calls += 1;
        let mut removable = HashSet::new();
        for (source_idx, stmt) in source_stmts.iter().enumerate() {
            if removable.contains(&source_idx) {
                continue;
            }
            let Some((sym, rhs)) = plain_assignment(stmt).map(|(sym, rhs)| (sym, rhs.clone()))
            else {
                continue;
            };
            if !self.can_inline_globally(sym, &rhs) {
                continue;
            }
            for stmt in next_stmts.iter_mut() {
                self.stats.read_counter_calls += 1;
                if count_symbol_reads_in_stmt(stmt, sym) == 0 {
                    continue;
                }
                if can_substitute_in_stmt_context(stmt, sym, &rhs) {
                    self.stats.substitution_attempts += 1;
                    if replace_symbol_in_stmt(stmt, sym, &rhs) > 0 {
                        self.stats.successful_substitutions += 1;
                        removable.insert(source_idx);
                    }
                }
                break;
            }
        }
        self.remove_stmts(source_stmts, &removable);
    }

    fn inline_return(&mut self, stmts: &mut Vec<HilStmt>, values: &mut SmallVec<[HilExpr; 3]>) {
        self.stats.inline_return_calls += 1;
        if self.try_inline_tuple_return(stmts, values) {
            return;
        }

        for value in values.iter_mut() {
            self.inline_expr_from_block(stmts, value);
        }
        if values
            .iter()
            .any(|value| !matches!(value, HilExpr::Symbol(_)))
        {
            return;
        }

        let mut removable = HashSet::new();
        for value in values.iter_mut() {
            let HilExpr::Symbol(sym) = value else {
                continue;
            };
            let Some((idx, rhs)) = self.find_plain_source(stmts, *sym) else {
                continue;
            };
            if self.can_inline_globally(*sym, &rhs) {
                *value = rhs;
                removable.insert(idx);
            }
        }
        self.remove_stmts(stmts, &removable);
    }

    fn inline_expr_from_block(&mut self, stmts: &mut Vec<HilStmt>, expr: &mut HilExpr) {
        self.stats.inline_expr_from_block_calls += 1;
        let mut removable = HashSet::new();
        for (source_idx, stmt) in stmts.iter().enumerate() {
            if removable.contains(&source_idx) {
                continue;
            }
            let Some((sym, rhs)) = plain_assignment(stmt).map(|(sym, rhs)| (sym, rhs.clone()))
            else {
                continue;
            };
            if !self.can_inline_globally(sym, &rhs) {
                continue;
            }
            if !can_substitute_in_expr_context(expr, sym, &rhs) {
                continue;
            }
            self.stats.substitution_attempts += 1;
            if replace_symbol_in_expr(expr, sym, &rhs) > 0 {
                self.stats.successful_substitutions += 1;
                removable.insert(source_idx);
            }
        }
        self.remove_stmts(stmts, &removable);
    }

    fn try_inline_tuple_return(
        &mut self,
        stmts: &mut Vec<HilStmt>,
        values: &mut SmallVec<[HilExpr; 3]>,
    ) -> bool {
        let Some(targets) = values
            .iter()
            .map(|expr| match expr {
                HilExpr::Symbol(sym) => Some(*sym),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };

        let Some((idx, source)) = self.find_tuple_source(stmts, &targets) else {
            return false;
        };
        if !self.can_inline_tuple(&source, targets.len()) {
            return false;
        }
        if self.expr_arity(&source.value) != ReturnArity::Exact(targets.len()) {
            return false;
        }

        values.clear();
        values.push(source.value);
        stmts.remove(idx);
        self.stats.direct_statement_removals += 1;
        self.changed = true;
        true
    }

    fn inline_generic_for(&mut self, stmts: &mut Vec<HilStmt>, exprs: &mut SmallVec<[HilExpr; 3]>) {
        if self.inline_plain_exprs(stmts, exprs) {
            return;
        }

        let Some(targets) = exprs
            .iter()
            .map(|expr| match expr {
                HilExpr::Symbol(sym) => Some(*sym),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            return;
        };

        let Some((idx, source)) = self.find_tuple_source(stmts, &targets) else {
            return;
        };
        if !self.can_inline_tuple(&source, targets.len()) {
            return;
        }
        let ReturnArity::Exact(arity) = self.expr_arity(&source.value) else {
            return;
        };
        if arity > targets.len() || targets.len() > 3 {
            return;
        }

        *exprs = smallvec![source.value];
        stmts.remove(idx);
        self.stats.direct_statement_removals += 1;
        self.changed = true;
    }

    fn inline_plain_exprs(
        &mut self,
        stmts: &mut Vec<HilStmt>,
        exprs: &mut SmallVec<[HilExpr; 3]>,
    ) -> bool {
        let mut removable = HashSet::new();
        for expr in exprs.iter_mut() {
            let HilExpr::Symbol(sym) = expr else {
                continue;
            };
            let Some((idx, rhs)) = self.find_plain_source(stmts, *sym) else {
                continue;
            };
            if self.can_inline_globally(*sym, &rhs) {
                *expr = rhs;
                removable.insert(idx);
            }
        }
        let changed = !removable.is_empty();
        self.remove_stmts(stmts, &removable);
        changed
    }

    fn inline_numeric_for(
        &mut self,
        stmts: &mut Vec<HilStmt>,
        start: &mut HilExpr,
        end: &mut HilExpr,
        step: &mut HilExpr,
    ) {
        let mut removable = HashSet::new();
        for bound in [start, end, step] {
            let HilExpr::Symbol(sym) = bound else {
                continue;
            };
            let Some((idx, rhs)) = self.find_plain_source(stmts, *sym) else {
                continue;
            };
            if self.can_inline_globally(*sym, &rhs) {
                *bound = rhs;
                removable.insert(idx);
            }
        }
        self.remove_stmts(stmts, &removable);
    }

    fn find_plain_source(&self, stmts: &[HilStmt], sym: SymbolId) -> Option<(usize, HilExpr)> {
        stmts.iter().enumerate().find_map(|(idx, stmt)| match stmt {
            HilStmt::Assign {
                left: HilExpr::Symbol(target),
                value,
            } if *target == sym => Some((idx, value.clone())),
            _ => None,
        })
    }

    fn find_tuple_source(
        &self,
        stmts: &[HilStmt],
        targets: &[SymbolId],
    ) -> Option<(usize, TupleSource)> {
        if targets.is_empty() {
            return None;
        }

        stmts.iter().enumerate().find_map(|(idx, stmt)| match stmt {
            HilStmt::AssignMany { left, value } => {
                let source_targets: Vec<_> = left
                    .iter()
                    .filter_map(|expr| match expr {
                        HilExpr::Symbol(sym) => Some(*sym),
                        _ => None,
                    })
                    .collect();
                if source_targets == targets {
                    let write_pos = self
                        .analysis
                        .facts
                        .get(&targets[0])
                        .and_then(|fact| fact.write_pos)?;

                    Some((
                        idx,
                        TupleSource {
                            targets: source_targets,
                            value: value.clone(),
                            write_pos,
                        },
                    ))
                } else {
                    None
                }
            }
            _ => None,
        })
    }

    fn can_inline_globally(&self, sym: SymbolId, rhs: &HilExpr) -> bool {
        let Some(fact) = self.analysis.facts.get(&sym) else {
            return false;
        };
        if fact.poisoned || fact.writes != 1 || fact.reads != 1 || rhs.reads_symbol(&sym) {
            return false;
        }
        if fact.rhs.as_ref() != Some(rhs) {
            return false;
        }
        self.can_move_rhs(fact, rhs)
    }

    fn can_inline_locally(
        &self,
        stmts: &[HilStmt],
        source_idx: usize,
        use_idx: usize,
        sym: SymbolId,
        rhs: &HilExpr,
    ) -> bool {
        if rhs.reads_symbol(&sym)
            || !matches!(
                &stmts[source_idx],
                HilStmt::Assign {
                    left: HilExpr::Symbol(target),
                    value,
                } if *target == sym && value == rhs
            )
        {
            return false;
        }
        if let Some(fact) = self.analysis.facts.get(&sym)
            && (fact.poisoned || fact.writes != 1)
        {
            return false;
        }
        if stmts[source_idx + 1..use_idx]
            .iter()
            .any(|stmt| count_symbol_reads_in_stmt(stmt, sym) > 0)
        {
            return false;
        }
        if stmts[use_idx + 1..]
            .iter()
            .any(|stmt| count_symbol_reads_in_stmt(stmt, sym) > 0)
        {
            return false;
        }
        if !rhs.is_pure()
            && !matches!(rhs, HilExpr::Symbol(_))
            && !is_adjacent_assignment_consumer(&stmts[use_idx], sym, rhs, source_idx, use_idx)
        {
            return false;
        }
        let rhs_reads = expr_read_symbols(rhs);
        if rhs_reads.iter().any(|source| {
            stmts[source_idx + 1..use_idx]
                .iter()
                .any(|stmt| stmt_writes_symbol(stmt, *source))
        }) {
            return false;
        }
        if rhs_reads.iter().any(|source| {
            self.analysis
                .facts
                .get(source)
                .is_some_and(|fact| fact.poisoned)
                && stmts[source_idx + 1..use_idx].iter().any(stmt_has_effect)
        }) {
            return false;
        }

        true
    }

    fn can_inline_tuple(&self, source: &TupleSource, target_count: usize) -> bool {
        if source.targets.len() != target_count || source.targets.is_empty() {
            return false;
        }
        if source
            .targets
            .iter()
            .any(|target| source.value.reads_symbol(target))
        {
            return false;
        }

        for target in &source.targets {
            let Some(fact) = self.analysis.facts.get(target) else {
                return false;
            };
            if fact.poisoned || fact.writes != 1 || fact.reads != 1 {
                return false;
            }
            let Some(tuple) = &fact.tuple else {
                return false;
            };
            if tuple.targets != source.targets || tuple.value != source.value {
                return false;
            }
            if !self.can_move_rhs(fact, &source.value) {
                return false;
            }
        }

        true
    }

    fn can_move_rhs(&self, fact: &SymbolFacts, rhs: &HilExpr) -> bool {
        let Some(write_pos) = fact.write_pos else {
            return false;
        };
        let Some(read_pos) = fact.read_positions.iter().copied().max() else {
            return false;
        };
        for source in expr_read_symbols(rhs) {
            let Some(source_fact) = self.analysis.facts.get(&source) else {
                return false;
            };
            if positions_contain_in_range(&source_fact.write_positions, write_pos + 1, read_pos) {
                return false;
            }
            if source_fact.poisoned && self.has_effect_between_positions(write_pos, read_pos) {
                return false;
            }
        }

        rhs.is_pure() || !self.has_effect_between_positions(write_pos, read_pos)
    }

    fn has_effect_between_positions(&self, write_pos: usize, read_pos: usize) -> bool {
        positions_contain_in_range(&self.analysis.effect_positions, write_pos + 1, read_pos)
    }

    fn expr_arity(&self, expr: &HilExpr) -> ReturnArity {
        match expr {
            HilExpr::Call { fun, .. } => self.call_arity(fun),
            HilExpr::MethodCall { .. } | HilExpr::VarArgs => ReturnArity::Unknown,
            _ => ReturnArity::Exact(1),
        }
    }

    fn call_arity(&self, fun: &HilExpr) -> ReturnArity {
        match fun {
            HilExpr::Global(_) => luau_libfunc_arity(fun),
            HilExpr::GetField { obj, .. } if matches!(&**obj, HilExpr::Global(_)) => {
                luau_libfunc_arity(fun)
            }
            HilExpr::Closure { proto, .. } => self
                .return_arities
                .get(proto.0 as usize)
                .copied()
                .unwrap_or(ReturnArity::Unknown),
            HilExpr::Symbol(sym) => self
                .analysis
                .facts
                .get(sym)
                .and_then(|fact| fact.rhs.as_ref())
                .map_or(ReturnArity::Unknown, |rhs| self.call_arity(rhs)),
            _ => ReturnArity::Unknown,
        }
    }

    fn remove_stmts(&mut self, stmts: &mut Vec<HilStmt>, removable: &HashSet<usize>) {
        if removable.is_empty() {
            return;
        }
        self.stats.removed_statements += removable.len();
        let mut idx = 0usize;
        stmts.retain(|_| {
            let keep = !removable.contains(&idx);
            idx += 1;
            keep
        });
        self.changed = true;
    }
}

fn plain_assignment(stmt: &HilStmt) -> Option<(SymbolId, &HilExpr)> {
    match stmt {
        HilStmt::Assign {
            left: HilExpr::Symbol(sym),
            value,
        } => Some((*sym, value)),
        _ => None,
    }
}

fn stmt_has_effect(stmt: &HilStmt) -> bool {
    match stmt {
        HilStmt::Assign { left, value } => !left.is_pure() || !value.is_pure(),
        HilStmt::AssignMany { left, value } => {
            left.iter().any(|left| !left.is_pure()) || !value.is_pure()
        }
        HilStmt::SetList { .. } | HilStmt::Call(_) => true,
        HilStmt::Phi(_) => unreachable!("phi nodes should have been unfolded at this point"),
    }
}

fn can_substitute_in_stmt_context(stmt: &HilStmt, sym: SymbolId, rhs: &HilExpr) -> bool {
    rhs.is_pure() || matches!(rhs, HilExpr::Symbol(_)) || is_call_statement_consumer(stmt, sym, rhs)
}

fn can_substitute_in_expr_context(expr: &HilExpr, sym: SymbolId, rhs: &HilExpr) -> bool {
    rhs.is_pure()
        || matches!(rhs, HilExpr::Symbol(_))
        || can_inline_effectful_at_expr_occurrence(expr, sym, rhs)
}

fn is_adjacent_assignment_consumer(
    stmt: &HilStmt,
    sym: SymbolId,
    rhs: &HilExpr,
    source_idx: usize,
    use_idx: usize,
) -> bool {
    let HilStmt::Assign { left, value } = stmt else {
        return false;
    };

    !left.reads_symbol(&sym)
        && left.is_pure()
        && use_idx == source_idx + 1
        && can_inline_effectful_at_expr_occurrence(value, sym, rhs)
}

fn is_call_statement_consumer(stmt: &HilStmt, sym: SymbolId, rhs: &HilExpr) -> bool {
    matches!(stmt, HilStmt::Call(expr) if can_substitute_in_expr_context(expr, sym, rhs))
}

fn can_inline_effectful_at_expr_occurrence(expr: &HilExpr, sym: SymbolId, rhs: &HilExpr) -> bool {
    count_symbol_reads_in_expr(expr, sym) == 1
        && occurrence_has_no_prior_effect(expr, sym)
        && !occurrence_is_final_multiret_position(expr, sym, rhs)
}

fn occurrence_has_no_prior_effect(expr: &HilExpr, sym: SymbolId) -> bool {
    match expr {
        HilExpr::Symbol(target) => *target == sym,
        HilExpr::GetField { obj, .. } => occurrence_has_no_prior_effect(obj, sym),
        HilExpr::GetIndex { obj, index } => {
            if obj.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(obj, sym)
            } else {
                obj.is_pure() && occurrence_has_no_prior_effect(index, sym)
            }
        }
        HilExpr::Call { fun, args } => {
            if fun.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(fun, sym)
            } else if !fun.is_pure() {
                false
            } else {
                args.iter()
                    .position(|arg| arg.reads_symbol(&sym))
                    .is_some_and(|idx| {
                        args[..idx].iter().all(HilExpr::is_pure)
                            && occurrence_has_no_prior_effect(&args[idx], sym)
                    })
            }
        }
        HilExpr::MethodCall { object, args, .. } => {
            if object.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(object, sym)
            } else if !object.is_pure() {
                false
            } else {
                args.iter()
                    .position(|arg| arg.reads_symbol(&sym))
                    .is_some_and(|idx| {
                        args[..idx].iter().all(HilExpr::is_pure)
                            && occurrence_has_no_prior_effect(&args[idx], sym)
                    })
            }
        }
        HilExpr::Binary { lhs, rhs, .. } => {
            if lhs.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(lhs, sym)
            } else {
                lhs.is_pure() && occurrence_has_no_prior_effect(rhs, sym)
            }
        }
        HilExpr::Unary { expr, .. } => occurrence_has_no_prior_effect(expr, sym),
        HilExpr::IfElse {
            condition,
            then_expr,
            else_expr,
        } => {
            if condition.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(condition, sym)
            } else if !condition.is_pure() {
                false
            } else if then_expr.reads_symbol(&sym) {
                occurrence_has_no_prior_effect(then_expr, sym)
            } else {
                occurrence_has_no_prior_effect(else_expr, sym)
            }
        }
        HilExpr::Table { items } => {
            let Some(idx) = items.iter().position(|item| match item {
                HilTableItem::List(expr) => expr.reads_symbol(&sym),
                HilTableItem::Index(key, value) => {
                    key.reads_symbol(&sym) || value.reads_symbol(&sym)
                }
            }) else {
                return false;
            };

            items[..idx].iter().all(|item| match item {
                HilTableItem::List(expr) => expr.is_pure(),
                HilTableItem::Index(key, value) => key.is_pure() && value.is_pure(),
            }) && match &items[idx] {
                HilTableItem::List(expr) => occurrence_has_no_prior_effect(expr, sym),
                HilTableItem::Index(key, value) => {
                    if key.reads_symbol(&sym) {
                        occurrence_has_no_prior_effect(key, sym)
                    } else {
                        key.is_pure() && occurrence_has_no_prior_effect(value, sym)
                    }
                }
            }
        }
        HilExpr::Nil
        | HilExpr::Number(_)
        | HilExpr::String(_)
        | HilExpr::Bool(_)
        | HilExpr::Closure { .. }
        | HilExpr::Global(_)
        | HilExpr::VarArgs => false,
    }
}

fn occurrence_is_final_multiret_position(expr: &HilExpr, sym: SymbolId, rhs: &HilExpr) -> bool {
    if !matches!(
        rhs,
        HilExpr::Call { .. } | HilExpr::MethodCall { .. } | HilExpr::VarArgs
    ) {
        return false;
    }

    match expr {
        HilExpr::Call { fun, args } => {
            if fun.reads_symbol(&sym) {
                return false;
            }

            args.last().is_some_and(|arg| arg.reads_symbol(&sym))
        }
        HilExpr::MethodCall { object, args, .. } => {
            if object.reads_symbol(&sym) {
                return false;
            }

            args.last().is_some_and(|arg| arg.reads_symbol(&sym))
        }
        _ => false,
    }
}

fn positions_contain_in_range(positions: &[usize], start: usize, end: usize) -> bool {
    let idx = positions.partition_point(|pos| *pos < start);
    positions.get(idx).is_some_and(|pos| *pos < end)
}

pub fn run(fun: &mut StructuredFunction, return_arities: &[ReturnArity]) -> bool {
    let mut changed = false;
    let mut iteration = 0;
    loop {
        iteration += 1;
        let span = tracing::info_span!(
            "post_region_inlining_iteration",
            proto = fun.proto.0,
            iteration,
            changed = tracing::field::Empty,
        );
        let _enter = span.enter();

        let mut inliner = Inliner::new(fun, return_arities);
        inliner.run(&mut fun.root);
        span.record("changed", inliner.changed);
        if !inliner.changed {
            break;
        }
        changed = true;
    }
    changed
}
