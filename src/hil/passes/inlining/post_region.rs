use std::collections::{HashMap, HashSet};

use smallvec::{SmallVec, smallvec};

use crate::hil::{
    ReturnArity, StructuredFunction,
    cflow::region::RegionNode,
    ir::{HilExpr, HilStmt, HilTableItem, PhiNode},
    lifter::ssa::SymbolId,
    passes::return_arity::luau_global_arity,
    visitor::{Visitor, VisitorMut, walk_expr, walk_expr_mut},
};

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
        let mut analyzer = Self::default();
        for param in &fun.params {
            analyzer.facts.entry(*param).or_default().poisoned = true;
        }
        for upvalue in &fun.upvalues {
            analyzer.facts.entry(*upvalue).or_default().poisoned = true;
        }
        analyzer.visit_region(&fun.root);
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
}

impl<'a> Inliner<'a> {
    fn new(fun: &StructuredFunction, return_arities: &'a [ReturnArity]) -> Self {
        Self {
            analysis: Analyzer::analyze(fun),
            return_arities,
            changed: false,
        }
    }

    fn run(&mut self, root: &mut RegionNode) {
        self.visit_region(root);
    }

    fn visit_region(&mut self, node: &mut RegionNode) {
        match node {
            RegionNode::BasicBlock { stmts } => {
                self.inline_block(stmts);
            }
            RegionNode::Sequence { nodes } => {
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

    fn inline_block_inner(&mut self, stmts: &mut Vec<HilStmt>, tail: Option<&[RegionNode]>) {
        let mut removable = HashSet::new();
        let mut idx = 0;
        while idx < stmts.len() {
            for source_idx in 0..idx {
                if removable.contains(&source_idx) {
                    continue;
                }
                let Some((sym, rhs)) =
                    plain_assignment(&stmts[source_idx]).map(|(s, r)| (s, r.clone()))
                else {
                    continue;
                };

                let inlineable = match tail {
                    None => {
                        self.can_inline_globally(sym, &rhs)
                            && can_substitute_in_stmt_context(
                                &stmts[idx],
                                sym,
                                &rhs,
                                source_idx,
                                idx,
                            )
                    }
                    Some(tail) => {
                        self.can_inline_locally(stmts, source_idx, idx, sym, &rhs)
                            && !tail
                                .iter()
                                .any(|node| ReadCounter::new(sym).in_region(node) > 0)
                    }
                };

                if inlineable && substitute_in_stmt(&mut stmts[idx], sym, &rhs) {
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

    fn inline_block_with_tail(&mut self, stmts: &mut Vec<HilStmt>, tail: &[RegionNode]) {
        self.inline_block_inner(stmts, Some(tail));
    }

    fn inline_sequence_edges(&mut self, nodes: &mut [RegionNode]) {
        for idx in 0..nodes.len() {
            let (left, tail) = nodes.split_at_mut(idx + 1);
            if let RegionNode::BasicBlock { stmts } = &mut left[idx] {
                self.inline_block_with_tail(stmts, tail);
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

    fn inline_next_block(&mut self, source_stmts: &mut Vec<HilStmt>, next_stmts: &mut [HilStmt]) {
        let mut removable = HashSet::new();
        for source_idx in 0..source_stmts.len() {
            if removable.contains(&source_idx) {
                continue;
            }
            let Some((sym, rhs)) =
                plain_assignment(&source_stmts[source_idx]).map(|(sym, rhs)| (sym, rhs.clone()))
            else {
                continue;
            };
            if !self.can_inline_globally(sym, &rhs) {
                continue;
            }
            if !rhs.is_pure() && !matches!(rhs, HilExpr::Symbol(_)) {
                continue;
            }
            let mut used = false;
            for stmt in next_stmts.iter_mut() {
                used |= substitute_in_stmt(stmt, sym, &rhs);
            }
            if used {
                removable.insert(source_idx);
            }
        }
        self.remove_stmts(source_stmts, &removable);
    }

    fn inline_return(&mut self, stmts: &mut Vec<HilStmt>, values: &mut SmallVec<[HilExpr; 3]>) {
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
        let mut removable = HashSet::new();
        for source_idx in 0..stmts.len() {
            if removable.contains(&source_idx) {
                continue;
            }
            let Some((sym, rhs)) =
                plain_assignment(&stmts[source_idx]).map(|(sym, rhs)| (sym, rhs.clone()))
            else {
                continue;
            };
            if !self.can_inline_globally(sym, &rhs) {
                continue;
            }
            if !can_substitute_in_expr_context(expr, sym, &rhs) {
                continue;
            }
            let mut substituter = SymbolSubstituter {
                sym,
                replacement: &rhs,
                changed: false,
            };
            substituter.visit_expr(expr);
            if substituter.changed {
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
                    let Some(write_pos) = self
                        .analysis
                        .facts
                        .get(&targets[0])
                        .and_then(|fact| fact.write_pos)
                    else {
                        return None;
                    };

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
        if let HilExpr::Symbol(source) = rhs {
            let Some(source_fact) = self.analysis.facts.get(source) else {
                return false;
            };
            if self.source_rewritten_between(source_fact, fact) {
                return false;
            }
            if source_fact.poisoned && self.has_effect_between(fact) {
                return false;
            }
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
        if let Some(fact) = self.analysis.facts.get(&sym) {
            if fact.poisoned || fact.writes != 1 {
                return false;
            }
        }
        if stmts[source_idx + 1..use_idx]
            .iter()
            .any(|stmt| ReadCounter::new(sym).in_stmt(stmt) > 0)
        {
            return false;
        }
        if stmts[use_idx + 1..]
            .iter()
            .any(|stmt| ReadCounter::new(sym).in_stmt(stmt) > 0)
        {
            return false;
        }
        if !rhs.is_pure()
            && !matches!(rhs, HilExpr::Symbol(_))
            && !is_adjacent_assignment_consumer(&stmts[use_idx], sym, source_idx, use_idx)
        {
            return false;
        }
        if let HilExpr::Symbol(source) = rhs {
            if stmts[source_idx + 1..use_idx]
                .iter()
                .any(|stmt| stmt_writes_symbol(stmt, *source))
            {
                return false;
            }
            if self
                .analysis
                .facts
                .get(source)
                .is_some_and(|fact| fact.poisoned)
                && stmts[source_idx + 1..use_idx].iter().any(stmt_has_effect)
            {
                return false;
            }
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
        if rhs.is_pure() {
            return true;
        }
        let Some(write_pos) = fact.write_pos else {
            return false;
        };
        let Some(read_pos) = fact.read_positions.iter().copied().max() else {
            return false;
        };
        !self.has_effect_between_positions(write_pos, read_pos)
    }

    fn has_effect_between(&self, fact: &SymbolFacts) -> bool {
        let Some(write_pos) = fact.write_pos else {
            return true;
        };
        let Some(read_pos) = fact.read_positions.iter().copied().max() else {
            return true;
        };
        self.has_effect_between_positions(write_pos, read_pos)
    }

    fn has_effect_between_positions(&self, write_pos: usize, read_pos: usize) -> bool {
        self.analysis
            .effect_positions
            .iter()
            .any(|pos| *pos > write_pos && *pos < read_pos)
    }

    fn source_rewritten_between(&self, source: &SymbolFacts, target: &SymbolFacts) -> bool {
        let Some(write_pos) = target.write_pos else {
            return true;
        };
        let Some(read_pos) = target.read_positions.iter().copied().max() else {
            return true;
        };
        source
            .write_positions
            .iter()
            .any(|pos| *pos > write_pos && *pos < read_pos)
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
            HilExpr::Closure { proto, .. } => self
                .return_arities
                .get(*proto)
                .copied()
                .unwrap_or(ReturnArity::Unknown),
            HilExpr::Global(name) | HilExpr::Import(name) => luau_global_arity(name),
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

fn stmt_writes_symbol(stmt: &HilStmt, sym: SymbolId) -> bool {
    match stmt {
        HilStmt::Assign { left, .. } => matches!(left, HilExpr::Symbol(target) if *target == sym),
        HilStmt::AssignMany { left, .. } => left
            .iter()
            .any(|left| matches!(left, HilExpr::Symbol(target) if *target == sym)),
        HilStmt::SetList { table, .. } => *table == sym,
        HilStmt::Call(_) => false,
        HilStmt::Phi(_) => unreachable!("phi nodes should have been unfolded at this point"),
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

fn can_substitute_in_stmt_context(
    stmt: &HilStmt,
    sym: SymbolId,
    rhs: &HilExpr,
    source_idx: usize,
    use_idx: usize,
) -> bool {
    rhs.is_pure()
        || matches!(rhs, HilExpr::Symbol(_))
        || is_adjacent_assignment_consumer(stmt, sym, source_idx, use_idx)
}

fn can_substitute_in_expr_context(expr: &HilExpr, sym: SymbolId, rhs: &HilExpr) -> bool {
    rhs.is_pure()
        || matches!(rhs, HilExpr::Symbol(_))
        || can_inline_effectful_at_expr_occurrence(expr, sym)
}

fn is_adjacent_assignment_consumer(
    stmt: &HilStmt,
    sym: SymbolId,
    source_idx: usize,
    use_idx: usize,
) -> bool {
    let HilStmt::Assign { left, value } = stmt else {
        return false;
    };

    !left.reads_symbol(&sym)
        && left.is_pure()
        && use_idx == source_idx + 1
        && can_inline_effectful_at_expr_occurrence(value, sym)
}

fn can_inline_effectful_at_expr_occurrence(expr: &HilExpr, sym: SymbolId) -> bool {
    ReadCounter::new(sym).in_expr(expr) == 1 && occurrence_has_no_prior_effect(expr, sym)
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
        | HilExpr::Import(_)
        | HilExpr::VarArgs => false,
    }
}

struct ReadCounter {
    sym: SymbolId,
    counter: usize,
}

impl ReadCounter {
    fn new(sym: SymbolId) -> Self {
        Self { sym, counter: 0 }
    }

    fn in_expr(mut self, expr: &HilExpr) -> usize {
        self.visit_expr(expr);
        self.counter
    }

    fn in_stmt(mut self, stmt: &HilStmt) -> usize {
        self.visit_stmt(stmt);
        self.counter
    }

    fn in_region(mut self, region: &RegionNode) -> usize {
        self.visit_region(region);
        self.counter
    }
}

impl Visitor for ReadCounter {
    fn visit_expr(&mut self, expr: &HilExpr) {
        if let HilExpr::Symbol(sym) = expr
            && *sym == self.sym
        {
            self.counter += 1;
            return;
        }

        walk_expr(self, expr);
    }

    fn visit_phi(&mut self, _: &PhiNode) {
        unreachable!("phi nodes should have been unfolded at this point")
    }
}

fn substitute_in_stmt(stmt: &mut HilStmt, sym: SymbolId, replacement: &HilExpr) -> bool {
    let mut substituter = SymbolSubstituter {
        sym,
        replacement,
        changed: false,
    };
    substituter.visit_stmt(stmt);
    substituter.changed
}

struct SymbolSubstituter<'a> {
    sym: SymbolId,
    replacement: &'a HilExpr,
    changed: bool,
}

impl VisitorMut for SymbolSubstituter<'_> {
    fn visit_phi(&mut self, _: &mut PhiNode) {
        unreachable!("phi nodes should have been unfolded at this point")
    }

    fn visit_expr(&mut self, expr: &mut HilExpr) {
        if let HilExpr::Symbol(sym) = expr
            && *sym == self.sym
        {
            *expr = self.replacement.clone();
            self.changed = true;
            return;
        }

        walk_expr_mut(self, expr);
    }
}

pub fn run(fun: &mut StructuredFunction, return_arities: &[ReturnArity]) -> bool {
    let mut changed = false;
    loop {
        let mut inliner = Inliner::new(fun, return_arities);
        inliner.run(&mut fun.root);
        if !inliner.changed {
            break;
        }
        changed = true;
    }
    changed
}
