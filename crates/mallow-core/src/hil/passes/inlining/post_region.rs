use std::collections::HashSet;

use crate::hil::{
    ReturnArity, StructuredFunction,
    cflow::region::RegionNode,
    ir::{Expr, Stmt, ValuePack},
    lifter::ssa::SymbolId,
    passes::return_arity::luau_libfunc_arity,
};

use super::{
    common::{
        expr_read_symbols, region_read_symbols, replace_symbol_in_expr, replace_symbol_in_stmt,
    },
    evaluation::{can_substitute_in_expr, can_substitute_in_stmt, is_adjacent_assignment_consumer},
};
use crate::hil::passes::use_def::{
    BlockUseDef, CallSource, FunctionUseDef, SymbolUseDef, positions_contain_in_range,
};

/// Describes one tuple assignment which can move into a consumer.
struct TupleSource {
    /// Symbols written by the assignment.
    targets: Vec<SymbolId>,
    /// Values evaluated by the assignment.
    values: ValuePack,
    /// Group shared by every target from this assignment.
    group: usize,
}

/// Rewrites a structured function using one immutable function index.
struct Inliner<'a> {
    analysis: FunctionUseDef,
    return_arities: &'a [ReturnArity],
    changed: bool,
}

impl<'a> Inliner<'a> {
    /// Creates an inliner for one function sweep.
    fn new(fun: &StructuredFunction, return_arities: &'a [ReturnArity]) -> Self {
        Self {
            analysis: FunctionUseDef::analyze(fun),
            return_arities,
            changed: false,
        }
    }

    /// Rewrites the function root once.
    fn run(&mut self, root: &mut RegionNode) {
        let span = tracing::info_span!("post_region_inlining_rewrite");
        let _enter = span.enter();
        self.rewrite_region(root, &HashSet::new(), &HashSet::new());
    }

    /// Rewrites one region with its later and repeated reads.
    fn rewrite_region(
        &mut self,
        node: &mut RegionNode,
        tail_reads: &HashSet<SymbolId>,
        repeated_reads: &HashSet<SymbolId>,
    ) {
        match node {
            RegionNode::BasicBlock { stmts } => {
                self.inline_block(stmts, tail_reads, repeated_reads)
            }
            RegionNode::Sequence { nodes } => {
                self.rewrite_sequence(nodes, tail_reads, repeated_reads)
            }
            RegionNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.rewrite_region(then_branch, tail_reads, repeated_reads);
                if let Some(else_branch) = else_branch {
                    self.rewrite_region(else_branch, tail_reads, repeated_reads);
                }
            }
            RegionNode::While { condition, body } | RegionNode::RepeatUntil { condition, body } => {
                // Reads in the loop can execute again after the current use.
                let mut loop_reads = repeated_reads.clone();
                loop_reads.extend(expr_read_symbols(condition));
                loop_reads.extend(region_read_symbols(body));
                self.rewrite_region(body, tail_reads, &loop_reads);
            }
            RegionNode::NumericFor { body, .. } | RegionNode::GenericFor { body, .. } => {
                let mut loop_reads = repeated_reads.clone();
                loop_reads.extend(region_read_symbols(body));
                self.rewrite_region(body, tail_reads, &loop_reads);
            }
            RegionNode::Continue | RegionNode::Break | RegionNode::Return { .. } => {}
        }
    }

    /// Rewrites a sequence from left to right and then joins each adjacent edge.
    fn rewrite_sequence(
        &mut self,
        nodes: &mut [RegionNode],
        tail_reads: &HashSet<SymbolId>,
        repeated_reads: &HashSet<SymbolId>,
    ) {
        let tails = sequence_tails(nodes, tail_reads);
        for idx in 0..nodes.len() {
            self.rewrite_region(&mut nodes[idx], &tails[idx], repeated_reads);

            if idx + 1 < nodes.len() {
                let (left, right) = nodes.split_at_mut(idx + 1);
                self.inline_edge(&mut left[idx], &mut right[0]);
            }
        }
    }

    /// Rewrites assignments whose uses are in the same basic block.
    fn inline_block(
        &mut self,
        stmts: &mut Vec<Stmt>,
        tail_reads: &HashSet<SymbolId>,
        repeated_reads: &HashSet<SymbolId>,
    ) {
        // Removing a source can make two effectful statements adjacent. Rebuild
        // only this block until no source is removed.
        loop {
            let block = BlockUseDef::analyze(stmts);
            let mut removable = HashSet::new();

            for source_idx in 0..stmts.len() {
                let Some((sym, rhs)) = plain_assignment(&stmts[source_idx]) else {
                    continue;
                };
                let Some(use_idx) = block.only_read_stmt_after(sym, source_idx) else {
                    continue;
                };

                let can_move = if self.can_inline_globally(sym, rhs) {
                    true
                } else {
                    // A loop can execute earlier reads again. Every syntactic read
                    // must be in this use when the symbol is read by the loop.
                    let repeated_use_is_local =
                        !repeated_reads.contains(&sym)
                            || self.analysis.symbols.get(&sym).is_some_and(|fact| {
                                fact.reads == block.read_count_at(sym, use_idx)
                            });
                    !tail_reads.contains(&sym)
                        && repeated_use_is_local
                        && self.can_inline_locally(&block, source_idx, use_idx, sym, rhs)
                };
                if !can_move {
                    continue;
                }
                let context_is_safe = can_substitute_in_stmt(&stmts[use_idx], sym, rhs)
                    || is_adjacent_assignment_consumer(
                        &stmts[use_idx],
                        sym,
                        rhs,
                        source_idx,
                        use_idx,
                    );
                if !context_is_safe {
                    continue;
                }

                let replacement = rhs.clone();
                if replace_symbol_in_stmt(&mut stmts[use_idx], sym, &replacement) > 0 {
                    removable.insert(source_idx);
                }
            }

            if removable.is_empty() {
                break;
            }
            self.remove_stmts(stmts, &removable);
        }
    }

    /// Rewrites values across one adjacent sequence edge.
    fn inline_edge(&mut self, source: &mut RegionNode, target: &mut RegionNode) {
        let RegionNode::BasicBlock { stmts } = source else {
            return;
        };

        match target {
            RegionNode::BasicBlock { stmts: next_stmts } => {
                self.inline_next_block(stmts, next_stmts)
            }
            RegionNode::Return { values } => self.inline_return(stmts, values),
            RegionNode::If { condition, .. } => self.inline_expr_from_block(stmts, condition),
            RegionNode::GenericFor { exprs, .. } => self.inline_generic_for(stmts, exprs),
            RegionNode::NumericFor {
                start, end, step, ..
            } => self.inline_numeric_for(stmts, start, end, step),
            _ => {}
        }
    }

    /// Rewrites a source assignment into the next basic block.
    fn inline_next_block(&mut self, source_stmts: &mut Vec<Stmt>, next_stmts: &mut [Stmt]) {
        let next = BlockUseDef::analyze(next_stmts);
        let mut removable = HashSet::new();

        for (source_idx, stmt) in source_stmts.iter().enumerate() {
            let Some((sym, rhs)) = plain_assignment(stmt) else {
                continue;
            };
            if !self.can_inline_globally(sym, rhs) {
                continue;
            }
            let Some(use_idx) = next.first_read_stmt(sym) else {
                continue;
            };
            let stmt = &mut next_stmts[use_idx];
            if can_substitute_in_stmt(stmt, sym, rhs) && replace_symbol_in_stmt(stmt, sym, rhs) > 0
            {
                removable.insert(source_idx);
            }
        }

        self.remove_stmts(source_stmts, &removable);
    }

    /// Rewrites assignments into a return value pack.
    fn inline_return(&mut self, stmts: &mut Vec<Stmt>, values: &mut ValuePack) {
        if self.try_inline_tuple_return(stmts, values) {
            return;
        }

        for value in values.iter_mut() {
            self.inline_expr_from_block(stmts, value);
        }
    }

    /// Rewrites assignments from a basic block into one expression.
    fn inline_expr_from_block(&mut self, stmts: &mut Vec<Stmt>, expr: &mut Expr) {
        let block = BlockUseDef::analyze(stmts);
        let mut removable = HashSet::new();

        loop {
            let mut sources: Vec<_> = expr_read_symbols(expr)
                .into_iter()
                .filter_map(|sym| block.plain_source(sym).map(|idx| (idx, sym)))
                .filter(|(idx, _)| !removable.contains(idx))
                .collect();
            sources.sort_unstable_by_key(|(idx, _)| *idx);

            let mut changed = false;
            for (source_idx, sym) in sources {
                let Some((_, rhs)) = plain_assignment(&stmts[source_idx]) else {
                    continue;
                };
                if !self.can_inline_globally(sym, rhs) || !can_substitute_in_expr(expr, sym, rhs) {
                    continue;
                }
                if replace_symbol_in_expr(expr, sym, rhs) > 0 {
                    removable.insert(source_idx);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        self.remove_stmts(stmts, &removable);
    }

    /// Rewrites one tuple assignment directly into a return.
    fn try_inline_tuple_return(&mut self, stmts: &mut Vec<Stmt>, values: &mut ValuePack) -> bool {
        let ValuePack::Fixed(returned) = values else {
            return false;
        };
        let Some(targets) = returned
            .iter()
            .map(|expr| match expr {
                Expr::Symbol(sym) => Some(*sym),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };

        let Some((idx, source)) = self.find_tuple_source(stmts, &targets) else {
            return false;
        };
        if !self.can_inline_tuple(&source, targets.len())
            || self.value_pack_arity(&source.values) != ReturnArity::Exact(targets.len())
        {
            return false;
        }

        *values = source.values;
        stmts.remove(idx);
        self.changed = true;
        true
    }

    /// Rewrites assignments into a generic for value pack.
    fn inline_generic_for(&mut self, stmts: &mut Vec<Stmt>, exprs: &mut ValuePack) {
        if self.inline_plain_value_pack(stmts, exprs) {
            return;
        }

        let ValuePack::Fixed(expressions) = exprs else {
            return;
        };
        let Some(targets) = expressions
            .iter()
            .map(|expr| match expr {
                Expr::Symbol(sym) => Some(*sym),
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
        let ReturnArity::Exact(arity) = self.value_pack_arity(&source.values) else {
            return;
        };
        if arity > targets.len() || targets.len() > 3 {
            return;
        }

        *exprs = source.values;
        stmts.remove(idx);
        self.changed = true;
    }

    /// Rewrites plain assignments into a value pack.
    fn inline_plain_value_pack(&mut self, stmts: &mut Vec<Stmt>, exprs: &mut ValuePack) -> bool {
        let block = BlockUseDef::analyze(stmts);
        let mut removable = HashSet::new();

        for expr in exprs.iter_mut() {
            let Expr::Symbol(sym) = expr else {
                continue;
            };
            let Some(idx) = block.plain_source(*sym) else {
                continue;
            };
            let Some((_, rhs)) = plain_assignment(&stmts[idx]) else {
                continue;
            };
            if self.can_inline_globally(*sym, rhs) {
                *expr = rhs.clone();
                removable.insert(idx);
            }
        }

        let changed = !removable.is_empty();
        self.remove_stmts(stmts, &removable);
        changed
    }

    /// Rewrites plain assignments into numeric for bounds.
    fn inline_numeric_for(
        &mut self,
        stmts: &mut Vec<Stmt>,
        start: &mut Expr,
        end: &mut Expr,
        step: &mut Expr,
    ) {
        let block = BlockUseDef::analyze(stmts);
        let mut removable = HashSet::new();

        for bound in [start, end, step] {
            let Expr::Symbol(sym) = bound else {
                continue;
            };
            let Some(idx) = block.plain_source(*sym) else {
                continue;
            };
            let Some((_, rhs)) = plain_assignment(&stmts[idx]) else {
                continue;
            };
            if self.can_inline_globally(*sym, rhs) {
                *bound = rhs.clone();
                removable.insert(idx);
            }
        }

        self.remove_stmts(stmts, &removable);
    }

    /// Finds a tuple assignment with the exact target order.
    fn find_tuple_source(
        &self,
        stmts: &[Stmt],
        targets: &[SymbolId],
    ) -> Option<(usize, TupleSource)> {
        if targets.is_empty() {
            return None;
        }

        stmts.iter().enumerate().find_map(|(idx, stmt)| match stmt {
            Stmt::AssignMany { left, values } => {
                let source_targets: Vec<_> = left
                    .iter()
                    .filter_map(|expr| match expr {
                        Expr::Symbol(sym) => Some(*sym),
                        _ => None,
                    })
                    .collect();
                if source_targets != targets {
                    return None;
                }

                let fact = self.analysis.symbols.get(&targets[0])?;
                Some((
                    idx,
                    TupleSource {
                        targets: source_targets,
                        values: values.clone(),
                        group: fact.tuple_group?,
                    },
                ))
            }
            _ => None,
        })
    }

    /// Returns whether one plain assignment can move to its only global use.
    fn can_inline_globally(&self, sym: SymbolId, rhs: &Expr) -> bool {
        let Some(fact) = self.analysis.symbols.get(&sym) else {
            return false;
        };
        if fact.poisoned || fact.writes != 1 || fact.reads != 1 || rhs.reads_symbol(&sym) {
            return false;
        }
        self.can_move_rhs(fact, rhs)
    }

    /// Returns whether one assignment can move to a later use in the same block.
    fn can_inline_locally(
        &self,
        block: &BlockUseDef,
        source_idx: usize,
        use_idx: usize,
        sym: SymbolId,
        rhs: &Expr,
    ) -> bool {
        if rhs.reads_symbol(&sym) {
            return false;
        }
        let Some(fact) = self.analysis.symbols.get(&sym) else {
            return false;
        };
        if fact.poisoned || fact.writes != 1 {
            return false;
        }
        if !rhs.is_pure() && !matches!(rhs, Expr::Symbol(_)) && use_idx != source_idx + 1 {
            return false;
        }

        for source in expr_read_symbols(rhs) {
            if block.has_write_in(source, source_idx + 1, use_idx) {
                return false;
            }
            if self
                .analysis
                .symbols
                .get(&source)
                .is_some_and(|fact| fact.poisoned)
                && block.has_effect_in(source_idx + 1, use_idx)
            {
                return false;
            }
        }

        true
    }

    /// Returns whether one tuple assignment can move to its consumers.
    fn can_inline_tuple(&self, source: &TupleSource, target_count: usize) -> bool {
        if source.targets.len() != target_count || source.targets.is_empty() {
            return false;
        }
        if source
            .targets
            .iter()
            .any(|target| source.values.iter().any(|value| value.reads_symbol(target)))
        {
            return false;
        }

        for target in &source.targets {
            let Some(fact) = self.analysis.symbols.get(target) else {
                return false;
            };
            if fact.poisoned || fact.writes != 1 || fact.reads != 1 {
                return false;
            }
            if fact.tuple_group != Some(source.group) {
                return false;
            }
            if !self.can_move_value_pack(fact, &source.values) {
                return false;
            }
        }

        true
    }

    /// Returns whether an expression can move from a write to its only read.
    fn can_move_rhs(&self, fact: &SymbolUseDef, rhs: &Expr) -> bool {
        let Some(write_pos) = fact.write_pos else {
            return false;
        };
        let Some(read_pos) = fact.read_positions.last().copied() else {
            return false;
        };

        for source in expr_read_symbols(rhs) {
            let Some(source_fact) = self.analysis.symbols.get(&source) else {
                return false;
            };
            if positions_contain_in_range(&source_fact.write_positions, write_pos + 1, read_pos) {
                return false;
            }
            if source_fact.poisoned && self.has_effect_between(write_pos, read_pos) {
                return false;
            }
        }

        rhs.is_pure() || !self.has_effect_between(write_pos, read_pos)
    }

    /// Returns whether a value pack can move from a write to its only reads.
    fn can_move_value_pack(&self, fact: &SymbolUseDef, values: &ValuePack) -> bool {
        let Some(write_pos) = fact.write_pos else {
            return false;
        };
        let Some(read_pos) = fact.read_positions.last().copied() else {
            return false;
        };
        let sources: HashSet<_> = values.iter().flat_map(expr_read_symbols).collect();

        for source in sources {
            let Some(source_fact) = self.analysis.symbols.get(&source) else {
                return false;
            };
            if positions_contain_in_range(&source_fact.write_positions, write_pos + 1, read_pos) {
                return false;
            }
            if source_fact.poisoned && self.has_effect_between(write_pos, read_pos) {
                return false;
            }
        }

        values.iter().all(Expr::is_pure) || !self.has_effect_between(write_pos, read_pos)
    }

    /// Returns whether an effect occurs between two function positions.
    fn has_effect_between(&self, write_pos: usize, read_pos: usize) -> bool {
        positions_contain_in_range(&self.analysis.effect_positions, write_pos + 1, read_pos)
    }

    /// Returns the number of values produced by one expression when known.
    fn expr_arity(&self, expr: &Expr) -> ReturnArity {
        match expr {
            Expr::Call { fun, .. } => self.call_arity(fun),
            Expr::MethodCall { .. } | Expr::VarArgs => ReturnArity::Unknown,
            _ => ReturnArity::Exact(1),
        }
    }

    /// Returns the number of values produced by one value pack when known.
    fn value_pack_arity(&self, values: &ValuePack) -> ReturnArity {
        match values {
            ValuePack::Fixed(values) => ReturnArity::Exact(values.len()),
            ValuePack::Open { head, tail } => match self.expr_arity(tail) {
                ReturnArity::Exact(tail) => ReturnArity::Exact(head.len() + tail),
                ReturnArity::Unknown => ReturnArity::Unknown,
            },
        }
    }

    /// Returns the known return arity for one call target.
    fn call_arity(&self, fun: &Expr) -> ReturnArity {
        self.call_arity_inner(fun, &mut HashSet::new())
    }

    /// Resolves call arity while stopping symbol cycles.
    fn call_arity_inner(&self, fun: &Expr, seen: &mut HashSet<SymbolId>) -> ReturnArity {
        match fun {
            Expr::Global(_) => luau_libfunc_arity(fun),
            Expr::GetField { obj, .. } if matches!(&**obj, Expr::Global(_)) => {
                luau_libfunc_arity(fun)
            }
            Expr::Closure { proto, .. } => self
                .return_arities
                .get(proto.0 as usize)
                .copied()
                .unwrap_or(ReturnArity::Unknown),
            Expr::Symbol(sym) if seen.insert(*sym) => {
                let Some(source) = self
                    .analysis
                    .symbols
                    .get(sym)
                    .and_then(|fact| fact.call_source.as_ref())
                else {
                    return ReturnArity::Unknown;
                };
                match source {
                    CallSource::Builtin(expr) => luau_libfunc_arity(expr),
                    CallSource::Closure(proto) => self
                        .return_arities
                        .get(proto.0 as usize)
                        .copied()
                        .unwrap_or(ReturnArity::Unknown),
                    CallSource::Symbol(sym) => self.call_arity_inner(&Expr::Symbol(*sym), seen),
                }
            }
            _ => ReturnArity::Unknown,
        }
    }

    /// Removes statements by their positions and marks the function changed.
    fn remove_stmts(&mut self, stmts: &mut Vec<Stmt>, removable: &HashSet<usize>) {
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

/// Returns the symbols read after each node in a sequence.
fn sequence_tails(nodes: &[RegionNode], outer_tail: &HashSet<SymbolId>) -> Vec<HashSet<SymbolId>> {
    let mut tails = vec![HashSet::new(); nodes.len()];
    let mut following = outer_tail.clone();

    for idx in (0..nodes.len()).rev() {
        tails[idx] = following.clone();
        following.extend(region_read_symbols(&nodes[idx]));
    }

    tails
}

/// Returns a plain symbol assignment.
fn plain_assignment(stmt: &Stmt) -> Option<(SymbolId, &Expr)> {
    match stmt {
        Stmt::Assign {
            left: Expr::Symbol(sym),
            value,
        } => Some((*sym, value)),
        _ => None,
    }
}

/// Runs post-region inlining until every assignment is stable.
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
