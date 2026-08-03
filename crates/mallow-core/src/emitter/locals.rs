use std::collections::{HashMap, HashSet};

use crate::emitter::collectors::ReadCollector;
use crate::hil::StructuredFunction;
use crate::hil::cflow::region::RegionNode;
use crate::hil::ir::{Expr, Stmt, ValuePack};
use crate::hil::lifter::ssa::SymbolId;
use crate::hil::ty2::canonical::TypeId;
use crate::hil::visitor::{Visitor, walk_expr};

#[derive(Default)]
pub struct LocalPlan {
    /// Final emitted slot for each HIL symbol known to this function.
    slots: HashMap<SymbolId, usize>,
    /// Number of source-local slots reserved by this plan.
    slot_count: usize,
}

impl LocalPlan {
    /// Builds local slots for one structured function.
    pub fn build(fun: &StructuredFunction, reuse_slots: bool) -> Self {
        let mut analysis = LifetimeAnalysis::new(fun);
        analysis.visit_region(&fun.root);
        if reuse_slots && is_straight_line_region(&fun.root) {
            analysis.allocate()
        } else {
            analysis.allocate_without_reuse()
        }
    }

    pub fn slot(&self, sym: SymbolId) -> Option<usize> {
        self.slots.get(&sym).copied()
    }

    pub fn slot_count(&self) -> usize {
        self.slot_count
    }

    /// Returns the symbols known to the local planner and their emitted slots.
    pub fn symbol_slots(&self) -> Vec<(SymbolId, usize)> {
        let mut slots: Vec<_> = self.slots.iter().map(|(&sym, &slot)| (sym, slot)).collect();
        slots.sort_by_key(|(sym, _)| sym.index());
        slots
    }
}

#[derive(Default)]
struct Event {
    /// Symbols assigned by this event. Reads are kept in `last_read`; writes are
    /// needed separately so a symbol is not released before its own assignment.
    writes: HashSet<SymbolId>,
}

struct LifetimeAnalysis {
    /// Linearized source events for the final HIL tree.
    events: Vec<Event>,
    /// Symbols that must keep stable slots because source semantics observe
    /// their identity: params, upvalues, loop vars, and closure captures.
    pinned: HashSet<SymbolId>,
    /// Last event index where each symbol is read.
    last_read: HashMap<SymbolId, usize>,
    /// All symbols seen by the planner, including write-only symbols.
    mentioned: HashSet<SymbolId>,
    /// Printable graph type attached to each symbol by lifting or inference.
    annotations: HashMap<SymbolId, TypeId>,
}

impl LifetimeAnalysis {
    fn new(fun: &StructuredFunction) -> Self {
        let mut pinned = HashSet::new();
        pinned.extend(fun.symbols.params.iter().copied());
        pinned.extend(fun.symbols.upvalues.iter().copied());

        Self {
            events: Vec::new(),
            pinned,
            last_read: HashMap::new(),
            mentioned: HashSet::new(),
            annotations: fun
                .types
                .symbol_type_ids()
                .filter(|(_, ty)| fun.types.type_store().is_emittable_annotation(*ty))
                .collect(),
        }
    }

    fn allocate(self) -> LocalPlan {
        let mut allocation = SlotAllocator::default();

        let mut pinned: Vec<_> = self.pinned.iter().copied().collect();
        pinned.sort_by_key(|sym| sym.index());
        for sym in pinned {
            allocation.allocate_pinned(sym, self.annotations.get(&sym).copied());
        }

        for (event_idx, event) in self.events.iter().enumerate() {
            allocation.release_dead(event_idx, &self.last_read, &self.pinned);
            allocation.release_after_reads(event_idx, &event.writes, &self.last_read, &self.pinned);

            for &sym in &event.writes {
                if allocation.has_slot(sym) {
                    continue;
                }
                allocation.allocate(sym, &self.pinned, self.annotations.get(&sym).copied());
            }

            allocation.release_dead(event_idx + 1, &self.last_read, &self.pinned);
        }

        let mut remaining: Vec<_> = self.mentioned.into_iter().collect();
        remaining.sort_by_key(|sym| sym.index());
        for sym in remaining {
            if !allocation.has_slot(sym) {
                allocation.allocate(sym, &self.pinned, self.annotations.get(&sym).copied());
            }
        }

        allocation.finish()
    }

    fn allocate_without_reuse(self) -> LocalPlan {
        let mut symbols: Vec<_> = self.mentioned.into_iter().collect();
        symbols.sort_by_key(|sym| sym.index());

        let mut slots = HashMap::new();
        for (slot, sym) in symbols.into_iter().enumerate() {
            slots.insert(sym, slot);
        }

        LocalPlan {
            slot_count: slots.len(),
            slots,
        }
    }

    fn record_expr_event(&mut self, expr: &Expr) {
        self.pin_expr_captures(expr);
        self.record_event(ReadCollector::in_expr(expr), HashSet::new());
    }

    fn record_event(&mut self, reads: HashSet<SymbolId>, writes: HashSet<SymbolId>) {
        let event_idx = self.events.len();
        for &sym in reads.iter().chain(&writes) {
            self.mentioned.insert(sym);
        }
        for &sym in &reads {
            self.last_read.insert(sym, event_idx);
        }
        for &sym in &writes {
            self.last_read.entry(sym).or_insert(event_idx);
        }
        self.events.push(Event { writes });
    }

    fn pin_expr_captures(&mut self, expr: &Expr) {
        self.pinned.extend(CaptureCollector::collect_in(expr));
    }

    /// Pins captures and records the reads and writes of one value-pack event.
    fn record_value_pack_event(&mut self, values: &ValuePack, writes: HashSet<SymbolId>) {
        self.pinned
            .extend(CaptureCollector::collect_in_value_pack(values));
        self.record_event(ReadCollector::in_value_pack(values), writes);
    }
}

impl Visitor for LifetimeAnalysis {
    fn visit_region(&mut self, node: &RegionNode) {
        match node {
            RegionNode::BasicBlock { stmts } => {
                for stmt in stmts {
                    self.visit_stmt(stmt);
                }
            }
            RegionNode::Sequence { nodes } => {
                for node in nodes {
                    self.visit_region(node);
                }
            }
            RegionNode::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.record_expr_event(condition);
                self.visit_region(then_branch);
                if let Some(else_branch) = else_branch {
                    self.visit_region(else_branch);
                }
            }
            RegionNode::While { condition, body } => {
                self.record_expr_event(condition);
                self.visit_region(body);
            }
            RegionNode::RepeatUntil { body, condition } => {
                self.visit_region(body);
                self.record_expr_event(condition);
            }
            RegionNode::NumericFor {
                var,
                start,
                end,
                step,
                body,
            } => {
                self.pinned.insert(*var);
                self.pin_expr_captures(start);
                self.pin_expr_captures(end);
                self.pin_expr_captures(step);
                self.record_event(
                    ReadCollector::in_expr(start)
                        .into_iter()
                        .chain(ReadCollector::in_expr(end))
                        .chain(ReadCollector::in_expr(step))
                        .collect(),
                    [*var].into_iter().collect(),
                );
                self.visit_region(body);
            }
            RegionNode::GenericFor { vars, exprs, body } => {
                self.pinned.extend(vars.iter().copied());
                self.record_value_pack_event(exprs, vars.iter().copied().collect());
                self.visit_region(body);
            }
            RegionNode::Continue | RegionNode::Break => {}
            RegionNode::Return { values } => {
                self.record_value_pack_event(values, HashSet::new());
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assign { left, value } => {
                self.pin_expr_captures(value);
                let reads = ReadCollector::in_exprs([left, value]);
                let writes = symbol_lvalue(left).into_iter().collect();
                self.record_event(reads, writes);
            }
            Stmt::AssignMany { left, values } => {
                let mut reads = ReadCollector::in_exprs(left);
                reads.extend(ReadCollector::in_value_pack(values));
                let writes = left.iter().filter_map(symbol_lvalue).collect();
                self.pinned
                    .extend(CaptureCollector::collect_in_value_pack(values));
                self.record_event(reads, writes);
            }
            Stmt::SetList { table, values, .. } => {
                self.pinned
                    .extend(CaptureCollector::collect_in_value_pack(values));
                let mut reads = ReadCollector::in_value_pack(values);
                reads.insert(*table);
                self.record_event(reads, HashSet::new());
            }
            Stmt::Call(expr) => self.record_expr_event(expr),
            Stmt::Phi(phi) => {
                let reads = phi.operands.iter().map(|(_, symbol)| *symbol).collect();
                self.record_event(reads, [phi.target].into_iter().collect());
            }
        }
    }
}

fn is_straight_line_region(node: &RegionNode) -> bool {
    match node {
        RegionNode::BasicBlock { .. } | RegionNode::Return { .. } => true,
        RegionNode::Sequence { nodes } => nodes.iter().all(is_straight_line_region),
        _ => false,
    }
}

#[derive(Default)]
struct SlotAllocator {
    slots: HashMap<SymbolId, usize>,
    active: HashMap<SymbolId, usize>,
    free_slots: Vec<usize>,
    /// Declared type contract established when each source-local slot is created.
    slot_annotations: HashMap<usize, Option<TypeId>>,
    next_slot: usize,
}

impl SlotAllocator {
    fn has_slot(&self, sym: SymbolId) -> bool {
        self.slots.contains_key(&sym)
    }

    fn allocate_pinned(&mut self, sym: SymbolId, annotation: Option<TypeId>) {
        if self.has_slot(sym) {
            return;
        }
        let slot = self.next_fresh_slot();
        self.slot_annotations.insert(slot, annotation);
        self.slots.insert(sym, slot);
        self.active.insert(sym, slot);
    }

    fn allocate(&mut self, sym: SymbolId, pinned: &HashSet<SymbolId>, annotation: Option<TypeId>) {
        if pinned.contains(&sym) {
            self.allocate_pinned(sym, annotation);
            return;
        }

        let compatible = self.free_slots.iter().rposition(|slot| {
            self.slot_annotations
                .get(slot)
                .is_some_and(|contract| *contract == annotation)
        });
        let slot = compatible
            .map(|index| self.free_slots.swap_remove(index))
            .unwrap_or_else(|| {
                let slot = self.next_fresh_slot();
                self.slot_annotations.insert(slot, annotation);
                slot
            });
        self.slots.insert(sym, slot);
        self.active.insert(sym, slot);
    }

    fn release_dead(
        &mut self,
        next_event: usize,
        last_read: &HashMap<SymbolId, usize>,
        pinned: &HashSet<SymbolId>,
    ) {
        let dead: Vec<_> = self
            .active
            .keys()
            .copied()
            .filter(|sym| !pinned.contains(sym))
            .filter(|sym| last_read.get(sym).copied().unwrap_or(0) < next_event)
            .collect();

        for sym in dead {
            if let Some(slot) = self.active.remove(&sym) {
                self.free_slots.push(slot);
            }
        }
    }

    fn release_after_reads(
        &mut self,
        event_idx: usize,
        writes: &HashSet<SymbolId>,
        last_read: &HashMap<SymbolId, usize>,
        pinned: &HashSet<SymbolId>,
    ) {
        let dead: Vec<_> = self
            .active
            .keys()
            .copied()
            .filter(|sym| !pinned.contains(sym) && !writes.contains(sym))
            .filter(|sym| last_read.get(sym).copied().unwrap_or(0) == event_idx)
            .collect();

        for sym in dead {
            if let Some(slot) = self.active.remove(&sym) {
                self.free_slots.push(slot);
            }
        }
    }

    fn next_fresh_slot(&mut self) -> usize {
        let slot = self.next_slot;
        self.next_slot += 1;
        slot
    }

    fn finish(self) -> LocalPlan {
        LocalPlan {
            slots: self.slots,
            slot_count: self.next_slot,
        }
    }
}

fn symbol_lvalue(expr: &Expr) -> Option<SymbolId> {
    if let Expr::Symbol(sym) = expr {
        Some(*sym)
    } else {
        None
    }
}

#[derive(Default)]
struct CaptureCollector {
    captures: HashSet<SymbolId>,
}

impl CaptureCollector {
    fn collect_in(expr: &Expr) -> HashSet<SymbolId> {
        let mut collector = Self::default();
        collector.visit_expr(expr);
        collector.captures
    }

    /// Collects every closure capture nested in one value pack.
    fn collect_in_value_pack(values: &ValuePack) -> HashSet<SymbolId> {
        let mut collector = Self::default();
        collector.visit_value_pack(values);
        collector.captures
    }
}

impl Visitor for CaptureCollector {
    fn visit_expr(&mut self, expr: &Expr) {
        if let Expr::Closure { captures, .. } = expr {
            self.captures.extend(captures.iter().copied());
        }

        walk_expr(self, expr);
    }
}
