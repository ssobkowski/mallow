use std::collections::HashMap;

use smallvec::SmallVec;

use crate::hil::StructuredFunction;
use crate::hil::ir::{Expr, PhiNode, Stmt, ValuePack};
use crate::hil::lifter::ssa::SymbolId;
use crate::hil::visitor::{Visitor, walk_expr};
use crate::il::ProtoId;

/// Describes a plain value which can identify a call target.
#[derive(Debug, Clone)]
pub(super) enum CallSource {
    /// A builtin path represented by a global or one field access.
    Builtin(Expr),
    /// A directly created closure.
    Closure(ProtoId),
    /// Another symbol whose definition may identify the target.
    Symbol(SymbolId),
}

impl CallSource {
    /// Extracts the small part of an expression needed for call arity.
    fn from_expr(expr: &Expr) -> Option<Self> {
        match expr {
            Expr::Global(_) => Some(Self::Builtin(expr.clone())),
            Expr::GetField { obj, .. } if matches!(&**obj, Expr::Global(_)) => {
                Some(Self::Builtin(expr.clone()))
            }
            Expr::Closure { proto, .. } => Some(Self::Closure(*proto)),
            Expr::Symbol(sym) => Some(Self::Symbol(*sym)),
            _ => None,
        }
    }
}

/// Stores every definition and use recorded for one symbol.
#[derive(Debug, Clone, Default)]
pub(super) struct SymbolUseDef {
    /// Number of writes to the symbol.
    pub(super) writes: usize,
    /// Number of reads from the symbol.
    pub(super) reads: usize,
    /// Position of the last write.
    pub(super) write_pos: Option<usize>,
    /// Sorted positions of all writes.
    pub(super) write_positions: SmallVec<[usize; 2]>,
    /// Sorted positions of all reads.
    pub(super) read_positions: SmallVec<[usize; 2]>,
    /// Small call target source from a plain assignment.
    pub(super) call_source: Option<CallSource>,
    /// Tuple group when this symbol came from a tuple assignment.
    pub(super) tuple_group: Option<usize>,
    /// Whether the symbol cannot be moved using ordinary value rules.
    pub(super) poisoned: bool,
}

impl SymbolUseDef {
    /// Records one read at the given function position.
    fn note_read(&mut self, pos: usize) {
        self.reads += 1;
        self.read_positions.push(pos);
    }

    /// Records one plain assignment at the given function position.
    fn note_plain_write(&mut self, pos: usize, rhs: &Expr) {
        self.writes += 1;
        self.write_pos = Some(pos);
        self.write_positions.push(pos);
        self.call_source = CallSource::from_expr(rhs);
        self.tuple_group = None;
    }

    /// Records one tuple assignment at the given function position.
    fn note_tuple_write(&mut self, pos: usize, group: usize) {
        self.writes += 1;
        self.write_pos = Some(pos);
        self.write_positions.push(pos);
        self.call_source = None;
        self.tuple_group = Some(group);
    }

    /// Records a write whose value cannot be moved by ordinary rules.
    fn note_unknown_write(&mut self, pos: usize) {
        self.writes += 1;
        self.write_pos = Some(pos);
        self.write_positions.push(pos);
        self.call_source = None;
        self.tuple_group = None;
        self.poisoned = true;
    }
}

/// Indexes definitions, uses, and effects for one structured function.
#[derive(Debug, Default)]
pub(super) struct FunctionUseDef {
    /// Facts indexed by symbol.
    pub(super) symbols: HashMap<SymbolId, SymbolUseDef>,
    /// Sorted positions of observable effects.
    pub(super) effect_positions: Vec<usize>,
    next_pos: usize,
    next_tuple_group: usize,
}

impl FunctionUseDef {
    /// Builds the function index used by one rewrite sweep.
    pub(super) fn analyze(fun: &StructuredFunction) -> Self {
        let span = tracing::info_span!(
            "structured_use_def_analyze",
            proto = fun.proto.0,
            symbol_count = tracing::field::Empty,
            effect_count = tracing::field::Empty,
            position_count = tracing::field::Empty,
        );
        let _enter = span.enter();

        let mut analysis = Self::default();
        for param in &fun.symbols.params {
            analysis.symbols.entry(*param).or_default().poisoned = true;
        }
        for upvalue in &fun.symbols.upvalues {
            analysis.symbols.entry(*upvalue).or_default().poisoned = true;
        }
        analysis.visit_region(&fun.root);

        span.record("symbol_count", analysis.symbols.len());
        span.record("effect_count", analysis.effect_positions.len());
        span.record("position_count", analysis.next_pos);
        analysis
    }

    /// Allocates the next position in evaluation order.
    fn alloc_pos(&mut self) -> usize {
        let pos = self.next_pos;
        self.next_pos += 1;
        pos
    }

    /// Records an effect at the given position.
    fn note_effect_at(&mut self, pos: usize) {
        self.effect_positions.push(pos);
    }

    /// Records one unknown symbol write and returns its position.
    fn note_unknown_write(&mut self, sym: SymbolId) -> usize {
        let pos = self.alloc_pos();
        self.symbols.entry(sym).or_default().note_unknown_write(pos);
        pos
    }

    /// Records one plain symbol assignment after visiting its value.
    fn note_plain_assignment(&mut self, sym: SymbolId, rhs: &Expr) {
        self.visit_expr(rhs);
        let pos = self.alloc_pos();
        self.symbols
            .entry(sym)
            .or_default()
            .note_plain_write(pos, rhs);
    }

    /// Records one tuple assignment after visiting its values.
    fn note_tuple_assignment(&mut self, targets: &[SymbolId], values: &ValuePack) {
        self.visit_value_pack(values);
        let write_pos = self.alloc_pos();
        let group = self.next_tuple_group;
        self.next_tuple_group += 1;
        for target in targets {
            self.symbols
                .entry(*target)
                .or_default()
                .note_tuple_write(write_pos, group);
        }
    }

    /// Visits an lvalue and records a direct symbol write.
    fn visit_lvalue(&mut self, expr: &Expr) {
        match expr {
            Expr::Symbol(sym) => {
                self.note_unknown_write(*sym);
            }
            other => self.visit_expr(other),
        }
    }
}

impl Visitor for FunctionUseDef {
    fn visit_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assign {
                left: Expr::Symbol(sym),
                value,
            } => self.note_plain_assignment(*sym, value),
            Stmt::Assign { left, value } => {
                self.visit_lvalue(left);
                self.visit_expr(value);
                let pos = self.alloc_pos();
                self.note_effect_at(pos);
            }
            Stmt::AssignMany { left, values } => {
                let targets: Vec<_> = left
                    .iter()
                    .filter_map(|expr| match expr {
                        Expr::Symbol(sym) => Some(*sym),
                        _ => None,
                    })
                    .collect();

                if targets.len() == left.len() {
                    self.note_tuple_assignment(&targets, values);
                } else {
                    for lvalue in left {
                        self.visit_lvalue(lvalue);
                    }
                    self.visit_value_pack(values);
                    let pos = self.alloc_pos();
                    self.note_effect_at(pos);
                }
            }
            Stmt::SetList { table, values, .. } => {
                self.visit_value_pack(values);
                let pos = self.note_unknown_write(*table);
                self.note_effect_at(pos);
            }
            Stmt::Call(expr) => self.visit_expr(expr),
            Stmt::Phi(_) => {
                unreachable!("phi nodes should have been unfolded at this point")
            }
        }
    }

    fn visit_expr(&mut self, expr: &Expr) {
        if let Expr::Symbol(sym) = expr {
            let pos = self.alloc_pos();
            self.symbols.entry(*sym).or_default().note_read(pos);
            return;
        }

        walk_expr(self, expr);
        if !expr.is_pure() {
            let pos = self.alloc_pos();
            self.note_effect_at(pos);
        }
    }

    fn visit_capture(&mut self, _: usize, sym: SymbolId) {
        self.symbols.entry(sym).or_default().poisoned = true;
    }

    fn visit_symbol(&mut self, sym: SymbolId) {
        self.note_unknown_write(sym);
    }
}

/// Stores statement positions for symbols used in one basic block.
#[derive(Debug, Default)]
pub(super) struct BlockUseDef {
    reads: HashMap<SymbolId, SmallVec<[usize; 2]>>,
    writes: HashMap<SymbolId, SmallVec<[usize; 2]>>,
    plain_sources: HashMap<SymbolId, usize>,
    effects: Vec<usize>,
}

impl BlockUseDef {
    /// Builds a block index without borrowing the statements after construction.
    pub(super) fn analyze(stmts: &[Stmt]) -> Self {
        let mut analysis = Self::default();
        for (pos, stmt) in stmts.iter().enumerate() {
            analysis.visit_stmt_at(pos, stmt);
            if stmt_has_effect(stmt) {
                analysis.effects.push(pos);
            }
        }
        analysis
    }

    /// Records the reads and writes performed by one statement.
    fn visit_stmt_at(&mut self, pos: usize, stmt: &Stmt) {
        let mut reads = StatementReadCollector {
            pos,
            reads: &mut self.reads,
        };

        match stmt {
            Stmt::Assign {
                left: Expr::Symbol(sym),
                value,
            } => {
                self.writes.entry(*sym).or_default().push(pos);
                self.plain_sources.insert(*sym, pos);
                reads.visit_expr(value);
            }
            Stmt::Assign { left, value } => {
                reads.visit_expr(left);
                reads.visit_expr(value);
            }
            Stmt::AssignMany { left, values } => {
                for lvalue in left {
                    match lvalue {
                        Expr::Symbol(sym) => self.writes.entry(*sym).or_default().push(pos),
                        other => reads.visit_expr(other),
                    }
                }
                reads.visit_value_pack(values);
            }
            Stmt::SetList { table, values, .. } => {
                self.writes.entry(*table).or_default().push(pos);
                reads.visit_value_pack(values);
            }
            Stmt::Call(expr) => reads.visit_expr(expr),
            Stmt::Phi(_) => {
                unreachable!("phi nodes should have been unfolded at this point")
            }
        }
    }

    /// Returns the only statement which reads a symbol after the source.
    pub(super) fn only_read_stmt_after(&self, sym: SymbolId, source: usize) -> Option<usize> {
        let positions = self.reads.get(&sym)?;
        let start = positions.partition_point(|pos| *pos <= source);
        let use_pos = *positions.get(start)?;
        positions[start..]
            .iter()
            .all(|pos| *pos == use_pos)
            .then_some(use_pos)
    }

    /// Returns the first statement which reads a symbol.
    pub(super) fn first_read_stmt(&self, sym: SymbolId) -> Option<usize> {
        self.reads.get(&sym)?.first().copied()
    }

    /// Returns the plain assignment position for a symbol.
    pub(super) fn plain_source(&self, sym: SymbolId) -> Option<usize> {
        self.plain_sources.get(&sym).copied()
    }

    /// Returns the number of reads in one statement.
    pub(super) fn read_count_at(&self, sym: SymbolId, pos: usize) -> usize {
        let Some(positions) = self.reads.get(&sym) else {
            return 0;
        };
        let start = positions.partition_point(|read| *read < pos);
        let end = positions.partition_point(|read| *read <= pos);
        end - start
    }

    /// Returns whether a symbol is written in the half-open range.
    pub(super) fn has_write_in(&self, sym: SymbolId, start: usize, end: usize) -> bool {
        self.writes
            .get(&sym)
            .is_some_and(|positions| positions_contain_in_range(positions, start, end))
    }

    /// Returns whether an effect occurs in the half-open range.
    pub(super) fn has_effect_in(&self, start: usize, end: usize) -> bool {
        positions_contain_in_range(&self.effects, start, end)
    }
}

/// Collects exact symbol read positions for one statement.
struct StatementReadCollector<'a> {
    pos: usize,
    reads: &'a mut HashMap<SymbolId, SmallVec<[usize; 2]>>,
}

impl Visitor for StatementReadCollector<'_> {
    fn visit_expr(&mut self, expr: &Expr) {
        if let Expr::Symbol(sym) = expr {
            self.reads.entry(*sym).or_default().push(self.pos);
            return;
        }
        walk_expr(self, expr);
    }

    fn visit_phi(&mut self, _: &PhiNode) {
        unreachable!("phi nodes should have been unfolded at this point")
    }
}

/// Returns whether a statement can change observable state.
fn stmt_has_effect(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Assign {
            left: Expr::Symbol(_),
            value,
        } => !value.is_pure(),
        Stmt::Assign { .. } => true,
        Stmt::AssignMany { left, values } => {
            left.iter().any(|left| !matches!(left, Expr::Symbol(_)))
                || values.iter().any(|value| !value.is_pure())
        }
        Stmt::SetList { .. } | Stmt::Call(_) => true,
        Stmt::Phi(_) => unreachable!("phi nodes should have been unfolded at this point"),
    }
}

/// Returns whether sorted positions contain a value in the half-open range.
pub(super) fn positions_contain_in_range(positions: &[usize], start: usize, end: usize) -> bool {
    let idx = positions.partition_point(|pos| *pos < start);
    positions.get(idx).is_some_and(|pos| *pos < end)
}
