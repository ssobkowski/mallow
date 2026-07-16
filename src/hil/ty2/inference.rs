//! Conservative whole-program type inference over lifted SSA HIL.
//!
//! The solver separates three concepts that must not share one `merge`
//! operation:
//!
//! - producer observations form lower bounds;
//! - consumer requirements form upper bounds;
//! - control-flow edges create occurrence-specific refinements.
//!
//! Types are canonical IDs owned by one [`TypeArena`]. Inference variables and
//! mutable table objects live in separate arenas because neither is a printable
//! type. Closure, builtin-scheme, and table identities are propagated alongside
//! type bounds without pretending that those domains are structural types.

use std::collections::{HashMap, HashSet, VecDeque};

use id_arena::{Arena, Id};
use smol_str::{SmolStr, format_smolstr};

use crate::{
    hil::{
        cflow::cfg::BlockExit,
        ir::{Expr, Stmt, TableItem},
        lifted::LiftedFunction,
        lifter::ssa::SymbolId,
        ty::{FunctionTypeParam, FunctionTypeReturn, Metamethod, Type, TypeLiteral},
        ty2::{
            builtins::{BuiltinCallEffect, BuiltinEnvironment, BuiltinIndex, BuiltinPath},
            types::{MonoType, MonoTypeId, TypeArena, TypePack},
        },
        visitor::{Visitor, walk_expr},
    },
    il::ProtoId,
    operator::{BinOp, UnOp},
};

/// Durable key for an inference variable discovered while collecting HIL.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeSlot {
    /// One SSA symbol in one proto.
    Symbol(ProtoId, SymbolId),
    /// One fixed return position produced by a proto.
    Return(ProtoId, usize),
    /// One expression result without a durable HIL symbol.
    Synthetic(ProtoId, u32),
    /// One block-local occurrence narrowed by an incoming branch edge.
    Refined(ProtoId, usize, SymbolId),
}

/// Identity assigned to a table allocation during collection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct TableKey {
    /// Proto containing the allocation.
    proto: ProtoId,
    /// Allocation sequence number within the proto.
    index: u32,
}

/// Truthiness restriction carried by a CFG edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Truthiness {
    /// Values reaching the edge exclude `nil` and `false`.
    Truthy,
    /// Values reaching the edge are restricted to `nil | false`.
    Falsy,
}

impl std::ops::Not for Truthiness {
    type Output = Self;

    /// Returns the complementary branch restriction.
    fn not(self) -> Self::Output {
        match self {
            Self::Truthy => Self::Falsy,
            Self::Falsy => Self::Truthy,
        }
    }
}

/// One collected relation between HIL values.
#[derive(Debug, Clone, PartialEq)]
enum CollectedConstraint {
    /// A producer may evaluate to this concrete source type.
    Observe(Type),
    /// Values from the source slot flow into the constrained slot.
    FlowFrom(TypeSlot),
    /// Two SSA slots contain the same runtime value.
    Equal(TypeSlot),
    /// The constrained occurrence is a truthiness-filtered view of `source`.
    RefinedFrom {
        /// Unrefined definition slot.
        source: TypeSlot,
        /// Edge restriction applied to the occurrence.
        truthiness: Truthiness,
    },
    /// The constrained expression allocates one mutable table object.
    NewTable(TableKey),
    /// A table-like value receives an indexed write.
    SetIndex {
        /// Slot containing the index.
        index: TypeSlot,
        /// Slot containing the written value.
        value: TypeSlot,
    },
    /// A table-like value performs an indexed read.
    GetIndex {
        /// Slot containing the index.
        index: TypeSlot,
        /// Slot receiving the read value.
        value: TypeSlot,
    },
    /// A table-like value receives a named-field write.
    SetField {
        /// Field selected by the write.
        field: SmolStr,
        /// Slot containing the written value.
        value: TypeSlot,
        /// Whether the field is initialized by the table constructor itself.
        definite: bool,
    },
    /// A table-like value performs a named-field read.
    GetField {
        /// Field selected by the read.
        field: SmolStr,
        /// Slot receiving the read value.
        value: TypeSlot,
    },
    /// A binary operation relates two operands and one result.
    Binary {
        /// Operation performed by the expression.
        op: BinOp,
        /// Right operand slot.
        rhs: TypeSlot,
        /// Result slot.
        result: TypeSlot,
    },
    /// A unary operation relates one operand and one result.
    Unary {
        /// Operation performed by the expression.
        op: UnOp,
        /// Result slot.
        result: TypeSlot,
    },
    /// A callable value is invoked with fixed arguments and destinations.
    Call {
        /// Fixed argument slots in source order.
        args: Vec<TypeSlot>,
        /// Fixed destinations receiving returned values.
        returns: Vec<TypeSlot>,
    },
    /// Calls a field while preserving same-table field correlations.
    FieldCall {
        /// Field containing the callable value.
        callee: SmolStr,
        /// Arguments, some of which are fields of the same table object.
        args: Vec<CollectedCallArgument>,
        /// Fixed destinations receiving returned values.
        returns: Vec<TypeSlot>,
    },
    /// The constrained value is a closure for this proto.
    Closure(ProtoId),
    /// The constrained value denotes one builtin type scheme.
    Builtin(BuiltinPath),
}

impl CollectedConstraint {
    /// Returns whether this relation reads or writes `slot` as a secondary value.
    fn references_slot(&self, slot: TypeSlot) -> bool {
        match self {
            Self::Observe(_) | Self::NewTable(_) | Self::Closure(_) | Self::Builtin(_) => false,
            Self::FlowFrom(source)
            | Self::Equal(source)
            | Self::RefinedFrom { source, .. } => *source == slot,
            Self::SetIndex { index, value } | Self::GetIndex { index, value } => {
                *index == slot || *value == slot
            }
            Self::SetField { value, .. } | Self::GetField { value, .. } => *value == slot,
            Self::Binary { rhs, result, .. } => *rhs == slot || *result == slot,
            Self::Unary { result, .. } => *result == slot,
            Self::Call { args, returns } => args.iter().chain(returns).any(|value| *value == slot),
            Self::FieldCall { args, returns, .. } => {
                args.iter().any(
                    |argument| matches!(argument, CollectedCallArgument::Value(value) if *value == slot),
                ) || returns.contains(&slot)
            }
        }
    }
}

/// One argument to a table-field call before solver lowering.
#[derive(Debug, Clone, PartialEq)]
enum CollectedCallArgument {
    /// An independently collected expression value.
    Value(TypeSlot),
    /// A named field read from the same object as the callee field.
    Field(SmolStr),
}

/// Constraints and return-pack metadata collected across all protos.
#[derive(Debug, Default)]
struct CollectedProgram {
    /// Constraints grouped by their primary slot.
    constraints: HashMap<TypeSlot, Vec<CollectedConstraint>>,
    /// Largest fixed return arity observed for each proto.
    return_counts: HashMap<ProtoId, usize>,
    /// Relational field calls that can be expressed as source-level generics.
    generic_field_calls: HashMap<ProtoId, Vec<GenericFieldCall>>,
    /// Direct formal-parameter to return-slot relations proven from source constraints.
    generic_value_relations: HashMap<ProtoId, Vec<GenericValueRelation>>,
}

/// A same-table field relationship suitable for generic signature recovery.
#[derive(Debug, Clone, PartialEq, Eq)]
struct GenericFieldCall {
    /// Function parameter containing the related fields.
    parameter: SymbolId,
    /// Field invoked as the callback.
    callee: SmolStr,
    /// Callback argument positions sourced from fields of the same table.
    field_arguments: Vec<(usize, SmolStr)>,
    /// Number of fixed callback results consumed by the program.
    return_count: usize,
}

/// A direct opaque value relation suitable for source-level generic recovery.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GenericValueRelation {
    /// Formal parameter whose exact runtime value is returned.
    parameter: SymbolId,
    /// Fixed position of `parameter` in the closure signature.
    parameter_index: usize,
    /// Fixed return position receiving that same runtime value.
    return_index: usize,
}

/// Deterministic source-level generic shared by one formal and its related returns.
#[derive(Debug, Clone, PartialEq, Eq)]
struct GenericValuePlan {
    /// Formal parameter whose surface type is generalized.
    parameter: SymbolId,
    /// Fixed position of `parameter`.
    parameter_index: usize,
    /// Sorted fixed return positions rewritten to the same generic pattern.
    return_indices: Vec<usize>,
    /// Collision-free conventional generic name.
    name: SmolStr,
    /// Whether at least one callsite omitted this formal.
    optional: bool,
}

/// One named-field read resolved through SSA symbol definitions.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ResolvedFieldAccess {
    /// Canonical direct-symbol receiver after following SSA copies.
    object: SymbolId,
    /// Field selected from the receiver.
    field: SmolStr,
}

/// Collects symbols read by one expression, including closure captures.
#[derive(Default)]
struct ExpressionSymbolCollector {
    /// Symbols observed in value position.
    symbols: HashSet<SymbolId>,
}

impl ExpressionSymbolCollector {
    /// Returns every symbol read or captured by `expression`.
    fn collect(expression: &Expr) -> HashSet<SymbolId> {
        let mut collector = Self::default();
        collector.visit_expr(expression);
        collector.symbols
    }
}

impl Visitor for ExpressionSymbolCollector {
    /// Records a direct symbol read.
    fn visit_symbol(&mut self, symbol: SymbolId) {
        self.symbols.insert(symbol);
    }

    /// Treats closure capture as an escape of the captured value.
    fn visit_capture(&mut self, _index: usize, symbol: SymbolId) {
        self.symbols.insert(symbol);
    }

    /// Delegates recursive expression traversal to the shared HIL walker.
    fn visit_expr(&mut self, expression: &Expr) {
        walk_expr(self, expression);
    }
}

/// Tracks table allocations that have not been read or escaped within a block.
#[derive(Debug, Default)]
struct TableConstructionTracker {
    /// Construction root associated with each direct SSA alias.
    roots_by_symbol: HashMap<SymbolId, SymbolId>,
    /// Roots whose subsequent writes are still definite initialization.
    active_roots: HashSet<SymbolId>,
}

impl TableConstructionTracker {
    /// Starts tracking a fresh table allocation assigned to `symbol`.
    fn start(&mut self, symbol: SymbolId) {
        self.roots_by_symbol.insert(symbol, symbol);
        self.active_roots.insert(symbol);
    }

    /// Extends an active construction through one direct SSA alias.
    fn alias(&mut self, target: SymbolId, source: SymbolId) -> bool {
        let Some(root) = self.root(source) else {
            return false;
        };
        self.roots_by_symbol.insert(target, root);
        true
    }

    /// Returns whether `symbol` still denotes an unescaped construction.
    fn is_active(&self, symbol: SymbolId) -> bool {
        self.root(symbol).is_some()
    }

    /// Returns whether an expression reads any alias of `symbol`'s construction.
    fn expression_reads(&self, expression: &Expr, symbol: SymbolId) -> bool {
        let Some(root) = self.root(symbol) else {
            return false;
        };
        ExpressionSymbolCollector::collect(expression)
            .into_iter()
            .filter_map(|read| self.root(read))
            .any(|read_root| read_root == root)
    }

    /// Invalidates every active construction read or captured by `expression`.
    fn invalidate_expression(&mut self, expression: &Expr) {
        let roots: Vec<_> = ExpressionSymbolCollector::collect(expression)
            .into_iter()
            .filter_map(|symbol| self.root(symbol))
            .collect();
        for root in roots {
            self.active_roots.remove(&root);
        }
    }

    /// Returns the active construction root associated with `symbol`.
    fn root(&self, symbol: SymbolId) -> Option<SymbolId> {
        let root = self.roots_by_symbol.get(&symbol).copied()?;
        self.active_roots.contains(&root).then_some(root)
    }
}

impl CollectedProgram {
    /// Ensures that `slot` participates in solver construction.
    fn ensure_slot(&mut self, slot: TypeSlot) {
        self.constraints.entry(slot).or_default();
    }

    /// Adds a constraint unless the same relation was already collected.
    fn push(&mut self, slot: TypeSlot, constraint: CollectedConstraint) {
        let constraints = self.constraints.entry(slot).or_default();
        if !constraints.contains(&constraint) {
            constraints.push(constraint);
        }
    }

    /// Merges one proto's constraints into the whole-program graph.
    fn extend(&mut self, other: Self) {
        for (slot, constraints) in other.constraints {
            for constraint in constraints {
                self.push(slot, constraint);
            }
        }
        for (proto, count) in other.return_counts {
            self.return_counts
                .entry(proto)
                .and_modify(|existing| *existing = (*existing).max(count))
                .or_insert(count);
        }
        for (proto, calls) in other.generic_field_calls {
            let existing = self.generic_field_calls.entry(proto).or_default();
            for call in calls {
                if !existing.contains(&call) {
                    existing.push(call);
                }
            }
        }
        for (proto, relations) in other.generic_value_relations {
            let existing = self.generic_value_relations.entry(proto).or_default();
            existing.extend(relations);
            existing.sort_by_key(|relation| (relation.parameter_index, relation.return_index));
            existing.dedup();
        }
    }

    /// Proves direct opaque parameter-to-return relations from collected source edges.
    ///
    /// The proof deliberately rejects aliases and operations: a return position must
    /// contain only a direct `FlowFrom` edge from one formal, every concrete exit must
    /// supply that position, and the formal may participate in no other relation.
    fn direct_value_relations(
        &self,
        proto: ProtoId,
        parameters: &[SymbolId],
        return_lengths: &[usize],
        non_return_uses: &HashSet<SymbolId>,
    ) -> Vec<GenericValueRelation> {
        let return_count = return_lengths.iter().copied().max().unwrap_or(0);
        let mut candidates = Vec::new();
        for return_index in 0..return_count {
            if return_lengths.is_empty()
                || return_lengths.iter().any(|length| *length <= return_index)
            {
                continue;
            }
            let Some(constraints) = self.constraints.get(&TypeSlot::Return(proto, return_index))
            else {
                continue;
            };
            let mut parameter = None;
            let mut valid = !constraints.is_empty();
            for constraint in constraints {
                let CollectedConstraint::FlowFrom(TypeSlot::Symbol(owner, symbol)) = constraint
                else {
                    valid = false;
                    break;
                };
                let Some(parameter_index) = (*owner == proto)
                    .then(|| parameters.iter().position(|item| item == symbol))
                    .flatten()
                else {
                    valid = false;
                    break;
                };
                let relation = (*symbol, parameter_index);
                if parameter.is_some_and(|existing| existing != relation) {
                    valid = false;
                    break;
                }
                parameter = Some(relation);
            }
            if valid
                && let Some((parameter, parameter_index)) = parameter
                && !non_return_uses.contains(&parameter)
            {
                candidates.push(GenericValueRelation {
                    parameter,
                    parameter_index,
                    return_index,
                });
            }
        }

        let mut correlated_returns: HashMap<SymbolId, HashSet<usize>> = HashMap::new();
        for relation in &candidates {
            correlated_returns
                .entry(relation.parameter)
                .or_default()
                .insert(relation.return_index);
        }
        candidates.retain(|relation| {
            let formal = TypeSlot::Symbol(proto, relation.parameter);
            self.constraints.iter().all(|(primary, constraints)| {
                constraints.iter().all(|constraint| {
                    if *primary == formal {
                        return false;
                    }
                    if !constraint.references_slot(formal) {
                        return true;
                    }
                    matches!(
                        (primary, constraint),
                        (
                            TypeSlot::Return(owner, return_index),
                            CollectedConstraint::FlowFrom(source),
                        ) if *owner == proto
                            && *source == formal
                            && correlated_returns
                                .get(&relation.parameter)
                                .is_some_and(|returns| returns.contains(return_index))
                    )
                })
            })
        });
        candidates.sort_by_key(|relation| (relation.parameter_index, relation.return_index));
        candidates.dedup();
        candidates
    }

    /// Stores the deterministic direct-value relation plan for one proto.
    fn record_direct_value_relations(
        &mut self,
        proto: ProtoId,
        parameters: &[SymbolId],
        return_lengths: &[usize],
        non_return_uses: &HashSet<SymbolId>,
    ) {
        let relations =
            self.direct_value_relations(proto, parameters, return_lengths, non_return_uses);
        if !relations.is_empty() {
            self.generic_value_relations.insert(proto, relations);
        }
    }
}

/// Collects constraints from one lifted SSA proto.
struct ConstraintCollector<'a> {
    /// Proto currently being scanned.
    proto: ProtoId,
    /// All lifted functions, indexed by proto ID.
    functions: &'a [LiftedFunction],
    /// Shared builtin environment used only for path recognition.
    builtins: &'a BuiltinEnvironment,
    /// Constraints accumulated for the current proto.
    program: CollectedProgram,
    /// Next expression-only slot number.
    next_synthetic: u32,
    /// Next table allocation number.
    next_table: u32,
    /// Index of the CFG block currently being collected.
    current_block: usize,
    /// Truthiness facts that hold on every path entering each block.
    block_refinements: Vec<HashMap<SymbolId, Truthiness>>,
    /// Fixed return arity of every concrete return exit in this proto.
    return_lengths: Vec<usize>,
    /// Symbols that are formal parameters of the current proto.
    parameters: HashSet<SymbolId>,
    /// Formal parameters observed outside their direct return positions.
    non_return_parameter_uses: HashSet<SymbolId>,
    /// Block-local table allocations that have not escaped before initialization.
    constructions: TableConstructionTracker,
    /// Unique SSA definitions used to recover value provenance at calls.
    definitions: HashMap<SymbolId, Expr>,
    /// Symbols backed by nonlocal upvalue storage rather than private SSA locals.
    upvalues: HashSet<SymbolId>,
}

impl<'a> ConstraintCollector<'a> {
    /// Collects one lifted function into proto-qualified constraints.
    fn collect(
        function: &LiftedFunction,
        functions: &'a [LiftedFunction],
        builtins: &'a BuiltinEnvironment,
    ) -> CollectedProgram {
        let block_refinements = Self::compute_block_refinements(function);
        let definitions = Self::collect_definitions(function);
        let mut collector = Self {
            proto: function.proto,
            functions,
            builtins,
            program: CollectedProgram::default(),
            next_synthetic: 0,
            next_table: 0,
            current_block: 0,
            block_refinements,
            return_lengths: Vec::new(),
            parameters: function.symbols.params.iter().copied().collect(),
            non_return_parameter_uses: HashSet::new(),
            constructions: TableConstructionTracker::default(),
            definitions,
            upvalues: function.symbols.upvalues.iter().copied().collect(),
        };

        for (block_index, block) in function.cfg.blocks().enumerate() {
            collector.current_block = block_index;
            collector.constructions = TableConstructionTracker::default();
            for statement in block.stmts() {
                collector.collect_statement(statement);
            }
            collector.collect_exit(block.exit());
        }
        collector.complete_return_pack();
        collector.program.record_direct_value_relations(
            collector.proto,
            &function.symbols.params,
            &collector.return_lengths,
            &collector.non_return_parameter_uses,
        );
        collector.program
    }

    /// Collects direct symbol definitions from the SSA graph.
    fn collect_definitions(function: &LiftedFunction) -> HashMap<SymbolId, Expr> {
        let mut definitions = HashMap::new();
        for block in function.cfg.blocks() {
            for statement in block.stmts() {
                match statement {
                    Stmt::Assign {
                        left: Expr::Symbol(symbol),
                        value,
                    } => {
                        definitions.insert(*symbol, value.clone());
                    }
                    Stmt::AssignMany { left, value } => {
                        if let Some(Expr::Symbol(symbol)) = left.first() {
                            definitions.insert(*symbol, value.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        definitions
    }

    /// Computes refinements that hold on every incoming edge of each CFG block.
    fn compute_block_refinements(function: &LiftedFunction) -> Vec<HashMap<SymbolId, Truthiness>> {
        let blocks: Vec<_> = function.cfg.blocks().collect();
        if blocks.is_empty() {
            return Vec::new();
        }

        let mut incoming = vec![None::<HashMap<SymbolId, Truthiness>>; blocks.len()];
        incoming[0] = Some(HashMap::new());
        let mut queue = VecDeque::from([0usize]);
        let mut queued = HashSet::from([0usize]);

        while let Some(block_index) = queue.pop_front() {
            queued.remove(&block_index);
            let Some(base) = incoming[block_index].clone() else {
                continue;
            };

            let mut outgoing = Vec::new();
            match blocks[block_index].exit() {
                BlockExit::CondJump {
                    cond,
                    then_block,
                    else_block,
                } => {
                    let mut truthy = base.clone();
                    let mut falsy = base;
                    if let Some((symbol, condition_truthiness)) = Self::condition_symbol(cond) {
                        truthy.insert(symbol, condition_truthiness);
                        falsy.insert(symbol, !condition_truthiness);
                    }
                    outgoing.push((*then_block, truthy));
                    outgoing.push((*else_block, falsy));
                }
                exit => {
                    for target in exit.targets().into_iter().flatten() {
                        outgoing.push((target, base.clone()));
                    }
                }
            }

            for (target, candidate) in outgoing {
                if target >= incoming.len() {
                    continue;
                }
                let changed = match &mut incoming[target] {
                    None => {
                        incoming[target] = Some(candidate);
                        true
                    }
                    Some(existing) => {
                        let old_len = existing.len();
                        existing.retain(|symbol, fact| candidate.get(symbol) == Some(fact));
                        existing.len() != old_len
                    }
                };
                if changed && queued.insert(target) {
                    queue.push_back(target);
                }
            }
        }

        incoming
            .into_iter()
            .map(Option::unwrap_or_default)
            .collect()
    }

    /// Recognizes a direct symbol truthiness test, optionally under `not`.
    fn condition_symbol(condition: &Expr) -> Option<(SymbolId, Truthiness)> {
        match condition {
            Expr::Symbol(symbol) => Some((*symbol, Truthiness::Truthy)),
            Expr::Unary {
                op: UnOp::Not,
                expr,
            } => match expr.as_ref() {
                Expr::Symbol(symbol) => Some((*symbol, Truthiness::Falsy)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Allocates a unique synthetic expression slot.
    fn synthetic_slot(&mut self) -> TypeSlot {
        let slot = TypeSlot::Synthetic(self.proto, self.next_synthetic);
        self.next_synthetic = self
            .next_synthetic
            .checked_add(1)
            .expect("one proto exhausted synthetic type-slot IDs");
        self.program.ensure_slot(slot);
        slot
    }

    /// Allocates a unique identity for one table constructor.
    fn table_key(&mut self) -> TableKey {
        let key = TableKey {
            proto: self.proto,
            index: self.next_table,
        };
        self.next_table = self
            .next_table
            .checked_add(1)
            .expect("one proto exhausted inferred table IDs");
        key
    }

    /// Returns the definition slot for `symbol` without block refinement.
    fn symbol_slot(&mut self, symbol: SymbolId) -> TypeSlot {
        let slot = TypeSlot::Symbol(self.proto, symbol);
        self.program.ensure_slot(slot);
        slot
    }

    /// Returns a symbol definition slot belonging to an arbitrary proto.
    fn symbol_slot_for(&mut self, proto: ProtoId, symbol: SymbolId) -> TypeSlot {
        let slot = TypeSlot::Symbol(proto, symbol);
        self.program.ensure_slot(slot);
        slot
    }

    /// Returns the block-refined occurrence slot for a symbol read when needed.
    fn symbol_read_slot(&mut self, symbol: SymbolId) -> TypeSlot {
        let Some(truthiness) = self
            .block_refinements
            .get(self.current_block)
            .and_then(|facts| facts.get(&symbol))
            .copied()
        else {
            return self.symbol_slot(symbol);
        };

        let source = self.symbol_slot(symbol);
        let occurrence = TypeSlot::Refined(self.proto, self.current_block, symbol);
        self.program.push(
            occurrence,
            CollectedConstraint::RefinedFrom { source, truthiness },
        );
        occurrence
    }

    /// Collects one statement and its value-flow effects.
    fn collect_statement(&mut self, statement: &Stmt) {
        match statement {
            Stmt::Assign { left, value } => {
                let definite = self.initializes_active_field(left, value);
                if matches!(value, Expr::Call { .. } | Expr::MethodCall { .. }) {
                    let result = self.synthetic_for_lvalue(left, definite);
                    self.collect_call(value, vec![result]);
                } else {
                    let value_slot = self.collect_expression(value);
                    self.assign_lvalue(left, value_slot, definite);
                }
                self.update_construction_after_assignment(left, value);
            }
            Stmt::AssignMany { left, value } => {
                if matches!(value, Expr::Call { .. } | Expr::MethodCall { .. }) {
                    let returns = left
                        .iter()
                        .map(|lvalue| self.synthetic_for_lvalue(lvalue, false))
                        .collect();
                    self.collect_call(value, returns);
                } else if let Some((first, rest)) = left.split_first() {
                    let value = self.collect_expression(value);
                    self.assign_lvalue(first, value, false);
                    for lvalue in rest {
                        let nil = self.synthetic_slot();
                        self.program
                            .push(nil, CollectedConstraint::Observe(Type::Nil));
                        self.assign_lvalue(lvalue, nil, false);
                    }
                }
                self.constructions.invalidate_expression(value);
                for lvalue in left {
                    self.invalidate_noninitializing_lvalue(lvalue);
                }
            }
            Stmt::SetList {
                table,
                values,
                has_variadic_tail,
                ..
            } => {
                let table = self.symbol_slot(*table);
                for value in values {
                    let index = self.synthetic_slot();
                    self.program
                        .push(index, CollectedConstraint::Observe(Type::Number));
                    let value = self.collect_expression(value);
                    self.program
                        .push(table, CollectedConstraint::SetIndex { index, value });
                }
                if *has_variadic_tail {
                    let index = self.synthetic_slot();
                    let value = self.synthetic_slot();
                    self.program
                        .push(table, CollectedConstraint::SetIndex { index, value });
                }
                for value in values {
                    self.constructions.invalidate_expression(value);
                }
            }
            Stmt::Call(call) => {
                self.collect_call(call, Vec::new());
                self.constructions.invalidate_expression(call);
            }
            Stmt::Phi(phi) => {
                let target = self.symbol_slot(phi.target);
                for &(_, operand) in &phi.operands {
                    let operand = self.symbol_slot(operand);
                    self.program
                        .push(target, CollectedConstraint::FlowFrom(operand));
                }
            }
        }
    }

    /// Returns whether a named-field write is definite constructor initialization.
    fn initializes_active_field(&self, lvalue: &Expr, value: &Expr) -> bool {
        let Expr::GetField { obj, .. } = lvalue else {
            return false;
        };
        let Expr::Symbol(table) = obj.as_ref() else {
            return false;
        };
        self.constructions.is_active(*table) && !self.constructions.expression_reads(value, *table)
    }

    /// Updates block-local construction state after one ordinary assignment.
    fn update_construction_after_assignment(&mut self, lvalue: &Expr, value: &Expr) {
        match (lvalue, value) {
            (Expr::Symbol(target), Expr::Table { .. }) => {
                self.constructions.invalidate_expression(value);
                if !self.upvalues.contains(target) {
                    self.constructions.start(*target);
                }
            }
            (Expr::Symbol(target), Expr::Symbol(source))
                if !self.upvalues.contains(target)
                    && self.constructions.alias(*target, *source) => {}
            (Expr::GetField { obj, .. }, _) | (Expr::GetIndex { obj, .. }, _) if matches!(obj.as_ref(), Expr::Symbol(table) if self.constructions.is_active(*table)) =>
            {
                self.constructions.invalidate_expression(value);
                if let Expr::GetIndex { index, .. } = lvalue {
                    self.constructions.invalidate_expression(index);
                }
            }
            _ => {
                self.constructions.invalidate_expression(value);
                self.invalidate_noninitializing_lvalue(lvalue);
            }
        }
    }

    /// Invalidates construction values read by a non-initializing lvalue.
    fn invalidate_noninitializing_lvalue(&mut self, lvalue: &Expr) {
        match lvalue {
            Expr::GetField { obj, .. } => self.constructions.invalidate_expression(obj),
            Expr::GetIndex { obj, index } => {
                self.constructions.invalidate_expression(obj);
                self.constructions.invalidate_expression(index);
            }
            _ => {}
        }
    }

    /// Creates a call destination and wires it to an arbitrary lvalue.
    fn synthetic_for_lvalue(&mut self, lvalue: &Expr, definite: bool) -> TypeSlot {
        let result = self.synthetic_slot();
        self.assign_lvalue(lvalue, result, definite);
        result
    }

    /// Adds assignment relations for one supported HIL lvalue.
    fn assign_lvalue(&mut self, lvalue: &Expr, value: TypeSlot, definite: bool) {
        match lvalue {
            Expr::Symbol(symbol) => {
                let target = self.symbol_slot(*symbol);
                if matches!(value, TypeSlot::Symbol(_, _)) {
                    self.program.push(target, CollectedConstraint::Equal(value));
                } else {
                    self.program
                        .push(target, CollectedConstraint::FlowFrom(value));
                }
            }
            Expr::GetField { obj, field } => {
                let object = self.collect_expression(obj);
                self.program.push(
                    object,
                    CollectedConstraint::SetField {
                        field: field.clone(),
                        value,
                        definite,
                    },
                );
            }
            Expr::GetIndex { obj, index } => {
                let object = self.collect_expression(obj);
                let index = self.collect_expression(index);
                self.program
                    .push(object, CollectedConstraint::SetIndex { index, value });
            }
            _ => {
                // Malformed lvalues can appear only after an upstream lifting
                // defect. Keeping value flow one-way avoids manufacturing an
                // equality relation for an expression that is not storage.
                let target = self.collect_expression(lvalue);
                self.program
                    .push(target, CollectedConstraint::FlowFrom(value));
            }
        }
    }

    /// Collects one call expression using caller-provided return destinations.
    fn collect_call(&mut self, expression: &Expr, returns: Vec<TypeSlot>) {
        match expression {
            Expr::Call { fun, args } => {
                if let Some(callee) = self.resolve_field_access(fun) {
                    let object = self.symbol_read_slot(callee.object);
                    let field_arguments: Vec<_> = args
                        .iter()
                        .enumerate()
                        .filter_map(|(index, argument)| {
                            let argument = self.resolve_field_access(argument)?;
                            (argument.object == callee.object).then_some((index, argument.field))
                        })
                        .collect();
                    if self.parameters.contains(&callee.object) && !field_arguments.is_empty() {
                        let call = GenericFieldCall {
                            parameter: callee.object,
                            callee: callee.field.clone(),
                            field_arguments,
                            return_count: returns.len(),
                        };
                        let calls = self
                            .program
                            .generic_field_calls
                            .entry(self.proto)
                            .or_default();
                        if !calls.contains(&call) {
                            calls.push(call);
                        }
                    }
                    let args = args
                        .iter()
                        .map(|argument| {
                            if let Some(argument) = self.resolve_field_access(argument)
                                && argument.object == callee.object
                            {
                                return CollectedCallArgument::Field(argument.field);
                            }
                            CollectedCallArgument::Value(self.collect_expression(argument))
                        })
                        .collect();
                    self.program.push(
                        object,
                        CollectedConstraint::FieldCall {
                            callee: callee.field,
                            args,
                            returns,
                        },
                    );
                    return;
                }
                let callee = self.collect_expression(fun);
                let args = args
                    .iter()
                    .map(|argument| self.collect_expression(argument))
                    .collect();
                self.program
                    .push(callee, CollectedConstraint::Call { args, returns });
            }
            Expr::MethodCall {
                object,
                method,
                args,
            } => {
                let object = self.collect_expression(object);
                let callee = self.synthetic_slot();
                self.program.push(
                    object,
                    CollectedConstraint::GetField {
                        field: method.clone(),
                        value: callee,
                    },
                );
                let mut call_args = Vec::with_capacity(args.len() + 1);
                call_args.push(object);
                call_args.extend(
                    args.iter()
                        .map(|argument| self.collect_expression(argument)),
                );
                self.program.push(
                    callee,
                    CollectedConstraint::Call {
                        args: call_args,
                        returns,
                    },
                );
            }
            _ => unreachable!("call collector requires a HIL call expression"),
        }
    }

    /// Resolves one named-field read through direct SSA definitions and copies.
    fn resolve_field_access(&self, expression: &Expr) -> Option<ResolvedFieldAccess> {
        self.resolve_field_access_inner(expression, &mut HashSet::new())
    }

    /// Recursively resolves a field read while rejecting malformed definition cycles.
    fn resolve_field_access_inner(
        &self,
        expression: &Expr,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<ResolvedFieldAccess> {
        match expression {
            Expr::GetField { obj, field } => Some(ResolvedFieldAccess {
                object: self.resolve_alias_expression(obj, &mut HashSet::new())?,
                field: field.clone(),
            }),
            Expr::Symbol(symbol) if visiting.insert(*symbol) => self
                .definitions
                .get(symbol)
                .and_then(|definition| self.resolve_field_access_inner(definition, visiting)),
            _ => None,
        }
    }

    /// Resolves a direct symbol expression through SSA copy definitions.
    fn resolve_alias_expression(
        &self,
        expression: &Expr,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<SymbolId> {
        let Expr::Symbol(symbol) = expression else {
            return None;
        };
        self.resolve_alias_symbol(*symbol, visiting)
    }

    /// Resolves one symbol through direct SSA copy definitions.
    fn resolve_alias_symbol(
        &self,
        symbol: SymbolId,
        visiting: &mut HashSet<SymbolId>,
    ) -> Option<SymbolId> {
        if !visiting.insert(symbol) {
            return None;
        }
        match self.definitions.get(&symbol) {
            Some(Expr::Symbol(source)) => self.resolve_alias_symbol(*source, visiting),
            _ => Some(symbol),
        }
    }

    /// Collects one expression and returns the slot containing its value.
    ///
    /// This is intentionally recursive rather than a `Visitor`: each child must
    /// return a distinct inference slot to its parent relation.
    fn collect_expression(&mut self, expression: &Expr) -> TypeSlot {
        if let Some(path) = BuiltinPath::from_expr(expression)
            && self.builtins.get_path(&path).is_some()
        {
            let slot = self.synthetic_slot();
            self.program.push(slot, CollectedConstraint::Builtin(path));
            return slot;
        }

        match expression {
            Expr::Symbol(symbol) => {
                if self.parameters.contains(symbol) {
                    self.non_return_parameter_uses.insert(*symbol);
                }
                self.symbol_read_slot(*symbol)
            }
            Expr::Nil => {
                let slot = self.synthetic_slot();
                self.program
                    .push(slot, CollectedConstraint::Observe(Type::Nil));
                slot
            }
            Expr::Number(_) => {
                let slot = self.synthetic_slot();
                self.program
                    .push(slot, CollectedConstraint::Observe(Type::Number));
                slot
            }
            Expr::String(value) => {
                let slot = self.synthetic_slot();
                self.program.push(
                    slot,
                    CollectedConstraint::Observe(Type::Literal(TypeLiteral::String(value.clone()))),
                );
                slot
            }
            Expr::Bool(value) => {
                let slot = self.synthetic_slot();
                self.program.push(
                    slot,
                    CollectedConstraint::Observe(Type::Literal(TypeLiteral::Boolean(*value))),
                );
                slot
            }
            Expr::Closure { proto, captures } => {
                let slot = self.synthetic_slot();
                self.program
                    .push(slot, CollectedConstraint::Closure(*proto));
                if let Some(function) = self.functions.get(proto.0 as usize) {
                    for (index, capture) in captures.iter().enumerate() {
                        let Some(upvalue) = function.symbols.upvalues.get(index) else {
                            continue;
                        };
                        let parent = self.symbol_slot(*capture);
                        let child = self.symbol_slot_for(*proto, *upvalue);
                        self.program.push(parent, CollectedConstraint::Equal(child));
                    }
                }
                slot
            }
            Expr::Global(_) | Expr::VarArgs => self.synthetic_slot(),
            Expr::Table { items } => {
                let table = self.synthetic_slot();
                let key = self.table_key();
                self.program.push(table, CollectedConstraint::NewTable(key));
                for item in items {
                    match item {
                        TableItem::List(value) => {
                            let index = self.synthetic_slot();
                            self.program
                                .push(index, CollectedConstraint::Observe(Type::Number));
                            let value = self.collect_expression(value);
                            self.program
                                .push(table, CollectedConstraint::SetIndex { index, value });
                        }
                        TableItem::Index(Expr::String(field), value) => {
                            let value = self.collect_expression(value);
                            self.program.push(
                                table,
                                CollectedConstraint::SetField {
                                    field: field.as_str().into(),
                                    value,
                                    definite: true,
                                },
                            );
                        }
                        TableItem::Index(index, value) => {
                            let index = self.collect_expression(index);
                            let value = self.collect_expression(value);
                            self.program
                                .push(table, CollectedConstraint::SetIndex { index, value });
                        }
                    }
                }
                table
            }
            Expr::Call { .. } | Expr::MethodCall { .. } => {
                let result = self.synthetic_slot();
                self.collect_call(expression, vec![result]);
                result
            }
            Expr::Binary { lhs, op, rhs } => {
                let lhs = self.collect_expression(lhs);
                let rhs = self.collect_expression(rhs);
                let result = self.synthetic_slot();
                self.program.push(
                    lhs,
                    CollectedConstraint::Binary {
                        op: *op,
                        rhs,
                        result,
                    },
                );
                result
            }
            Expr::Unary { op, expr } => {
                let operand = self.collect_expression(expr);
                let result = self.synthetic_slot();
                self.program
                    .push(operand, CollectedConstraint::Unary { op: *op, result });
                result
            }
            Expr::GetField { obj, field } => {
                let object = self.collect_expression(obj);
                let value = self.synthetic_slot();
                self.program.push(
                    object,
                    CollectedConstraint::GetField {
                        field: field.clone(),
                        value,
                    },
                );
                value
            }
            Expr::GetIndex { obj, index } => {
                let object = self.collect_expression(obj);
                let index = self.collect_expression(index);
                let value = self.synthetic_slot();
                self.program
                    .push(object, CollectedConstraint::GetIndex { index, value });
                value
            }
            Expr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => {
                self.collect_expression(condition);
                let then_value = self.collect_expression(then_expr);
                let else_value = self.collect_expression(else_expr);
                let result = self.synthetic_slot();
                self.program
                    .push(result, CollectedConstraint::FlowFrom(then_value));
                self.program
                    .push(result, CollectedConstraint::FlowFrom(else_value));
                result
            }
        }
    }

    /// Collects facts encoded by one terminating CFG edge.
    fn collect_exit(&mut self, exit: &BlockExit) {
        match exit {
            BlockExit::CondJump { cond, .. } => {
                self.collect_expression(cond);
            }
            BlockExit::Return(values) => {
                self.return_lengths.push(values.len());
                for (index, value) in values.iter().enumerate() {
                    // A bare formal in return position is the only parameter use
                    // exempt from opacity tracking; all nested expressions consume it.
                    let value = match value {
                        Expr::Symbol(symbol) if self.parameters.contains(symbol) => {
                            self.symbol_read_slot(*symbol)
                        }
                        _ => self.collect_expression(value),
                    };
                    let result = TypeSlot::Return(self.proto, index);
                    self.program
                        .push(result, CollectedConstraint::FlowFrom(value));
                }
            }
            BlockExit::FornPrep {
                var,
                start,
                end,
                step,
                ..
            } => {
                let variable = self.symbol_slot(*var);
                self.program
                    .push(variable, CollectedConstraint::Observe(Type::Number));
                self.collect_expression(start);
                self.collect_expression(end);
                self.collect_expression(step);
            }
            BlockExit::ForgPrep { exprs, .. } => {
                for expression in exprs {
                    self.collect_expression(expression);
                }
            }
            BlockExit::ForgLoop { vars, .. } => {
                for variable in vars {
                    self.symbol_slot(*variable);
                }
            }
            BlockExit::FornLoop { .. } | BlockExit::Jump(_) | BlockExit::Fallthrough(_) => {}
        }
    }

    /// Adds `nil` to return positions omitted by shorter return exits.
    fn complete_return_pack(&mut self) {
        let return_count = self.return_lengths.iter().copied().max().unwrap_or(0);
        self.program.return_counts.insert(self.proto, return_count);
        for length in self.return_lengths.iter().copied() {
            for index in length..return_count {
                self.program.push(
                    TypeSlot::Return(self.proto, index),
                    CollectedConstraint::Observe(Type::Nil),
                );
            }
        }
    }
}

/// Stable handle for one solver inference variable.
type InferenceVarId = Id<InferenceVariable>;

/// Stable handle for one inferred mutable table object.
type TableObjectId = Id<TableObject>;

/// Bounds and identity facts associated with one inference variable.
#[derive(Debug, Clone)]
struct InferenceVariable {
    /// Union of concrete producer observations.
    lower: MonoTypeId,
    /// Intersection of consumer requirements.
    upper: MonoTypeId,
    /// Concrete closure identities carried by the value.
    closures: HashSet<ProtoId>,
    /// Mutable table identities carried by the value.
    tables: HashSet<TableObjectId>,
    /// Builtin schemes carried by the value.
    builtins: HashSet<BuiltinPath>,
}

/// One inferred named field in a mutable table object.
#[derive(Debug, Clone, Copy)]
struct TableField {
    /// Variable accumulating values written to the field.
    value: InferenceVarId,
    /// Whether a table constructor definitely initialized the field.
    definite: bool,
}

/// Mutable heap-shape facts for one table allocation.
#[derive(Debug)]
struct TableObject {
    /// Variable accumulating dynamic index keys.
    keys: InferenceVarId,
    /// Variable accumulating dynamic index values.
    values: InferenceVarId,
    /// Named fields observed on the allocation.
    fields: HashMap<SmolStr, TableField>,
    /// Table allocations installed as metatables.
    metatables: HashSet<TableObjectId>,
}

/// One solver-native constraint referencing arena variables directly.
#[derive(Debug, Clone, PartialEq)]
enum SolverConstraint {
    /// Adds a producer observation to the constrained variable.
    Observe(MonoTypeId),
    /// Narrows the constrained variable to a consumer-accepted type.
    Require(MonoTypeId),
    /// Propagates a subtype edge from `source` into the constrained variable.
    FlowFrom(InferenceVarId),
    /// Equates the constrained variable and `other`.
    Equal(InferenceVarId),
    /// Creates a truthiness-filtered occurrence from `source`.
    RefinedFrom {
        /// Unrefined definition variable.
        source: InferenceVarId,
        /// Edge restriction applied to the occurrence.
        truthiness: Truthiness,
    },
    /// Adds one mutable table identity.
    NewTable(TableObjectId),
    /// Applies an indexed write to every known table identity.
    SetIndex {
        /// Index variable.
        index: InferenceVarId,
        /// Written value variable.
        value: InferenceVarId,
    },
    /// Applies an indexed read to every known table identity.
    GetIndex {
        /// Index variable.
        index: InferenceVarId,
        /// Read destination variable.
        value: InferenceVarId,
    },
    /// Applies a named-field write to every known table identity.
    SetField {
        /// Field selected by the write.
        field: SmolStr,
        /// Written value variable.
        value: InferenceVarId,
        /// Whether the constructor definitely initializes the field.
        definite: bool,
    },
    /// Applies a named-field read to every known table identity.
    GetField {
        /// Field selected by the read.
        field: SmolStr,
        /// Read destination variable.
        value: InferenceVarId,
    },
    /// Relates a binary expression's operands and result.
    Binary {
        /// Binary operation.
        op: BinOp,
        /// Right operand variable.
        rhs: InferenceVarId,
        /// Result variable.
        result: InferenceVarId,
    },
    /// Relates a unary expression's operand and result.
    Unary {
        /// Unary operation.
        op: UnOp,
        /// Result variable.
        result: InferenceVarId,
    },
    /// Calls the constrained variable.
    Call {
        /// Fixed argument variables.
        args: Vec<InferenceVarId>,
        /// Fixed return destinations.
        returns: Vec<InferenceVarId>,
    },
    /// Calls one field separately for each concrete receiver table.
    FieldCall {
        /// Field containing the callable value.
        callee: SmolStr,
        /// Arguments retaining same-table field provenance.
        args: Vec<SolverCallArgument>,
        /// Fixed return destinations.
        returns: Vec<InferenceVarId>,
    },
    /// Adds one concrete closure identity.
    Closure(ProtoId),
    /// Adds one builtin scheme identity.
    Builtin(BuiltinPath),
    /// Links table objects through `setmetatable`.
    SetMetatable {
        /// Variable containing metatable identities.
        metatable: InferenceVarId,
        /// Optional destination receiving the base value.
        result: Option<InferenceVarId>,
    },
    /// Observes values stored in a table after excluding deletion-by-`nil`.
    NonNilFrom {
        /// Written value whose `nil` alternative does not remain stored.
        source: InferenceVarId,
    },
    /// Observes a source variable after excluding concrete scheme alternatives.
    GenericFrom {
        /// Argument variable supplying generic evidence.
        source: InferenceVarId,
        /// Concrete union alternatives that do not belong to the generic.
        excluded: Vec<MonoTypeId>,
    },
}

/// One argument to a table-field call after solver lowering.
#[derive(Debug, Clone, PartialEq)]
enum SolverCallArgument {
    /// An independently inferred value.
    Value(InferenceVarId),
    /// A field of the same concrete table as the callee.
    Field(SmolStr),
}

/// Constraint plus a stable identity used for one-time dynamic activation.
#[derive(Debug, Clone)]
struct ConstraintRecord {
    /// Monotonic identifier within the solver.
    id: usize,
    /// Relation applied when the primary variable is processed.
    constraint: SolverConstraint,
}

/// One indexed callsite used for closure and builtin activation.
#[derive(Debug, Clone)]
struct CallSite {
    /// Variable holding the callable value.
    callee: InferenceVarId,
    /// Fixed argument variables.
    args: Vec<InferenceVarId>,
    /// Fixed return destinations.
    returns: Vec<InferenceVarId>,
}

/// One unresolved refinement retained until ordinary propagation reaches quiescence.
#[derive(Debug, Clone, Copy)]
struct DeferredRefinement {
    /// Refined occurrence receiving the conservative fallback.
    target: InferenceVarId,
    /// Definition whose producer evidence remained absent.
    source: InferenceVarId,
    /// Branch restriction used to derive the fallback type.
    truthiness: Truthiness,
}
/// One operator overload resolved only after concrete identity propagation settles.
#[derive(Debug, Clone, Copy)]
enum DeferredOperator {
    /// Defaults an otherwise unconstrained arithmetic operation to numbers.
    Arithmetic {
        /// Left operand.
        lhs: InferenceVarId,
        /// Right operand.
        rhs: InferenceVarId,
        /// Produced result.
        result: InferenceVarId,
    },
    /// Narrows a comparison from the concrete primitive used by either side.
    Comparison {
        /// Left operand.
        lhs: InferenceVarId,
        /// Right operand.
        rhs: InferenceVarId,
    },
    /// Defaults an otherwise unconstrained negation to numeric negation.
    UnaryMinus {
        /// Negated operand.
        operand: InferenceVarId,
        /// Produced result.
        result: InferenceVarId,
    },
}

/// Deduplicating FIFO work queue for inference variables.
#[derive(Debug, Default)]
struct WorkQueue {
    /// Variables waiting to be processed.
    pending: VecDeque<InferenceVarId>,
    /// Membership set mirroring `pending`.
    members: HashSet<InferenceVarId>,
}

impl WorkQueue {
    /// Enqueues `variable` unless it is already pending.
    fn push(&mut self, variable: InferenceVarId) {
        if self.members.insert(variable) {
            self.pending.push_back(variable);
        }
    }

    /// Pops the next variable in FIFO order.
    fn pop(&mut self) -> Option<InferenceVarId> {
        let variable = self.pending.pop_front()?;
        self.members.remove(&variable);
        Some(variable)
    }
}

/// Arena-backed bounded constraint solver.
struct TypeSolver<'a> {
    /// Canonical monotypes for this inference session.
    types: TypeArena,
    /// Inference-variable storage.
    variables: Arena<InferenceVariable>,
    /// Durable HIL slots mapped to inference variables.
    variables_by_slot: HashMap<TypeSlot, InferenceVarId>,
    /// Constraints grouped by primary variable.
    constraints: HashMap<InferenceVarId, Vec<ConstraintRecord>>,
    /// Reverse dependencies used to reschedule affected variables.
    dependencies: HashMap<InferenceVarId, HashSet<InferenceVarId>>,
    /// Pending primary variables.
    queue: WorkQueue,
    /// Mutable table-object storage.
    tables: Arena<TableObject>,
    /// Collected table keys mapped to table-object identities.
    tables_by_key: HashMap<TableKey, TableObjectId>,
    /// Variables currently carrying each table identity.
    table_users: HashMap<TableObjectId, HashSet<InferenceVarId>>,
    /// Lifted functions indexed by proto ID.
    functions: &'a [LiftedFunction],
    /// Shared builtin scheme environment.
    builtins: &'a BuiltinEnvironment,
    /// Fixed return arity for every proto.
    return_counts: HashMap<ProtoId, usize>,
    /// Same-table callback relations recovered for generic source signatures.
    generic_field_calls: HashMap<ProtoId, Vec<GenericFieldCall>>,
    /// Direct formal-to-return relations recovered for generic source signatures.
    generic_value_relations: HashMap<ProtoId, Vec<GenericValueRelation>>,
    /// Formal positions omitted by at least one concrete closure callsite.
    omitted_parameters: HashSet<(ProtoId, usize)>,
    /// Correlated call destinations grouped by closure formal position.
    correlated_call_results: HashMap<(ProtoId, usize), HashSet<InferenceVarId>>,
    /// Callsites stored by dense call ID.
    callsites: Vec<CallSite>,
    /// Call IDs grouped by callee variable.
    callsites_by_callee: HashMap<InferenceVarId, Vec<usize>>,
    /// Closure targets already connected to a callsite.
    activated_closures: HashSet<(usize, ProtoId)>,
    /// Builtin schemes already instantiated at a callsite.
    activated_builtins: HashSet<(usize, BuiltinPath)>,
    /// Table operations already connected to a concrete allocation.
    activated_table_constraints: HashSet<(usize, TableObjectId)>,
    /// Index-dispatch handlers already connected for each table read.
    activated_index_dispatches: HashSet<(usize, TableObjectId)>,
    /// Named fields already connected to each dynamic table read.
    activated_dynamic_fields: HashSet<(usize, TableObjectId, SmolStr)>,
    /// Refinements waiting for producer-free fallback after normal quiescence.
    deferred_refinements: HashMap<usize, DeferredRefinement>,
    /// Refinement records whose producer-free fallback has run once.
    activated_refinement_fallbacks: HashSet<usize>,
    /// Operators waiting for primitive fallback after identity propagation.
    deferred_operators: HashMap<usize, DeferredOperator>,
    /// Operator records whose primitive fallback decision has run once.
    activated_operator_fallbacks: HashSet<usize>,
    /// Next stable constraint identity.
    next_constraint_id: usize,
}

impl<'a> TypeSolver<'a> {
    /// Builds solver arenas and lowers collected source types into canonical IDs.
    fn new(
        program: CollectedProgram,
        functions: &'a [LiftedFunction],
        builtins: &'a BuiltinEnvironment,
        seeds: HashMap<TypeSlot, Vec<Type>>,
    ) -> Self {
        let mut solver = Self {
            types: TypeArena::new(),
            variables: Arena::new(),
            variables_by_slot: HashMap::new(),
            constraints: HashMap::new(),
            dependencies: HashMap::new(),
            queue: WorkQueue::default(),
            tables: Arena::new(),
            tables_by_key: HashMap::new(),
            table_users: HashMap::new(),
            functions,
            builtins,
            return_counts: program.return_counts,
            generic_field_calls: program.generic_field_calls,
            generic_value_relations: program.generic_value_relations,
            omitted_parameters: HashSet::new(),
            correlated_call_results: HashMap::new(),
            callsites: Vec::new(),
            callsites_by_callee: HashMap::new(),
            activated_closures: HashSet::new(),
            activated_builtins: HashSet::new(),
            activated_table_constraints: HashSet::new(),
            activated_index_dispatches: HashSet::new(),
            activated_dynamic_fields: HashSet::new(),
            deferred_refinements: HashMap::new(),
            activated_refinement_fallbacks: HashSet::new(),
            deferred_operators: HashMap::new(),
            activated_operator_fallbacks: HashSet::new(),
            next_constraint_id: 0,
        };

        for slot in program.constraints.keys().copied() {
            solver.variable_for_slot(slot);
        }
        for (slot, constraints) in program.constraints {
            let variable = solver.variable_for_slot(slot);
            for constraint in constraints {
                solver.add_collected_constraint(variable, constraint);
            }
        }
        for (slot, types) in seeds {
            let variable = solver.variable_for_slot(slot);
            for ty in types {
                if let Some(ty) = solver.types.lower_surface(&ty) {
                    solver.add_constraint(variable, SolverConstraint::Observe(ty));
                    solver.add_constraint(variable, SolverConstraint::Require(ty));
                }
            }
        }
        solver
    }

    /// Allocates an unconstrained inference variable.
    fn fresh_variable(&mut self) -> InferenceVarId {
        let primitives = self.types.primitives();
        let variable = self.variables.alloc(InferenceVariable {
            lower: primitives.never,
            upper: primitives.unknown,
            closures: HashSet::new(),
            tables: HashSet::new(),
            builtins: HashSet::new(),
        });
        self.constraints.entry(variable).or_default();
        self.queue.push(variable);
        variable
    }

    /// Returns the inference variable corresponding to a durable HIL slot.
    fn variable_for_slot(&mut self, slot: TypeSlot) -> InferenceVarId {
        if let Some(variable) = self.variables_by_slot.get(&slot) {
            return *variable;
        }
        let variable = self.fresh_variable();
        self.variables_by_slot.insert(slot, variable);
        variable
    }

    /// Lowers and installs one collected constraint.
    fn add_collected_constraint(
        &mut self,
        variable: InferenceVarId,
        constraint: CollectedConstraint,
    ) {
        match constraint {
            CollectedConstraint::Observe(ty) => {
                if let Some(ty) = self.types.lower_surface(&ty) {
                    self.add_constraint(variable, SolverConstraint::Observe(ty));
                }
            }
            CollectedConstraint::FlowFrom(source) => {
                let source = self.variable_for_slot(source);
                self.add_constraint(variable, SolverConstraint::FlowFrom(source));
            }
            CollectedConstraint::Equal(other) => {
                let other = self.variable_for_slot(other);
                self.add_constraint(variable, SolverConstraint::Equal(other));
            }
            CollectedConstraint::RefinedFrom { source, truthiness } => {
                let source = self.variable_for_slot(source);
                self.add_constraint(
                    variable,
                    SolverConstraint::RefinedFrom { source, truthiness },
                );
            }
            CollectedConstraint::NewTable(key) => {
                let table = self.table_for_key(key);
                self.add_constraint(variable, SolverConstraint::NewTable(table));
            }
            CollectedConstraint::SetIndex { index, value } => {
                let index = self.variable_for_slot(index);
                let value = self.variable_for_slot(value);
                self.add_constraint(variable, SolverConstraint::SetIndex { index, value });
            }
            CollectedConstraint::GetIndex { index, value } => {
                let index = self.variable_for_slot(index);
                let value = self.variable_for_slot(value);
                self.add_constraint(variable, SolverConstraint::GetIndex { index, value });
            }
            CollectedConstraint::SetField {
                field,
                value,
                definite,
            } => {
                let value = self.variable_for_slot(value);
                self.add_constraint(
                    variable,
                    SolverConstraint::SetField {
                        field,
                        value,
                        definite,
                    },
                );
            }
            CollectedConstraint::GetField { field, value } => {
                let value = self.variable_for_slot(value);
                self.add_constraint(variable, SolverConstraint::GetField { field, value });
            }
            CollectedConstraint::Binary { op, rhs, result } => {
                let rhs = self.variable_for_slot(rhs);
                let result = self.variable_for_slot(result);
                self.add_constraint(variable, SolverConstraint::Binary { op, rhs, result });
            }
            CollectedConstraint::Unary { op, result } => {
                let result = self.variable_for_slot(result);
                self.add_constraint(variable, SolverConstraint::Unary { op, result });
            }
            CollectedConstraint::Call { args, returns } => {
                let args = args
                    .into_iter()
                    .map(|slot| self.variable_for_slot(slot))
                    .collect();
                let returns = returns
                    .into_iter()
                    .map(|slot| self.variable_for_slot(slot))
                    .collect();
                self.add_constraint(variable, SolverConstraint::Call { args, returns });
            }
            CollectedConstraint::FieldCall {
                callee,
                args,
                returns,
            } => {
                let args = args
                    .into_iter()
                    .map(|argument| match argument {
                        CollectedCallArgument::Value(slot) => {
                            SolverCallArgument::Value(self.variable_for_slot(slot))
                        }
                        CollectedCallArgument::Field(field) => SolverCallArgument::Field(field),
                    })
                    .collect();
                let returns = returns
                    .into_iter()
                    .map(|slot| self.variable_for_slot(slot))
                    .collect();
                self.add_constraint(
                    variable,
                    SolverConstraint::FieldCall {
                        callee,
                        args,
                        returns,
                    },
                );
            }
            CollectedConstraint::Closure(proto) => {
                self.add_constraint(variable, SolverConstraint::Closure(proto));
            }
            CollectedConstraint::Builtin(path) => {
                self.add_constraint(variable, SolverConstraint::Builtin(path));
            }
        }
    }

    /// Allocates or returns the mutable object associated with `key`.
    fn table_for_key(&mut self, key: TableKey) -> TableObjectId {
        if let Some(table) = self.tables_by_key.get(&key) {
            return *table;
        }
        let keys = self.fresh_variable();
        let values = self.fresh_variable();
        let table = self.tables.alloc(TableObject {
            keys,
            values,
            fields: HashMap::new(),
            metatables: HashSet::new(),
        });
        self.tables_by_key.insert(key, table);
        table
    }

    /// Adds a native constraint, its dependencies, and any callsite index.
    fn add_constraint(&mut self, variable: InferenceVarId, constraint: SolverConstraint) {
        let constraints = self.constraints.entry(variable).or_default();
        if constraints
            .iter()
            .any(|record| record.constraint == constraint)
        {
            return;
        }

        let record_id = self.next_constraint_id;
        self.next_constraint_id = self
            .next_constraint_id
            .checked_add(1)
            .expect("inference constraint IDs exhausted usize");
        self.register_dependencies(variable, &constraint);

        if let SolverConstraint::Call { args, returns } = &constraint {
            let call_id = self.callsites.len();
            self.callsites.push(CallSite {
                callee: variable,
                args: args.clone(),
                returns: returns.clone(),
            });
            self.callsites_by_callee
                .entry(variable)
                .or_default()
                .push(call_id);
        }

        self.constraints
            .entry(variable)
            .or_default()
            .push(ConstraintRecord {
                id: record_id,
                constraint,
            });
        self.queue.push(variable);
    }

    /// Registers reverse dependencies for one constraint.
    fn register_dependencies(&mut self, primary: InferenceVarId, constraint: &SolverConstraint) {
        let mut depend_on = |source: InferenceVarId| {
            self.dependencies.entry(source).or_default().insert(primary);
        };
        match constraint {
            SolverConstraint::Observe(_)
            | SolverConstraint::Require(_)
            | SolverConstraint::NewTable(_)
            | SolverConstraint::Closure(_)
            | SolverConstraint::Builtin(_) => {}
            SolverConstraint::FlowFrom(source)
            | SolverConstraint::Equal(source)
            | SolverConstraint::RefinedFrom { source, .. }
            | SolverConstraint::GenericFrom { source, .. }
            | SolverConstraint::NonNilFrom { source } => depend_on(*source),
            SolverConstraint::SetIndex { index, value }
            | SolverConstraint::GetIndex { index, value } => {
                depend_on(*index);
                depend_on(*value);
            }
            SolverConstraint::SetField { value, .. }
            | SolverConstraint::GetField { value, .. }
            | SolverConstraint::Unary { result: value, .. } => depend_on(*value),
            SolverConstraint::Binary { rhs, result, .. } => {
                depend_on(*rhs);
                depend_on(*result);
            }
            SolverConstraint::Call { args, returns } => {
                for variable in args.iter().chain(returns) {
                    depend_on(*variable);
                }
            }
            SolverConstraint::FieldCall { args, returns, .. } => {
                for argument in args {
                    if let SolverCallArgument::Value(variable) = argument {
                        depend_on(*variable);
                    }
                }
                for variable in returns {
                    depend_on(*variable);
                }
            }
            SolverConstraint::SetMetatable { metatable, result } => {
                depend_on(*metatable);
                if let Some(result) = result {
                    depend_on(*result);
                }
            }
        }
    }

    /// Runs every constraint until lower bounds, upper bounds, and identities stabilize.
    fn solve(&mut self) {
        loop {
            self.drain_queue();
            if self.activate_deferred_operators() {
                continue;
            }
            if self.activate_deferred_refinements() {
                continue;
            }
            break;
        }
    }

    /// Drains the ordinary event queue without activating producer-free fallbacks.
    fn drain_queue(&mut self) {
        while let Some(variable) = self.queue.pop() {
            let constraints = self.constraints.get(&variable).cloned().unwrap_or_default();
            for record in constraints {
                self.apply(variable, record);
            }
            self.activate_calls(variable);
        }
    }

    /// Activates primitive operator defaults after table and closure identities settle.
    fn activate_deferred_operators(&mut self) -> bool {
        let mut deferred: Vec<_> = std::mem::take(&mut self.deferred_operators)
            .into_iter()
            .collect();
        deferred.sort_by_key(|(constraint_id, _)| *constraint_id);
        let mut activated = false;
        for (constraint_id, operator) in deferred {
            if !self.activated_operator_fallbacks.insert(constraint_id) {
                continue;
            }
            let primitives = self.types.primitives();
            match operator {
                DeferredOperator::Arithmetic { lhs, rhs, result }
                    if self.can_default_to(lhs, primitives.number)
                        && self.can_default_to(rhs, primitives.number) =>
                {
                    self.require(lhs, primitives.number);
                    self.require(rhs, primitives.number);
                    self.observe(result, primitives.number);
                    activated = true;
                }
                DeferredOperator::Comparison { lhs, rhs } => {
                    let narrowed = if self.produced_is_subtype(lhs, primitives.number)
                        && self.can_default_to(rhs, primitives.number)
                        || self.produced_is_subtype(rhs, primitives.number)
                            && self.can_default_to(lhs, primitives.number)
                    {
                        Some(primitives.number)
                    } else if self.produced_is_subtype(lhs, primitives.string)
                        && self.can_default_to(rhs, primitives.string)
                        || self.produced_is_subtype(rhs, primitives.string)
                            && self.can_default_to(lhs, primitives.string)
                    {
                        Some(primitives.string)
                    } else {
                        None
                    };
                    if let Some(ty) = narrowed {
                        self.require(lhs, ty);
                        self.require(rhs, ty);
                        activated = true;
                    }
                }
                DeferredOperator::UnaryMinus { operand, result }
                    if self.can_default_to(operand, primitives.number) =>
                {
                    self.require(operand, primitives.number);
                    self.observe(result, primitives.number);
                    activated = true;
                }
                _ => {}
            }
        }
        activated
    }

    /// Returns whether unresolved evidence can conservatively default to `primitive`.
    fn can_default_to(&self, variable: InferenceVarId, primitive: MonoTypeId) -> bool {
        let facts = &self.variables[variable];
        if !facts.tables.is_empty() || !facts.closures.is_empty() || !facts.builtins.is_empty() {
            return false;
        }
        self.lower_defaults_to(facts.lower, primitive)
    }

    /// Returns whether `lower` differs from `primitive` only by nil or dynamic evidence.
    fn lower_defaults_to(&self, lower: MonoTypeId, primitive: MonoTypeId) -> bool {
        match self.types.get(lower) {
            MonoType::Never | MonoType::Nil | MonoType::Unknown | MonoType::Any => true,
            MonoType::Union(members) => members
                .iter()
                .all(|member| self.lower_defaults_to(*member, primitive)),
            _ => self.types.is_subtype(lower, primitive),
        }
    }

    /// Returns whether a variable produces only values inside `primitive`.
    fn produced_is_subtype(&self, variable: InferenceVarId, primitive: MonoTypeId) -> bool {
        self.produced_type(variable)
            .is_some_and(|produced| self.types.is_subtype(produced, primitive))
    }

    /// Records one operator fallback unless its final decision already ran.
    fn defer_operator(&mut self, constraint_id: usize, operator: DeferredOperator) {
        if !self.activated_operator_fallbacks.contains(&constraint_id) {
            self.deferred_operators
                .entry(constraint_id)
                .or_insert(operator);
        }
    }

    /// Activates every still-unresolved refinement fallback once in constraint order.
    fn activate_deferred_refinements(&mut self) -> bool {
        let mut deferred: Vec<_> = std::mem::take(&mut self.deferred_refinements)
            .into_iter()
            .collect();
        deferred.sort_by_key(|(constraint_id, _)| *constraint_id);
        let mut activated = false;
        for (constraint_id, refinement) in deferred {
            if self.evidence_type(refinement.source).is_some()
                || !self.activated_refinement_fallbacks.insert(constraint_id)
            {
                continue;
            }
            let unknown = self.types.primitives().unknown;
            let fallback = match refinement.truthiness {
                Truthiness::Truthy => unknown,
                Truthiness::Falsy => self.types.falsy_part(unknown),
            };
            self.observe(refinement.target, fallback);
            activated = true;
        }
        activated
    }

    /// Applies one native constraint to its primary variable.
    fn apply(&mut self, variable: InferenceVarId, record: ConstraintRecord) {
        match record.constraint {
            SolverConstraint::Observe(ty) => {
                self.observe(variable, ty);
            }
            SolverConstraint::Require(ty) => {
                self.require(variable, ty);
            }
            SolverConstraint::FlowFrom(source) => self.apply_flow(variable, source),
            SolverConstraint::Equal(other) => {
                self.apply_flow(variable, other);
                self.apply_flow(other, variable);
            }
            SolverConstraint::RefinedFrom { source, truthiness } => {
                self.apply_refinement(record.id, variable, source, truthiness);
            }
            SolverConstraint::NewTable(table) => {
                self.include_table(variable, table);
            }
            SolverConstraint::SetIndex { index, value } => {
                self.apply_set_index(record.id, variable, index, value);
            }
            SolverConstraint::GetIndex { index, value } => {
                self.apply_get_index(record.id, variable, index, value);
            }
            SolverConstraint::SetField {
                field,
                value,
                definite,
            } => self.apply_set_field(record.id, variable, field, value, definite),
            SolverConstraint::GetField { field, value } => {
                self.apply_get_field(record.id, variable, field, value);
            }
            SolverConstraint::Binary { op, rhs, result } => {
                self.apply_binary(record.id, variable, op, rhs, result);
            }
            SolverConstraint::Unary { op, result } => {
                self.apply_unary(record.id, variable, op, result);
            }
            SolverConstraint::Call { args, returns } => {
                self.infer_callable_requirement(variable, &args, &returns);
                self.apply_callable_monotype(variable, &args, &returns);
                self.connect_call_metamethod(variable, &args, &returns);
                self.activate_calls(variable);
            }
            SolverConstraint::FieldCall {
                callee,
                args,
                returns,
            } => self.apply_field_call(record.id, variable, callee, &args, &returns),
            SolverConstraint::Closure(proto) => {
                self.include_closure(variable, proto);
            }
            SolverConstraint::Builtin(path) => {
                self.include_builtin(variable, path);
            }
            SolverConstraint::SetMetatable { metatable, result } => {
                self.apply_set_metatable(variable, metatable, result);
            }
            SolverConstraint::NonNilFrom { source } => {
                if let Some(source_ty) = self.evidence_type(source) {
                    let stored_ty = self
                        .types
                        .exclude(source_ty, &[self.types.primitives().nil]);
                    self.observe(variable, stored_ty);
                }
            }
            SolverConstraint::GenericFrom { source, excluded } => {
                if let Some(source_ty) = self.evidence_type(source) {
                    let generic_ty = self.types.exclude(source_ty, &excluded);
                    self.observe(variable, generic_ty);
                }
            }
        }
    }

    /// Adds a producer observation to a variable's lower bound.
    fn observe(&mut self, variable: InferenceVarId, ty: MonoTypeId) -> bool {
        let old = self.variables[variable].lower;
        let next = self.types.union(old, ty);
        if old == next {
            return false;
        }
        self.variables[variable].lower = next;
        self.variable_changed(variable);
        true
    }

    /// Adds a consumer requirement to a variable's upper bound.
    fn require(&mut self, variable: InferenceVarId, ty: MonoTypeId) -> bool {
        let old = self.variables[variable].upper;
        let next = self.types.intersection(old, ty);
        if old == next {
            return false;
        }
        self.variables[variable].upper = next;
        self.variable_changed(variable);
        true
    }

    /// Re-enqueues a changed variable and every primary relation that reads it.
    fn variable_changed(&mut self, variable: InferenceVarId) {
        self.queue.push(variable);
        let dependents = self
            .dependencies
            .get(&variable)
            .cloned()
            .unwrap_or_default();
        for dependent in dependents {
            self.queue.push(dependent);
        }
    }

    /// Propagates a subtype edge and its non-type identity domains.
    fn apply_flow(&mut self, target: InferenceVarId, source: InferenceVarId) {
        let source_facts = self.variables[source].clone();
        self.observe(target, source_facts.lower);
        let target_upper = self.variables[target].upper;
        self.require(source, target_upper);
        for closure in source_facts.closures {
            self.include_closure(target, closure);
        }
        for table in source_facts.tables {
            self.include_table(target, table);
        }
        for builtin in source_facts.builtins {
            self.include_builtin(target, builtin);
        }
    }

    /// Applies one truthiness filter without narrowing the source definition.
    fn apply_refinement(
        &mut self,
        constraint_id: usize,
        target: InferenceVarId,
        source: InferenceVarId,
        truthiness: Truthiness,
    ) {
        if let Some(source_ty) = self.evidence_type(source) {
            self.deferred_refinements.remove(&constraint_id);
            let refined = match truthiness {
                Truthiness::Truthy => self.types.truthy_part(source_ty),
                Truthiness::Falsy => self.types.falsy_part(source_ty),
            };
            self.observe(target, refined);
        } else if !self.activated_refinement_fallbacks.contains(&constraint_id) {
            self.deferred_refinements.insert(
                constraint_id,
                DeferredRefinement {
                    target,
                    source,
                    truthiness,
                },
            );
        }

        if truthiness == Truthiness::Truthy {
            let source_facts = self.variables[source].clone();
            for closure in source_facts.closures {
                self.include_closure(target, closure);
            }
            for table in source_facts.tables {
                self.include_table(target, table);
            }
            for builtin in source_facts.builtins {
                self.include_builtin(target, builtin);
            }
        }
    }

    /// Adds a closure identity and the broad callable producer fact.
    fn include_closure(&mut self, variable: InferenceVarId, proto: ProtoId) -> bool {
        if !self.variables[variable].closures.insert(proto) {
            return false;
        }
        self.variable_changed(variable);
        true
    }

    /// Adds a table identity and the broad table producer fact.
    fn include_table(&mut self, variable: InferenceVarId, table: TableObjectId) -> bool {
        if !self.variables[variable].tables.insert(table) {
            return false;
        }
        self.table_users.entry(table).or_default().insert(variable);
        self.variable_changed(variable);
        true
    }

    /// Adds a builtin scheme identity and any monomorphic producer type.
    fn include_builtin(&mut self, variable: InferenceVarId, path: BuiltinPath) -> bool {
        if !self.variables[variable].builtins.insert(path.clone()) {
            return false;
        }
        let scheme = self.builtins.get_path(&path).cloned();
        if let Some(scheme) = scheme
            && let Some(ty) = self.types.lower_surface(&scheme)
        {
            self.observe(variable, ty);
        }
        self.variable_changed(variable);
        true
    }

    /// Returns a consistent produced type, excluding consumer-only inference.
    fn produced_type(&self, variable: InferenceVarId) -> Option<MonoTypeId> {
        let facts = &self.variables[variable];
        if facts.lower == self.types.primitives().never
            || !self.types.is_subtype(facts.lower, facts.upper)
        {
            return None;
        }
        Some(facts.lower)
    }

    /// Returns the best consistent candidate from lower and upper bounds.
    fn candidate_type(&self, variable: InferenceVarId) -> Option<MonoTypeId> {
        let facts = &self.variables[variable];
        if facts.lower != self.types.primitives().never {
            return self
                .types
                .is_subtype(facts.lower, facts.upper)
                .then_some(facts.lower);
        }
        self.types
            .is_emittable_upper_bound(facts.upper)
            .then_some(facts.upper)
    }

    /// Returns runtime evidence, adding broad markers for identity-only domains.
    fn evidence_type(&mut self, variable: InferenceVarId) -> Option<MonoTypeId> {
        let facts = self.variables[variable].clone();
        let primitives = self.types.primitives();
        let mut evidence = facts.lower;
        if !facts.tables.is_empty() {
            evidence = self.types.union(evidence, primitives.table);
        }
        if !facts.closures.is_empty() || !facts.builtins.is_empty() {
            evidence = self.types.union(evidence, primitives.function);
        }
        (evidence != primitives.never).then_some(evidence)
    }
}

impl TypeSolver<'_> {
    /// Returns or creates the variable for one named table field.
    fn table_field_variable(
        &mut self,
        table: TableObjectId,
        field: SmolStr,
        definite: bool,
    ) -> InferenceVarId {
        if let Some(existing) = self.tables[table].fields.get_mut(&field) {
            existing.definite |= definite;
            return existing.value;
        }
        let value = self.fresh_variable();
        self.tables[table]
            .fields
            .insert(field, TableField { value, definite });
        value
    }

    /// Re-enqueues every variable carrying a changed table allocation.
    fn table_changed(&mut self, table: TableObjectId) {
        let users = self.table_users.get(&table).cloned().unwrap_or_default();
        for user in users {
            self.variable_changed(user);
        }
    }

    /// Connects one indexed write to every table identity carried by `object`.
    fn apply_set_index(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        index: InferenceVarId,
        value: InferenceVarId,
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if !self
                .activated_table_constraints
                .insert((constraint_id, table))
            {
                continue;
            }
            let key_target = self.tables[table].keys;
            let value_target = self.tables[table].values;
            self.add_constraint(key_target, SolverConstraint::FlowFrom(index));
            self.add_constraint(value_target, SolverConstraint::NonNilFrom { source: value });
            self.table_changed(table);
        }
    }

    /// Connects one indexed read without feeding the read result back into the table.
    fn apply_get_index(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        index: InferenceVarId,
        value: InferenceVarId,
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if self
                .activated_table_constraints
                .insert((constraint_id, table))
            {
                let table_values = self.tables[table].values;
                self.add_constraint(value, SolverConstraint::FlowFrom(table_values));
                self.add_constraint(
                    value,
                    SolverConstraint::Observe(self.types.primitives().nil),
                );
            }

            // Dynamic reads can select any named field. This scan intentionally
            // remains outside direct activation so later field additions reconnect.
            let mut fields: Vec<_> = self.tables[table]
                .fields
                .iter()
                .map(|(name, field)| (name.clone(), field.value))
                .collect();
            fields.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
            for (field, field_value) in fields {
                if self
                    .activated_dynamic_fields
                    .insert((constraint_id, table, field))
                {
                    self.add_constraint(value, SolverConstraint::FlowFrom(field_value));
                }
            }
            self.connect_dynamic_index_dispatch(constraint_id, table, object, index, value);
        }

        if let Some(object_ty) = self.produced_type(object)
            && let Some(indexed) = self.structural_index_value(object_ty)
        {
            self.observe(value, indexed);
        }
    }

    /// Connects one named write to every table identity carried by `object`.
    fn apply_set_field(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        field: SmolStr,
        value: InferenceVarId,
        definite: bool,
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if !self
                .activated_table_constraints
                .insert((constraint_id, table))
            {
                continue;
            }
            let field_value = self.table_field_variable(table, field.clone(), definite);
            self.add_constraint(field_value, SolverConstraint::FlowFrom(value));
            self.table_changed(table);
        }
    }

    /// Connects one named read to concrete tables and sealed structural types.
    fn apply_get_field(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        field: SmolStr,
        value: InferenceVarId,
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if self
                .activated_table_constraints
                .insert((constraint_id, table))
            {
                let field_value = self.table_field_variable(table, field.clone(), false);
                self.add_constraint(value, SolverConstraint::FlowFrom(field_value));
                self.add_constraint(
                    value,
                    SolverConstraint::Observe(self.types.primitives().nil),
                );
            }
            // Handler discovery must not share the direct-read gate: metatable
            // links and `__index` fields can both appear after this read first ran.
            self.connect_named_index_dispatch(constraint_id, table, object, field.clone(), value);
        }

        if let Some(object_ty) = self.produced_type(object)
            && let Some(field_ty) = self.structural_field_type(object_ty, &field)
        {
            self.observe(value, field_ty);
        }
    }

    /// Instantiates a field call once per concrete receiver table.
    ///
    /// Keeping field arguments attached to the same table prevents a union of
    /// table shapes from turning `object.f(object.data)` into the Cartesian
    /// product of every observed `f` and every observed `data` value.
    fn apply_field_call(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        callee_field: SmolStr,
        arguments: &[SolverCallArgument],
        returns: &[InferenceVarId],
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if !self
                .activated_table_constraints
                .insert((constraint_id, table))
            {
                continue;
            }

            let callee = self.table_field_variable(table, callee_field.clone(), false);
            let args = arguments
                .iter()
                .map(|argument| match argument {
                    SolverCallArgument::Value(variable) => *variable,
                    SolverCallArgument::Field(field) => {
                        self.table_field_variable(table, field.clone(), false)
                    }
                })
                .collect();
            self.add_constraint(
                callee,
                SolverConstraint::Call {
                    args,
                    returns: returns.to_vec(),
                },
            );
        }
    }

    /// Connects a named read to every newly discovered `__index` handler.
    fn connect_named_index_dispatch(
        &mut self,
        constraint_id: usize,
        table: TableObjectId,
        object: InferenceVarId,
        field: SmolStr,
        value: InferenceVarId,
    ) {
        let metatables: Vec<_> = self.tables[table].metatables.iter().copied().collect();
        for metatable in metatables {
            if !self
                .activated_index_dispatches
                .insert((constraint_id, metatable))
            {
                continue;
            }
            let handler = self.table_field_variable(metatable, "__index".into(), false);
            let key = self.fresh_variable();
            let key_ty = self.types.intern(MonoType::StringLiteral(field.clone()));
            self.add_constraint(key, SolverConstraint::Observe(key_ty));
            self.add_constraint(
                handler,
                SolverConstraint::Call {
                    args: vec![object, key],
                    returns: vec![value],
                },
            );
            self.add_constraint(
                handler,
                SolverConstraint::GetField {
                    field: field.clone(),
                    value,
                },
            );
        }
    }

    /// Connects a dynamic read to callable and table-valued `__index` handlers.
    fn connect_dynamic_index_dispatch(
        &mut self,
        constraint_id: usize,
        table: TableObjectId,
        object: InferenceVarId,
        key: InferenceVarId,
        value: InferenceVarId,
    ) {
        let metatables: Vec<_> = self.tables[table].metatables.iter().copied().collect();
        for metatable in metatables {
            if !self
                .activated_index_dispatches
                .insert((constraint_id, metatable))
            {
                continue;
            }
            let handler = self.table_field_variable(metatable, "__index".into(), false);
            self.add_constraint(
                handler,
                SolverConstraint::Call {
                    args: vec![object, key],
                    returns: vec![value],
                },
            );
            self.add_constraint(handler, SolverConstraint::GetIndex { index: key, value });
        }
    }

    /// Extracts an indexer value from a sealed structural type.
    fn structural_index_value(&mut self, ty: MonoTypeId) -> Option<MonoTypeId> {
        match self.types.get(ty).clone() {
            MonoType::TableShape {
                indexer: Some((_, value)),
                ..
            } => Some(value),
            MonoType::Union(members) | MonoType::Intersection(members) => {
                let values: Vec<_> = members
                    .into_iter()
                    .filter_map(|member| self.structural_index_value(member))
                    .collect();
                (!values.is_empty()).then(|| self.types.union_all(values))
            }
            MonoType::WithMetatable { base, .. } => self.structural_index_value(base),
            _ => None,
        }
    }

    /// Extracts and unions all matching named fields from a structural type.
    fn structural_field_type(&mut self, ty: MonoTypeId, field: &SmolStr) -> Option<MonoTypeId> {
        match self.types.get(ty).clone() {
            MonoType::TableShape { fields, .. } => fields
                .into_iter()
                .find(|(name, _)| name == field)
                .map(|(_, ty)| ty),
            MonoType::Union(members) | MonoType::Intersection(members) => {
                let values: Vec<_> = members
                    .into_iter()
                    .filter_map(|member| self.structural_field_type(member, field))
                    .collect();
                (!values.is_empty()).then(|| self.types.union_all(values))
            }
            MonoType::WithMetatable { base, .. } => self.structural_field_type(base, field),
            _ => None,
        }
    }

    /// Links every base table allocation to every metatable allocation.
    fn apply_set_metatable(
        &mut self,
        base: InferenceVarId,
        metatable: InferenceVarId,
        result: Option<InferenceVarId>,
    ) {
        if let Some(result) = result {
            self.add_constraint(result, SolverConstraint::Equal(base));
        }
        let bases: Vec<_> = self.variables[base].tables.iter().copied().collect();
        let metatables: Vec<_> = self.variables[metatable].tables.iter().copied().collect();
        for base_table in bases {
            for metatable_table in &metatables {
                // Pair-level insertion is the activation gate. A constraint-level
                // gate loses later base identities that share an existing metatable.
                if self.tables[base_table].metatables.insert(*metatable_table) {
                    self.table_changed(base_table);
                }
            }
        }
    }

    /// Applies conservative builtin overloads and then known metamethods.
    fn apply_binary(
        &mut self,
        constraint_id: usize,
        lhs: InferenceVarId,
        op: BinOp,
        rhs: InferenceVarId,
        result: InferenceVarId,
    ) {
        let primitives = self.types.primitives();
        match op {
            BinOp::Eq | BinOp::Ne => {
                self.observe(result, primitives.boolean);
            }
            BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => {
                self.observe(result, primitives.boolean);
                let accepted =
                    self.operator_domain(&[primitives.number, primitives.string, primitives.table]);
                self.require(lhs, accepted);
                self.require(rhs, accepted);
                self.defer_operator(constraint_id, DeferredOperator::Comparison { lhs, rhs });
            }
            BinOp::And => {
                if let Some(lhs_ty) = self.evidence_type(lhs) {
                    let falsy = self.types.falsy_part(lhs_ty);
                    self.observe(result, falsy);
                }
                if let Some(rhs_ty) = self.evidence_type(rhs) {
                    self.observe(result, rhs_ty);
                }
            }
            BinOp::Or => {
                if let Some(lhs_ty) = self.evidence_type(lhs) {
                    let truthy = self.types.truthy_part(lhs_ty);
                    self.observe(result, truthy);
                }
                if let Some(rhs_ty) = self.evidence_type(rhs) {
                    self.observe(result, rhs_ty);
                }
            }
            BinOp::Concat => {
                let accepted =
                    self.operator_domain(&[primitives.string, primitives.number, primitives.table]);
                self.require(lhs, accepted);
                self.require(rhs, accepted);
                if self.operands_are_concat_primitives(lhs, rhs) {
                    self.observe(result, primitives.string);
                }
                self.connect_binary_metamethod(lhs, rhs, result, Metamethod::Concat);
            }
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::IDiv
            | BinOp::Mod
            | BinOp::Pow => {
                let accepted =
                    self.operator_domain(&[primitives.number, primitives.vector, primitives.table]);
                self.require(lhs, accepted);
                self.require(rhs, accepted);
                if let Some(ty) = self.arithmetic_result(lhs, op, rhs) {
                    self.observe(result, ty);
                }
                self.defer_operator(
                    constraint_id,
                    DeferredOperator::Arithmetic { lhs, rhs, result },
                );
                if let Ok(method) = Metamethod::try_from(op) {
                    self.connect_binary_metamethod(lhs, rhs, result, method);
                }
            }
        }
    }

    /// Applies conservative builtin unary operations and known metamethods.
    fn apply_unary(
        &mut self,
        constraint_id: usize,
        operand: InferenceVarId,
        op: UnOp,
        result: InferenceVarId,
    ) {
        let primitives = self.types.primitives();
        match op {
            UnOp::Not => {
                self.observe(result, primitives.boolean);
            }
            UnOp::Minus => {
                let accepted =
                    self.operator_domain(&[primitives.number, primitives.vector, primitives.table]);
                self.require(operand, accepted);
                if let Some(operand_ty) = self.evidence_type(operand) {
                    if self.has_concrete_overlap(operand_ty, primitives.number) {
                        self.observe(result, primitives.number);
                    }
                    if self.has_concrete_overlap(operand_ty, primitives.vector) {
                        self.observe(result, primitives.vector);
                    }
                }
                self.defer_operator(
                    constraint_id,
                    DeferredOperator::UnaryMinus { operand, result },
                );
                self.connect_unary_metamethod(operand, result, Metamethod::Unm);
            }
            UnOp::Length => {
                let accepted = self.operator_domain(&[primitives.string, primitives.table]);
                self.require(operand, accepted);
                if let Some(operand_ty) = self.evidence_type(operand)
                    && self.has_concrete_overlap(operand_ty, primitives.string)
                {
                    self.observe(result, primitives.number);
                }
                self.connect_unary_metamethod(operand, result, Metamethod::Len);
            }
        }
    }

    /// Builds an operator domain including userdata metamethod receivers.
    fn operator_domain(&mut self, builtins: &[MonoTypeId]) -> MonoTypeId {
        let userdata = self.types.intern(MonoType::Userdata);
        let members: Vec<_> = builtins.iter().copied().chain([userdata]).collect();
        self.types.union_all(members)
    }

    /// Returns every builtin arithmetic result supported by current evidence.
    fn arithmetic_result(
        &mut self,
        lhs: InferenceVarId,
        op: BinOp,
        rhs: InferenceVarId,
    ) -> Option<MonoTypeId> {
        let lhs = self.evidence_type(lhs)?;
        let rhs = self.evidence_type(rhs)?;
        let primitives = self.types.primitives();
        let mut results = Vec::new();
        if self.has_concrete_overlap(lhs, primitives.number)
            && self.has_concrete_overlap(rhs, primitives.number)
        {
            results.push(primitives.number);
        }

        let vector_lhs = self.has_concrete_overlap(lhs, primitives.vector);
        let vector_rhs = self.has_concrete_overlap(rhs, primitives.vector);
        let number_rhs = self.has_concrete_overlap(rhs, primitives.number);
        let supported = match op {
            BinOp::Add | BinOp::Sub => vector_lhs && vector_rhs,
            BinOp::Mul | BinOp::Div | BinOp::IDiv => vector_lhs && (vector_rhs || number_rhs),
            BinOp::Mod | BinOp::Pow => false,
            _ => false,
        };
        if supported {
            results.push(primitives.vector);
        }
        (!results.is_empty()).then(|| self.types.union_all(results))
    }

    /// Returns whether both operands prove a primitive concatenation overload.
    fn operands_are_concat_primitives(&mut self, lhs: InferenceVarId, rhs: InferenceVarId) -> bool {
        let Some(lhs) = self.evidence_type(lhs) else {
            return false;
        };
        let Some(rhs) = self.evidence_type(rhs) else {
            return false;
        };
        let primitives = self.types.primitives();
        let lhs_accepted = self.has_concrete_overlap(lhs, primitives.string)
            || self.has_concrete_overlap(lhs, primitives.number);
        let rhs_accepted = self.has_concrete_overlap(rhs, primitives.string)
            || self.has_concrete_overlap(rhs, primitives.number);
        lhs_accepted && rhs_accepted
    }

    /// Returns whether `evidence` contains a concrete member of `accepted`.
    fn has_concrete_overlap(&mut self, evidence: MonoTypeId, accepted: MonoTypeId) -> bool {
        if matches!(self.types.get(evidence), MonoType::Unknown | MonoType::Any) {
            return false;
        }
        self.types.intersection(evidence, accepted) != self.types.primitives().never
    }

    /// Connects a binary operation to every known operand metatable method.
    fn connect_binary_metamethod(
        &mut self,
        lhs: InferenceVarId,
        rhs: InferenceVarId,
        result: InferenceVarId,
        method: Metamethod,
    ) {
        let mut tables: Vec<_> = self.variables[lhs].tables.iter().copied().collect();
        tables.extend(self.variables[rhs].tables.iter().copied());
        tables.sort_unstable();
        tables.dedup();
        for table in tables {
            let metatables: Vec<_> = self.tables[table].metatables.iter().copied().collect();
            for metatable in metatables {
                let method = self.table_field_variable(
                    metatable,
                    SmolStr::new_static(method.field()),
                    false,
                );
                self.add_constraint(
                    method,
                    SolverConstraint::Call {
                        args: vec![lhs, rhs],
                        returns: vec![result],
                    },
                );
            }
        }
    }

    /// Connects a unary operation to every known operand metatable method.
    fn connect_unary_metamethod(
        &mut self,
        operand: InferenceVarId,
        result: InferenceVarId,
        method: Metamethod,
    ) {
        let tables: Vec<_> = self.variables[operand].tables.iter().copied().collect();
        for table in tables {
            let metatables: Vec<_> = self.tables[table].metatables.iter().copied().collect();
            for metatable in metatables {
                let method = self.table_field_variable(
                    metatable,
                    SmolStr::new_static(method.field()),
                    false,
                );
                self.add_constraint(
                    method,
                    SolverConstraint::Call {
                        args: vec![operand],
                        returns: vec![result],
                    },
                );
            }
        }
    }

    /// Connects a table call to every statically known `__call` method.
    fn connect_call_metamethod(
        &mut self,
        callee: InferenceVarId,
        args: &[InferenceVarId],
        returns: &[InferenceVarId],
    ) {
        let tables: Vec<_> = self.variables[callee].tables.iter().copied().collect();
        for table in tables {
            let metatables: Vec<_> = self.tables[table].metatables.iter().copied().collect();
            for metatable in metatables {
                let method = self.table_field_variable(metatable, "__call".into(), false);
                let mut call_args = Vec::with_capacity(args.len() + 1);
                call_args.push(callee);
                call_args.extend_from_slice(args);
                self.add_constraint(
                    method,
                    SolverConstraint::Call {
                        args: call_args,
                        returns: returns.to_vec(),
                    },
                );
            }
        }
    }
}

impl TypeSolver<'_> {
    /// Resolves one inference variable into a canonical printable monotype.
    fn resolved_type(
        &mut self,
        variable: InferenceVarId,
        visiting: &mut HashSet<InferenceVarId>,
    ) -> Option<MonoTypeId> {
        if !visiting.insert(variable) {
            return Some(self.types.primitives().unknown);
        }

        let facts = self.variables[variable].clone();
        let primitives = self.types.primitives();
        let mut components = Vec::new();
        if facts.lower != primitives.never {
            components.push(facts.lower);
        }
        if !facts.tables.is_empty() {
            let table_types: Vec<_> = facts
                .tables
                .into_iter()
                .map(|table| self.materialize_table(table, visiting))
                .collect();
            components.extend(table_types);
        }
        if !facts.closures.is_empty() {
            let function_types: Vec<_> = facts
                .closures
                .into_iter()
                .map(|proto| self.materialize_function(proto, visiting))
                .collect();
            components.extend(function_types);
        }

        let resolved = if components.is_empty() {
            self.candidate_type(variable)?
        } else {
            let resolved = self.types.union_all(components);
            if !self.types.is_subtype(resolved, facts.upper) {
                visiting.remove(&variable);
                return None;
            }
            resolved
        };
        visiting.remove(&variable);
        (resolved != primitives.never).then_some(resolved)
    }

    /// Materializes one mutable table allocation as an immutable structural type.
    fn materialize_table(
        &mut self,
        table: TableObjectId,
        visiting: &mut HashSet<InferenceVarId>,
    ) -> MonoTypeId {
        let (keys, values, fields, metatables): (
            InferenceVarId,
            InferenceVarId,
            Vec<(SmolStr, TableField)>,
            Vec<TableObjectId>,
        ) = {
            let table = &self.tables[table];
            (
                table.keys,
                table.values,
                table
                    .fields
                    .iter()
                    .map(|(name, field)| (name.clone(), *field))
                    .collect(),
                table.metatables.iter().copied().collect(),
            )
        };

        let mut materialized_fields = Vec::new();
        for (name, field) in fields {
            let mut value = self
                .resolved_type(field.value, visiting)
                .unwrap_or(self.types.primitives().unknown);
            if !field.definite {
                value = self.types.union(value, self.types.primitives().nil);
            }
            materialized_fields.push((name, value));
        }
        materialized_fields.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

        let indexer = match (
            self.resolved_type(keys, visiting),
            self.resolved_type(values, visiting),
        ) {
            (Some(key), Some(value)) => {
                Some((key, self.types.union(value, self.types.primitives().nil)))
            }
            _ => None,
        };
        let base = self.types.intern(MonoType::TableShape {
            fields: materialized_fields,
            indexer,
        });

        let mut methods = Vec::new();
        for metatable in metatables {
            let fields: Vec<_> = self.tables[metatable]
                .fields
                .iter()
                .map(|(name, field)| (name.clone(), field.value))
                .collect();
            for (name, value) in fields {
                let Ok(method) = Metamethod::try_from(name.as_str()) else {
                    continue;
                };
                let Some(ty) = self.resolved_type(value, visiting) else {
                    continue;
                };
                methods.push(crate::hil::ty2::types::MetamethodType { method, ty });
            }
        }
        methods.sort_by_key(|entry| entry.method as u8);
        methods.dedup_by_key(|entry| entry.method);
        if methods.is_empty() {
            base
        } else {
            self.types.intern(MonoType::WithMetatable { base, methods })
        }
    }

    /// Materializes a lifted proto's parameter and return pack.
    fn materialize_function(
        &mut self,
        proto: ProtoId,
        visiting: &mut HashSet<InferenceVarId>,
    ) -> MonoTypeId {
        let Some(function) = self.functions.get(proto.0 as usize) else {
            return self.types.primitives().function;
        };
        let params = function.symbols.params.clone();
        let is_vararg = function.is_vararg;
        let param_types: Vec<_> = params
            .into_iter()
            .map(|parameter| {
                let slot = TypeSlot::Symbol(proto, parameter);
                let variable = self.variable_for_slot(slot);
                self.parameter_upper_bound(slot, variable)
                    .or_else(|| self.resolved_type(variable, visiting))
                    .unwrap_or(self.types.primitives().unknown)
            })
            .collect();
        let params = self.types.intern_pack(TypePack {
            head: param_types,
            tail: is_vararg.then_some(self.types.primitives().unknown),
        });

        let return_count = self.return_counts.get(&proto).copied().unwrap_or(0);
        let return_types: Vec<_> = (0..return_count)
            .map(|index| {
                let variable = self.variable_for_slot(TypeSlot::Return(proto, index));
                self.compatible_upper_bound(variable)
                    .or_else(|| self.resolved_type(variable, visiting))
                    .unwrap_or(self.types.primitives().unknown)
            })
            .collect();
        let returns = self.types.intern_pack(TypePack {
            head: return_types,
            tail: None,
        });
        self.types
            .intern(MonoType::FunctionSignature { params, returns })
    }

    /// Returns a precise consumer bound when producer mismatch is only nil or dynamic.
    fn compatible_upper_bound(&self, variable: InferenceVarId) -> Option<MonoTypeId> {
        let facts = &self.variables[variable];
        (self.types.is_emittable_upper_bound(facts.upper)
            && self.can_default_to(variable, facts.upper))
        .then_some(facts.upper)
    }

    /// Returns a body's precise parameter requirement when call evidence is only dynamic.
    fn parameter_upper_bound(
        &self,
        slot: TypeSlot,
        variable: InferenceVarId,
    ) -> Option<MonoTypeId> {
        let TypeSlot::Symbol(proto, symbol) = slot else {
            return None;
        };
        let function = self.functions.get(proto.0 as usize)?;
        if !function.symbols.params.contains(&symbol) {
            return None;
        }
        self.compatible_upper_bound(variable)
    }

    /// Resolves one durable symbol into an owned source type.
    fn resolved_symbol_type(&mut self, slot: TypeSlot) -> Option<Type> {
        let variable = *self.variables_by_slot.get(&slot)?;
        let closure_proto = {
            let closures = &self.variables[variable].closures;
            (closures.len() == 1).then(|| *closures.iter().next().expect("one closure exists"))
        };
        let ty = self
            .parameter_upper_bound(slot, variable)
            .or_else(|| self.resolved_type(variable, &mut HashSet::new()))?;
        let mut ty = self.types.to_surface(ty);
        if let TypeSlot::Symbol(proto, symbol) = slot
            && let Some(parameter) = self.generic_parameter_type(proto, symbol, &ty)
        {
            ty = parameter;
        } else if let Some(proto) = closure_proto {
            ty = self.generic_function_type(proto, ty);
        }
        if ty.contains_metatable() {
            // Luau has no direct structural annotation syntax for an arbitrary
            // inferred metatable. Printing only the base table would erase
            // operator support and can make otherwise valid code fail checking.
            return None;
        }
        let ty = ty.widen_literals();
        ty.is_meaningful().then_some(ty)
    }

    /// Rewrites a recovered function signature with every proven source generic.
    fn generic_function_type(&self, proto: ProtoId, ty: Type) -> Type {
        let Type::Function {
            mut generics,
            mut params,
            mut return_type,
        } = ty
        else {
            return ty;
        };
        let Some(function) = self.functions.get(proto.0 as usize) else {
            return Type::Function {
                generics,
                params,
                return_type,
            };
        };

        for (index, symbol) in function.symbols.params.iter().copied().enumerate() {
            let Some(param) = params.get(index) else {
                continue;
            };
            let base = match param {
                FunctionTypeParam::Type(ty) | FunctionTypeParam::Vararg(ty) => ty,
            };
            let Some((names, table)) = self.generic_parameter_shape(proto, symbol, base) else {
                continue;
            };
            for name in names {
                if !generics.contains(&name) {
                    generics.push(name);
                }
            }
            params[index] = FunctionTypeParam::Type(table);
        }

        for plan in self.generic_value_plans(proto) {
            if !generics.contains(&plan.name) {
                generics.push(plan.name.clone());
            }
            let pattern = self.generic_value_pattern(&plan);
            if let Some(parameter) = params.get_mut(plan.parameter_index) {
                *parameter = FunctionTypeParam::Type(pattern.clone());
            }
            for return_index in plan.return_indices {
                if let Some(returned) = return_type.get_mut(return_index) {
                    *returned = FunctionTypeReturn::Type(pattern.clone());
                }
            }
        }

        Type::Function {
            generics,
            params,
            return_type,
        }
    }

    /// Returns a generic parameter annotation for a directly emitted parameter.
    fn generic_parameter_type(
        &self,
        proto: ProtoId,
        symbol: SymbolId,
        base: &Type,
    ) -> Option<Type> {
        if let Some(plan) = self
            .generic_value_plans(proto)
            .into_iter()
            .find(|plan| plan.parameter == symbol)
        {
            return Some(self.generic_value_pattern(&plan));
        }
        self.generic_parameter_shape(proto, symbol, base)
            .map(|(_, table)| table)
    }

    /// Plans collision-free direct-value generics whose formal upper bound stayed unknown.
    fn generic_value_plans(&self, proto: ProtoId) -> Vec<GenericValuePlan> {
        let Some(relations) = self.generic_value_relations.get(&proto) else {
            return Vec::new();
        };

        // Same-table field generics conventionally occupy the prefix T, T1, ...
        // Reserve that full prefix so direct-value names are stable and disjoint.
        let mut fields_by_parameter: HashMap<SymbolId, HashSet<SmolStr>> = HashMap::new();
        if let Some(calls) = self.generic_field_calls.get(&proto) {
            for call in calls {
                let fields = fields_by_parameter.entry(call.parameter).or_default();
                fields.extend(call.field_arguments.iter().map(|(_, field)| field.clone()));
            }
        }
        let reserved_count = fields_by_parameter
            .values()
            .map(HashSet::len)
            .max()
            .unwrap_or(0);

        let mut sorted = relations.clone();
        sorted.sort_by_key(|relation| (relation.parameter_index, relation.return_index));
        sorted.dedup();
        let unknown = self.types.primitives().unknown;
        let mut plans: Vec<GenericValuePlan> = Vec::new();
        for relation in sorted {
            let slot = TypeSlot::Symbol(proto, relation.parameter);
            let Some(variable) = self.variables_by_slot.get(&slot) else {
                continue;
            };
            if self.variables[*variable].upper != unknown {
                continue;
            }
            if let Some(existing) = plans
                .iter_mut()
                .find(|plan| plan.parameter_index == relation.parameter_index)
            {
                existing.return_indices.push(relation.return_index);
                continue;
            }
            let name_index = reserved_count + plans.len();
            plans.push(GenericValuePlan {
                parameter: relation.parameter,
                parameter_index: relation.parameter_index,
                return_indices: vec![relation.return_index],
                name: Self::conventional_generic_name(name_index),
                optional: self
                    .omitted_parameters
                    .contains(&(proto, relation.parameter_index)),
            });
        }
        for plan in &mut plans {
            plan.return_indices.sort_unstable();
            plan.return_indices.dedup();
        }
        plans
    }

    /// Returns `T`, `T1`, and subsequent conventional generic names.
    fn conventional_generic_name(index: usize) -> SmolStr {
        if index == 0 {
            "T".into()
        } else {
            format_smolstr!("T{index}")
        }
    }

    /// Builds the exact shared parameter/return pattern for one direct-value plan.
    fn generic_value_pattern(&self, plan: &GenericValuePlan) -> Type {
        let generic = Type::Generic(plan.name.clone());
        if plan.optional {
            Type::Union(vec![generic, Type::Nil])
        } else {
            generic
        }
    }

    /// Builds one structural table parameter from same-object field relations.
    fn generic_parameter_shape(
        &self,
        proto: ProtoId,
        symbol: SymbolId,
        base: &Type,
    ) -> Option<(Vec<SmolStr>, Type)> {
        let mut calls: Vec<_> = self
            .generic_field_calls
            .get(&proto)?
            .iter()
            .filter(|call| call.parameter == symbol)
            .cloned()
            .collect();
        if calls.is_empty() {
            return None;
        }
        calls.sort_by(|lhs, rhs| lhs.callee.cmp(&rhs.callee));

        let mut fields = HashMap::new();
        Self::collect_surface_field_names(base, &mut fields);
        let mut generic_by_field: HashMap<SmolStr, SmolStr> = HashMap::new();
        for call in &calls {
            for (_, field) in &call.field_arguments {
                let next_index = generic_by_field.len();
                generic_by_field.entry(field.clone()).or_insert_with(|| {
                    if next_index == 0 {
                        "T".into()
                    } else {
                        format_smolstr!("T{next_index}")
                    }
                });
            }
        }

        for (field, generic) in &generic_by_field {
            fields.insert(field.clone(), Type::Generic(generic.clone()));
        }
        for call in calls {
            let param_count = call
                .field_arguments
                .iter()
                .map(|(index, _)| index + 1)
                .max()
                .unwrap_or(0);
            let mut callback_params = vec![FunctionTypeParam::Type(Type::Unknown); param_count];
            for (index, field) in call.field_arguments {
                let generic = generic_by_field
                    .get(&field)
                    .expect("generic field was indexed before callback construction");
                callback_params[index] = FunctionTypeParam::Type(Type::Generic(generic.clone()));
            }
            let callback_returns = if call.return_count == 0 {
                vec![FunctionTypeReturn::Type(Type::Unit)]
            } else {
                vec![FunctionTypeReturn::Type(Type::Unknown); call.return_count]
            };
            fields.insert(
                call.callee,
                Type::Function {
                    generics: Vec::new(),
                    params: callback_params,
                    return_type: callback_returns,
                },
            );
        }

        let mut names: Vec<_> = generic_by_field.into_values().collect();
        names.sort();
        Some((
            names,
            Type::Table {
                fields,
                array: None,
            },
        ))
    }

    /// Collects field names that occur in any structural table alternative.
    fn collect_surface_field_names(ty: &Type, fields: &mut HashMap<SmolStr, Type>) {
        match ty {
            Type::Table {
                fields: table_fields,
                ..
            } => {
                for name in table_fields.keys() {
                    fields.entry(name.clone()).or_insert(Type::Unknown);
                }
            }
            Type::Union(members) | Type::Intersection(members) => {
                for member in members {
                    Self::collect_surface_field_names(member, fields);
                }
            }
            _ => {}
        }
    }
}

impl TypeSolver<'_> {
    /// Activates newly discovered closure and builtin targets for `callee`.
    fn activate_calls(&mut self, callee: InferenceVarId) {
        let call_ids = self
            .callsites_by_callee
            .get(&callee)
            .cloned()
            .unwrap_or_default();
        let closures: Vec<_> = self.variables[callee].closures.iter().copied().collect();
        let builtins: Vec<_> = self.variables[callee].builtins.iter().cloned().collect();

        for call_id in call_ids {
            let call = self.callsites[call_id].clone();
            debug_assert_eq!(call.callee, callee);
            for proto in &closures {
                if self.activated_closures.insert((call_id, *proto)) {
                    self.connect_call_to_proto(&call, *proto);
                }
            }
            for path in &builtins {
                if self.activated_builtins.insert((call_id, path.clone())) {
                    self.instantiate_builtin(&call, path);
                }
            }
        }
    }

    /// Connects one callsite to one concrete lifted closure.
    fn connect_call_to_proto(&mut self, call: &CallSite, proto: ProtoId) {
        let Some(function) = self.functions.get(proto.0 as usize) else {
            return;
        };
        let params = function.symbols.params.clone();
        for (parameter_index, parameter) in params.into_iter().enumerate() {
            let formal = self.variable_for_slot(TypeSlot::Symbol(proto, parameter));
            if let Some(argument) = call.args.get(parameter_index) {
                self.add_constraint(formal, SolverConstraint::FlowFrom(*argument));
            } else {
                self.add_constraint(
                    formal,
                    SolverConstraint::Observe(self.types.primitives().nil),
                );
                self.mark_parameter_omitted(proto, parameter_index);
            }
        }

        let return_count = self.return_counts.get(&proto).copied().unwrap_or(0);
        let relations = self
            .generic_value_relations
            .get(&proto)
            .cloned()
            .unwrap_or_default();
        for (return_index, target) in call.returns.iter().enumerate() {
            if let Some(relation) = relations
                .iter()
                .find(|relation| relation.return_index == return_index)
            {
                self.record_correlated_call_result(proto, relation.parameter_index, *target);
                if let Some(argument) = call.args.get(relation.parameter_index) {
                    self.add_constraint(*target, SolverConstraint::FlowFrom(*argument));
                } else {
                    self.add_constraint(
                        *target,
                        SolverConstraint::Observe(self.types.primitives().nil),
                    );
                }
            } else if return_index < return_count {
                let source = self.variable_for_slot(TypeSlot::Return(proto, return_index));
                self.add_constraint(*target, SolverConstraint::FlowFrom(source));
            } else {
                self.add_constraint(
                    *target,
                    SolverConstraint::Observe(self.types.primitives().nil),
                );
            }
        }
    }

    /// Marks one fixed formal omitted and optionalizes all related call destinations.
    fn mark_parameter_omitted(&mut self, proto: ProtoId, parameter_index: usize) {
        let key = (proto, parameter_index);
        if !self.omitted_parameters.insert(key) {
            return;
        }
        let targets = self
            .correlated_call_results
            .get(&key)
            .cloned()
            .unwrap_or_default();
        for target in targets {
            self.add_constraint(
                target,
                SolverConstraint::Observe(self.types.primitives().nil),
            );
        }
    }

    /// Records one correlated destination and applies any previously discovered omission.
    fn record_correlated_call_result(
        &mut self,
        proto: ProtoId,
        parameter_index: usize,
        target: InferenceVarId,
    ) {
        let key = (proto, parameter_index);
        self.correlated_call_results
            .entry(key)
            .or_default()
            .insert(target);
        if self.omitted_parameters.contains(&key) {
            self.add_constraint(
                target,
                SolverConstraint::Observe(self.types.primitives().nil),
            );
        }
    }

    /// Applies the mutable heap semantics attached to one builtin call.
    fn apply_builtin_effect(&mut self, call: &CallSite, effect: BuiltinCallEffect) {
        match effect {
            BuiltinCallEffect::SetIndex {
                table_argument,
                index,
                value_argument,
            } => {
                let Some(&table) = call.args.get(table_argument) else {
                    return;
                };
                let Some(&value) = call.args.get(value_argument) else {
                    return;
                };
                let index = match index {
                    BuiltinIndex::Argument(argument) => {
                        let Some(&index) = call.args.get(argument) else {
                            return;
                        };
                        index
                    }
                    BuiltinIndex::Number => {
                        let index = self.fresh_variable();
                        self.add_constraint(
                            index,
                            SolverConstraint::Observe(self.types.primitives().number),
                        );
                        index
                    }
                };
                self.add_constraint(table, SolverConstraint::SetIndex { index, value });
            }
            BuiltinCallEffect::SetMetatable {
                table_argument,
                metatable_argument,
            } => {
                let Some(&table) = call.args.get(table_argument) else {
                    return;
                };
                let Some(&metatable) = call.args.get(metatable_argument) else {
                    return;
                };
                self.add_constraint(
                    table,
                    SolverConstraint::SetMetatable {
                        metatable,
                        result: call.returns.first().copied(),
                    },
                );
            }
        }
    }

    /// Instantiates one builtin scheme at one callsite.
    fn instantiate_builtin(&mut self, call: &CallSite, path: &BuiltinPath) {
        if let Some(effect) = path.call_effect(call.args.len()) {
            self.apply_builtin_effect(call, effect);
        }
        let Some(scheme) = self.builtins.get_path(path).cloned() else {
            return;
        };
        let alternatives = match scheme {
            Type::Intersection(types) => types,
            ty => vec![ty],
        };
        let mut viable: Vec<_> = alternatives
            .into_iter()
            .filter(|alternative| Self::function_accepts_arity(alternative, call.args.len()))
            .collect();

        if viable.len() > 1 {
            viable.retain(|alternative| self.signature_may_accept(alternative, &call.args));
        }
        if viable.len() == 1 {
            self.instantiate_function_scheme(call, &viable[0]);
        } else {
            self.observe_common_overload_returns(call, &viable);
        }
    }

    /// Returns whether a function scheme can accept `arity` fixed arguments.
    fn function_accepts_arity(scheme: &Type, arity: usize) -> bool {
        let Type::Function { params, .. } = scheme else {
            return false;
        };
        let fixed_params: Vec<_> = params
            .iter()
            .take_while(|param| matches!(param, FunctionTypeParam::Type(_)))
            .collect();
        let fixed = fixed_params.len();
        let optional = fixed_params
            .iter()
            .rev()
            .take_while(|param| match param {
                FunctionTypeParam::Type(ty) => ty.accepts_nil(),
                FunctionTypeParam::Vararg(_) => false,
            })
            .count();
        let minimum = fixed - optional;
        let variadic = params
            .iter()
            .any(|param| matches!(param, FunctionTypeParam::Vararg(_)));
        (minimum..=fixed).contains(&arity) || (variadic && arity >= minimum)
    }

    /// Returns whether current producer facts do not contradict a monomorphic signature.
    fn signature_may_accept(&mut self, scheme: &Type, args: &[InferenceVarId]) -> bool {
        let Type::Function { params, .. } = scheme else {
            return false;
        };
        for (argument, parameter) in args.iter().zip(params) {
            let (FunctionTypeParam::Type(parameter) | FunctionTypeParam::Vararg(parameter)) =
                parameter;
            if parameter.contains_generic() {
                continue;
            }
            let Some(parameter) = self.types.lower_surface(parameter) else {
                continue;
            };
            let Some(argument) = self.produced_type(*argument) else {
                continue;
            };
            if !self.types.is_subtype(argument, parameter) {
                return false;
            }
        }
        true
    }

    /// Instantiates one selected function scheme with fresh generic variables.
    fn instantiate_function_scheme(&mut self, call: &CallSite, scheme: &Type) {
        let Type::Function {
            generics,
            params,
            return_type,
        } = scheme
        else {
            return;
        };
        let generic_variables: HashMap<_, _> = generics
            .iter()
            .map(|name| (name.clone(), self.fresh_variable()))
            .collect();

        let mut fixed_index = 0usize;
        for parameter in params {
            match parameter {
                FunctionTypeParam::Type(pattern) => {
                    if let Some(argument) = call.args.get(fixed_index) {
                        self.bind_argument_pattern(*argument, pattern, &generic_variables);
                    }
                    fixed_index += 1;
                }
                FunctionTypeParam::Vararg(pattern) => {
                    for argument in call.args.iter().skip(fixed_index) {
                        self.bind_argument_pattern(*argument, pattern, &generic_variables);
                    }
                    break;
                }
            }
        }

        let mut fixed_index = 0usize;
        for returned in return_type {
            match returned {
                FunctionTypeReturn::Type(pattern) => {
                    if let Some(target) = call.returns.get(fixed_index) {
                        self.emit_return_pattern(*target, pattern, &generic_variables);
                    }
                    fixed_index += 1;
                }
                FunctionTypeReturn::Vararg(pattern) => {
                    for target in call.returns.iter().skip(fixed_index) {
                        self.emit_return_pattern(*target, pattern, &generic_variables);
                    }
                    return;
                }
            }
        }
        for target in call.returns.iter().skip(fixed_index) {
            self.add_constraint(
                *target,
                SolverConstraint::Observe(self.types.primitives().nil),
            );
        }
    }

    /// Applies one parameter pattern to an actual argument.
    fn bind_argument_pattern(
        &mut self,
        argument: InferenceVarId,
        pattern: &Type,
        generics: &HashMap<SmolStr, InferenceVarId>,
    ) {
        match pattern {
            Type::Generic(name) => {
                if let Some(generic) = generics.get(name) {
                    self.add_constraint(*generic, SolverConstraint::FlowFrom(argument));
                }
            }
            Type::Table { fields, array } => {
                let tables: Vec<_> = self.variables[argument].tables.iter().copied().collect();
                for table in tables {
                    if let Some(array) = array {
                        let (key_pattern, value_pattern) = array.as_ref();
                        let keys = self.tables[table].keys;
                        let values = self.tables[table].values;
                        self.bind_argument_pattern(keys, key_pattern, generics);
                        self.bind_argument_pattern(values, value_pattern, generics);
                    }

                    let mut fields: Vec<_> = fields.iter().collect();
                    fields.sort_by_key(|(lhs, _)| *lhs);
                    for (name, pattern) in fields {
                        let value = self.table_field_variable(table, name.clone(), false);
                        self.bind_argument_pattern(value, pattern, generics);
                    }
                }
            }
            Type::Union(members) => {
                let generic_members: Vec<_> = members
                    .iter()
                    .filter_map(|member| match member {
                        Type::Generic(name) => generics.get(name).copied(),
                        _ => None,
                    })
                    .collect();
                let concrete: Vec<_> = members
                    .iter()
                    .filter(|member| !matches!(member, Type::Generic(_)))
                    .filter_map(|member| self.types.lower_surface(member))
                    .collect();
                if generic_members.is_empty() {
                    if let Some(accepted) = self.types.lower_surface(pattern) {
                        self.add_constraint(argument, SolverConstraint::Require(accepted));
                    }
                } else if generic_members.len() == 1 {
                    self.add_constraint(
                        generic_members[0],
                        SolverConstraint::GenericFrom {
                            source: argument,
                            excluded: concrete,
                        },
                    );
                }
            }
            _ if !pattern.contains_generic() => {
                if let Some(accepted) = self.types.lower_surface(pattern) {
                    self.add_constraint(argument, SolverConstraint::Require(accepted));
                }
            }
            _ => {
                // Nested generic table/function patterns require structural
                // matching. Leaving them unconstrained is conservative: the
                // corresponding result generic also remains unresolved rather
                // than being independently guessed.
            }
        }
    }

    /// Emits one instantiated return pattern into a call destination.
    fn emit_return_pattern(
        &mut self,
        target: InferenceVarId,
        pattern: &Type,
        generics: &HashMap<SmolStr, InferenceVarId>,
    ) {
        match pattern {
            Type::Generic(name) => {
                if let Some(generic) = generics.get(name) {
                    self.add_constraint(target, SolverConstraint::FlowFrom(*generic));
                }
            }
            Type::Union(members) => {
                for member in members {
                    self.emit_return_pattern(target, member, generics);
                }
            }
            _ if !pattern.contains_generic() => {
                if let Some(ty) = self.types.lower_surface(pattern) {
                    self.add_constraint(target, SolverConstraint::Observe(ty));
                }
            }
            _ => {}
        }
    }

    /// Observes only return types shared safely across unresolved overloads.
    fn observe_common_overload_returns(&mut self, call: &CallSite, alternatives: &[Type]) {
        for (index, target) in call.returns.iter().enumerate() {
            let mut returns = Vec::new();
            for alternative in alternatives {
                let Type::Function { return_type, .. } = alternative else {
                    continue;
                };
                let Some(returned) = return_type.get(index) else {
                    returns.push(self.types.primitives().nil);
                    continue;
                };
                let returned = match returned {
                    FunctionTypeReturn::Type(ty) | FunctionTypeReturn::Vararg(ty) => ty,
                };
                if returned.contains_generic() {
                    returns.clear();
                    break;
                }
                if let Some(returned) = self.types.lower_surface(returned) {
                    returns.push(returned);
                }
            }
            if !returns.is_empty() {
                let returned = self.types.union_all(returns);
                self.observe(*target, returned);
            }
        }
    }

    /// Infers a callable upper bound from one otherwise dynamic callsite.
    fn infer_callable_requirement(
        &mut self,
        callee: InferenceVarId,
        args: &[InferenceVarId],
        returns: &[InferenceVarId],
    ) {
        let facts = &self.variables[callee];
        if !facts.tables.is_empty() || !facts.closures.is_empty() || !facts.builtins.is_empty() {
            return;
        }
        if !matches!(
            self.types.get(facts.lower),
            MonoType::Never | MonoType::Unknown | MonoType::Any
        ) {
            return;
        }
        let Some(params) = args
            .iter()
            .map(|argument| self.callsite_bound_type(*argument))
            .collect::<Option<Vec<_>>>()
        else {
            return;
        };
        let Some(returns) = returns
            .iter()
            .map(|returned| self.callsite_bound_type(*returned))
            .collect::<Option<Vec<_>>>()
        else {
            return;
        };
        let params = self.types.intern_pack(TypePack {
            head: params,
            tail: None,
        });
        let returns = self.types.intern_pack(TypePack {
            head: returns,
            tail: None,
        });
        let signature = self
            .types
            .intern(MonoType::FunctionSignature { params, returns });
        self.require(callee, signature);
    }

    /// Returns the precise produced or required type available at one call slot.
    fn callsite_bound_type(&self, variable: InferenceVarId) -> Option<MonoTypeId> {
        if let Some(candidate) = self.candidate_type(variable) {
            return Some(candidate);
        }
        let upper = self.variables[variable].upper;
        (self.types.is_emittable_upper_bound(upper) && self.can_default_to(variable, upper))
            .then_some(upper)
    }

    /// Applies one unique monomorphic signature found in the callee's lower bound.
    fn apply_callable_monotype(
        &mut self,
        callee: InferenceVarId,
        args: &[InferenceVarId],
        returns: &[InferenceVarId],
    ) {
        let Some(callee_ty) = self.produced_type(callee) else {
            return;
        };
        let mut signatures = Vec::new();
        self.collect_function_signatures(callee_ty, &mut signatures);
        signatures.sort_unstable();
        signatures.dedup();
        let [signature] = signatures.as_slice() else {
            return;
        };
        let MonoType::FunctionSignature {
            params,
            returns: result_pack,
        } = self.types.get(*signature)
        else {
            return;
        };
        let params = self.types.get_pack(*params).clone();
        let result_pack = self.types.get_pack(*result_pack).clone();

        for (index, argument) in args.iter().enumerate() {
            let accepted = params.head.get(index).copied().or(params.tail);
            if let Some(accepted) = accepted {
                self.require(*argument, accepted);
            }
        }
        for (index, target) in returns.iter().enumerate() {
            if let Some(returned) = result_pack.head.get(index).copied().or(result_pack.tail) {
                self.observe(*target, returned);
            } else {
                self.observe(*target, self.types.primitives().nil);
            }
        }
    }

    /// Collects concrete function signatures nested inside a monotype.
    fn collect_function_signatures(&self, ty: MonoTypeId, output: &mut Vec<MonoTypeId>) {
        match self.types.get(ty) {
            MonoType::FunctionSignature { .. } => output.push(ty),
            MonoType::Union(members) | MonoType::Intersection(members) => {
                for member in members {
                    self.collect_function_signatures(*member, output);
                }
            }
            MonoType::WithMetatable { methods, .. } => {
                for method in methods {
                    if method.method == Metamethod::Call {
                        self.collect_function_signatures(method.ty, output);
                    }
                }
            }
            _ => {}
        }
    }
}

/// Runs whole-program inference and writes conservative symbol annotations back.
pub fn run(functions: &mut [LiftedFunction]) {
    let builtins = BuiltinEnvironment::new();
    let mut program = CollectedProgram::default();
    for function in functions.iter() {
        program.extend(ConstraintCollector::collect(function, functions, &builtins));
    }

    let mut seeds: HashMap<TypeSlot, Vec<Type>> = HashMap::new();
    for function in functions.iter() {
        for (symbol, ty) in function.types.symbol_types() {
            seeds
                .entry(TypeSlot::Symbol(function.proto, symbol))
                .or_default()
                .push(ty.clone());
        }
    }

    let mut solver = TypeSolver::new(program, functions, &builtins, seeds);
    solver.solve();
    let symbol_slots: Vec<_> = solver
        .variables_by_slot
        .keys()
        .filter_map(|slot| match slot {
            TypeSlot::Symbol(proto, symbol) => Some((*proto, *symbol, *slot)),
            _ => None,
        })
        .collect();
    let inferred: Vec<_> = symbol_slots
        .into_iter()
        .filter_map(|(proto, symbol, slot)| {
            solver
                .resolved_symbol_type(slot)
                .map(|ty| (proto, symbol, ty))
        })
        .collect();
    drop(solver);

    for (proto, symbol, ty) in inferred {
        if let Some(function) = functions.get_mut(proto.0 as usize) {
            function.types.set_inferred_symbol_type(symbol, ty);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use id_arena::Arena;

    use super::{
        CallSite, CollectedConstraint, CollectedProgram, GenericFieldCall, GenericValueRelation,
        SolverConstraint, TableKey, TypeSlot, TypeSolver,
    };
    use crate::{
        hil::{
            lifter::ssa::Symbol,
            ty::{FunctionTypeParam, FunctionTypeReturn, Type},
            ty2::{
                builtins::{BuiltinEnvironment, BuiltinPath},
                types::MonoType,
            },
        },
        il::ProtoId,
    };

    /// Builds an empty solver suitable for bound-algebra unit tests.
    fn empty_solver<'a>(builtins: &'a BuiltinEnvironment) -> TypeSolver<'a> {
        TypeSolver::new(CollectedProgram::default(), &[], builtins, HashMap::new())
    }

    /// Consumer requirements intersect instead of widening into an invalid union.
    #[test]
    fn requirements_intersect() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let variable = solver.fresh_variable();
        let primitives = solver.types.primitives();
        let string_or_number = solver.types.union(primitives.string, primitives.number);

        solver.add_constraint(variable, SolverConstraint::Require(string_or_number));
        solver.add_constraint(variable, SolverConstraint::Require(primitives.number));
        solver.solve();

        assert_eq!(solver.candidate_type(variable), Some(primitives.number));
    }

    /// Broad capability markers validate evidence but never seed annotations alone.
    #[test]
    fn broad_table_requirement_is_not_an_annotation_candidate() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let variable = solver.fresh_variable();
        let table = solver.types.primitives().table;

        solver.add_constraint(variable, SolverConstraint::Require(table));
        solver.solve();

        assert_eq!(solver.candidate_type(variable), None);
    }

    /// Conflicting producer evidence and consumer requirements suppress a solution.
    #[test]
    fn inconsistent_bounds_do_not_produce_an_annotation() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let variable = solver.fresh_variable();
        let primitives = solver.types.primitives();

        solver.add_constraint(variable, SolverConstraint::Observe(primitives.string));
        solver.add_constraint(variable, SolverConstraint::Require(primitives.number));
        solver.solve();

        assert_eq!(solver.candidate_type(variable), None);
    }

    /// Optional producer evidence is narrowed only in the refined occurrence.
    #[test]
    fn truthy_refinement_does_not_mutate_definition() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let source = solver.fresh_variable();
        let refined = solver.fresh_variable();
        let primitives = solver.types.primitives();
        let optional = solver.types.union(primitives.string, primitives.nil);

        solver.add_constraint(source, SolverConstraint::Observe(optional));
        solver.add_constraint(
            refined,
            SolverConstraint::RefinedFrom {
                source,
                truthiness: super::Truthiness::Truthy,
            },
        );
        solver.solve();

        assert_eq!(solver.produced_type(source), Some(optional));
        assert_eq!(solver.produced_type(refined), Some(primitives.string));
    }

    /// Producer-free refinements remain absent until the ordinary queue is quiescent.
    #[test]
    fn refinement_fallback_runs_only_after_quiescence() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let truthy = solver.fresh_variable();
        let falsy = solver.fresh_variable();
        let source = solver.fresh_variable();
        solver.add_constraint(
            truthy,
            SolverConstraint::RefinedFrom {
                source,
                truthiness: super::Truthiness::Truthy,
            },
        );
        solver.add_constraint(
            falsy,
            SolverConstraint::RefinedFrom {
                source,
                truthiness: super::Truthiness::Falsy,
            },
        );

        solver.drain_queue();
        assert_eq!(solver.produced_type(truthy), None);
        assert_eq!(solver.produced_type(falsy), None);
        assert_eq!(solver.deferred_refinements.len(), 2);

        assert!(solver.activate_deferred_refinements());
        solver.drain_queue();
        let unknown = solver.types.primitives().unknown;
        let unknown_falsy = solver.types.falsy_part(unknown);
        assert_eq!(solver.produced_type(truthy), Some(unknown));
        assert_eq!(solver.produced_type(falsy), Some(unknown_falsy));
    }

    /// Concrete evidence scheduled after a refinement wins before fallback activation.
    #[test]
    fn late_refinement_evidence_stays_precise() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let refined = solver.fresh_variable();
        let source = solver.fresh_variable();
        let number = solver.types.primitives().number;
        solver.add_constraint(
            refined,
            SolverConstraint::RefinedFrom {
                source,
                truthiness: super::Truthiness::Truthy,
            },
        );
        solver.add_constraint(source, SolverConstraint::Observe(number));

        solver.solve();

        assert_eq!(solver.produced_type(refined), Some(number));
        assert!(solver.activated_refinement_fallbacks.is_empty());
    }

    /// Surface `unknown` remains a real type rather than absence of evidence.
    #[test]
    fn unknown_observation_is_not_replaced_by_concrete_evidence() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let variable = solver.fresh_variable();
        let unknown = solver
            .types
            .lower_surface(&Type::Unknown)
            .expect("unknown is a monotype");
        let number = solver.types.primitives().number;

        solver.add_constraint(variable, SolverConstraint::Observe(unknown));
        solver.add_constraint(variable, SolverConstraint::Observe(number));
        solver.solve();

        assert_eq!(solver.produced_type(variable), Some(unknown));
    }

    /// Direct identity metadata rejects mixed, omitted, and otherwise used formals.
    #[test]
    fn direct_value_relation_proof_is_strict_and_deterministic() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let parameter = symbols.alloc(Symbol::param(0));
        let other = symbols.alloc(Symbol::param(1));
        let proto = ProtoId(0);
        let formal = TypeSlot::Symbol(proto, parameter);
        let returned = TypeSlot::Return(proto, 0);
        let mut program = CollectedProgram::default();
        program.push(returned, CollectedConstraint::FlowFrom(formal));

        let relations =
            program.direct_value_relations(proto, &[parameter, other], &[1, 1], &HashSet::new());
        assert_eq!(relations.len(), 1);
        assert_eq!(relations[0].parameter_index, 0);
        assert_eq!(relations[0].return_index, 0);
        assert!(
            program
                .direct_value_relations(proto, &[parameter, other], &[1, 0], &HashSet::new())
                .is_empty()
        );
        assert!(
            program
                .direct_value_relations(
                    proto,
                    &[parameter, other],
                    &[1, 1],
                    &HashSet::from([parameter]),
                )
                .is_empty()
        );

        program.push(
            returned,
            CollectedConstraint::FlowFrom(TypeSlot::Symbol(proto, other)),
        );
        assert!(
            program
                .direct_value_relations(proto, &[parameter, other], &[1, 1], &HashSet::new())
                .is_empty()
        );
    }

    /// Direct-value plans reserve table generic names and optionalize both positions.
    #[test]
    fn direct_value_plan_is_optional_collision_free_and_bound_guarded() {
        let builtins = BuiltinEnvironment::new();
        let mut symbols: Arena<Symbol> = Arena::new();
        let table_parameter = symbols.alloc(Symbol::param(0));
        let value_parameter = symbols.alloc(Symbol::param(1));
        let proto = ProtoId(0);
        let mut program = CollectedProgram::default();
        program.generic_field_calls.insert(
            proto,
            vec![GenericFieldCall {
                parameter: table_parameter,
                callee: "visit".into(),
                field_arguments: vec![(0, "value".into())],
                return_count: 1,
            }],
        );
        program.generic_value_relations.insert(
            proto,
            vec![GenericValueRelation {
                parameter: value_parameter,
                parameter_index: 1,
                return_index: 0,
            }],
        );
        let mut solver = TypeSolver::new(program, &[], &builtins, HashMap::new());
        let formal = solver.variable_for_slot(TypeSlot::Symbol(proto, value_parameter));
        solver.omitted_parameters.insert((proto, 1));

        let plans = solver.generic_value_plans(proto);
        assert_eq!(plans.len(), 1);
        assert_eq!(plans[0].name.as_str(), "T1");
        assert_eq!(
            solver.generic_value_pattern(&plans[0]),
            Type::Union(vec![Type::Generic("T1".into()), Type::Nil])
        );

        let number = solver.types.primitives().number;
        solver.require(formal, number);
        assert!(solver.generic_value_plans(proto).is_empty());
    }

    /// Omission optionalizes correlated destinations registered before and after it.
    #[test]
    fn correlated_call_results_are_optionalized_without_order_dependence() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let proto = ProtoId(0);
        let present = solver.fresh_variable();
        let future = solver.fresh_variable();
        let number = solver.types.primitives().number;
        let nil = solver.types.primitives().nil;
        let optional_number = solver.types.union(number, nil);

        solver.record_correlated_call_result(proto, 0, present);
        solver.add_constraint(present, SolverConstraint::Observe(number));
        solver.solve();
        assert_eq!(solver.produced_type(present), Some(number));

        solver.mark_parameter_omitted(proto, 0);
        solver.record_correlated_call_result(proto, 0, future);
        solver.solve();

        assert_eq!(solver.produced_type(present), Some(optional_number));
        assert_eq!(solver.produced_type(future), Some(nil));
    }

    /// Known metatable arithmetic dispatches through the metamethod signature.
    #[test]
    fn arithmetic_uses_known_metamethod_return_type() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let base = solver.fresh_variable();
        let metatable = solver.fresh_variable();
        let method = solver.fresh_variable();
        let rhs = solver.fresh_variable();
        let result = solver.fresh_variable();
        let base_table = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 0,
        });
        let metatable_table = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 1,
        });
        let signature = Type::Function {
            generics: Vec::new(),
            params: vec![
                FunctionTypeParam::Type(Type::Table {
                    fields: HashMap::new(),
                    array: None,
                }),
                FunctionTypeParam::Type(Type::Number),
            ],
            return_type: vec![FunctionTypeReturn::Type(Type::String)],
        };
        let signature = solver
            .types
            .lower_surface(&signature)
            .expect("monomorphic function lowers");
        let number = solver.types.primitives().number;

        solver.add_constraint(base, SolverConstraint::NewTable(base_table));
        solver.add_constraint(metatable, SolverConstraint::NewTable(metatable_table));
        solver.add_constraint(method, SolverConstraint::Observe(signature));
        solver.add_constraint(
            metatable,
            SolverConstraint::SetField {
                field: "__add".into(),
                value: method,
                definite: true,
            },
        );
        solver.add_constraint(
            base,
            SolverConstraint::SetMetatable {
                metatable,
                result: None,
            },
        );
        solver.add_constraint(rhs, SolverConstraint::Observe(number));
        solver.add_constraint(
            base,
            SolverConstraint::Binary {
                op: crate::operator::BinOp::Add,
                rhs,
                result,
            },
        );
        solver.solve();

        assert!(
            solver.tables[base_table]
                .metatables
                .contains(&metatable_table)
        );
        assert!(matches!(
            solver
                .types
                .get(solver.produced_type(result).expect("metamethod result")),
            MonoType::String
        ));
    }

    /// Named and dynamic reads reconnect when a callable `__index` arrives late.
    #[test]
    fn late_callable_index_handler_reconnects_all_read_kinds() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let base = solver.fresh_variable();
        let metatable = solver.fresh_variable();
        let handler = solver.fresh_variable();
        let key = solver.fresh_variable();
        let named = solver.fresh_variable();
        let dynamic = solver.fresh_variable();
        let base_table = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 10,
        });
        let metatable_table = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 11,
        });
        let signature = Type::Function {
            generics: Vec::new(),
            params: vec![
                FunctionTypeParam::Type(Type::Unknown),
                FunctionTypeParam::Type(Type::String),
            ],
            return_type: vec![FunctionTypeReturn::Type(Type::String)],
        };
        let signature = solver
            .types
            .lower_surface(&signature)
            .expect("monomorphic index handler lowers");
        let string = solver.types.primitives().string;

        solver.add_constraint(base, SolverConstraint::NewTable(base_table));
        solver.add_constraint(metatable, SolverConstraint::NewTable(metatable_table));
        solver.add_constraint(
            base,
            SolverConstraint::SetMetatable {
                metatable,
                result: None,
            },
        );
        solver.add_constraint(
            base,
            SolverConstraint::GetField {
                field: "answer".into(),
                value: named,
            },
        );
        solver.add_constraint(key, SolverConstraint::Observe(string));
        solver.add_constraint(
            base,
            SolverConstraint::GetIndex {
                index: key,
                value: dynamic,
            },
        );
        solver.solve();

        solver.add_constraint(handler, SolverConstraint::Observe(signature));
        solver.add_constraint(
            metatable,
            SolverConstraint::SetField {
                field: "__index".into(),
                value: handler,
                definite: true,
            },
        );
        solver.solve();

        let named = solver.produced_type(named).expect("named index result");
        let dynamic = solver.produced_type(dynamic).expect("dynamic index result");
        assert!(solver.types.is_subtype(string, named));
        assert!(solver.types.is_subtype(string, dynamic));
    }

    /// Dynamic reads revisit named fields of a table-valued `__index` handler.
    #[test]
    fn table_valued_dynamic_index_revisits_late_named_fields() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let base = solver.fresh_variable();
        let metatable = solver.fresh_variable();
        let handler = solver.fresh_variable();
        let key = solver.fresh_variable();
        let field_value = solver.fresh_variable();
        let result = solver.fresh_variable();
        let base_table = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 20,
        });
        let metatable_table = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 21,
        });
        let handler_table = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 22,
        });
        let string = solver.types.primitives().string;
        let number = solver.types.primitives().number;

        solver.add_constraint(base, SolverConstraint::NewTable(base_table));
        solver.add_constraint(metatable, SolverConstraint::NewTable(metatable_table));
        solver.add_constraint(handler, SolverConstraint::NewTable(handler_table));
        solver.add_constraint(
            metatable,
            SolverConstraint::SetField {
                field: "__index".into(),
                value: handler,
                definite: true,
            },
        );
        solver.add_constraint(
            base,
            SolverConstraint::SetMetatable {
                metatable,
                result: None,
            },
        );
        solver.add_constraint(key, SolverConstraint::Observe(string));
        solver.add_constraint(
            base,
            SolverConstraint::GetIndex {
                index: key,
                value: result,
            },
        );
        solver.solve();

        solver.add_constraint(field_value, SolverConstraint::Observe(number));
        solver.add_constraint(
            handler,
            SolverConstraint::SetField {
                field: "answer".into(),
                value: field_value,
                definite: true,
            },
        );
        solver.solve();

        let result = solver.produced_type(result).expect("table index result");
        assert!(solver.types.is_subtype(number, result));
    }

    /// Setmetatable links the same metatable to every base identity.
    #[test]
    fn setmetatable_links_multiple_base_tables() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let base = solver.fresh_variable();
        let metatable = solver.fresh_variable();
        let first = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 30,
        });
        let second = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 31,
        });
        let meta = solver.table_for_key(TableKey {
            proto: ProtoId(0),
            index: 32,
        });

        solver.add_constraint(base, SolverConstraint::NewTable(first));
        solver.add_constraint(base, SolverConstraint::NewTable(second));
        solver.add_constraint(metatable, SolverConstraint::NewTable(meta));
        solver.add_constraint(
            base,
            SolverConstraint::SetMetatable {
                metatable,
                result: None,
            },
        );
        solver.solve();

        assert!(solver.tables[first].metatables.contains(&meta));
        assert!(solver.tables[second].metatables.contains(&meta));
    }

    /// Fresh builtin generics preserve argument-to-return relationships.
    #[test]
    fn builtin_generic_return_flows_from_argument() {
        let builtins = BuiltinEnvironment::new();
        let mut solver = empty_solver(&builtins);
        let argument = solver.fresh_variable();
        let returned = solver.fresh_variable();
        let string = solver.types.primitives().string;
        solver.add_constraint(argument, SolverConstraint::Observe(string));
        let call = CallSite {
            callee: solver.fresh_variable(),
            args: vec![argument],
            returns: vec![returned],
        };

        solver.instantiate_builtin(&call, &BuiltinPath::Global("assert".into()));
        solver.solve();

        assert_eq!(solver.produced_type(returned), Some(string));
    }
}
