//! HIL traversal and constraint collection.

use std::collections::{HashMap, HashSet};

use smol_str::SmolStr;

use crate::{
    hil::{
        cflow::cfg::BlockExit,
        ir::{Expr, Stmt, TableItem, ValuePack},
        lifted::LiftedFunction,
        lifter::ssa::SymbolId,
        ty2::{
            builtins::{BuiltinEnvironment, BuiltinPath},
            canonical::PrimitiveIds,
            inference::queue::WorkQueue,
        },
        visitor::Visitor,
    },
    operator::UnOp,
};

use super::program::{
    CollectedCallArgument, CollectedConstraint, CollectedFunction, CollectedPackConstraint,
    GenericFieldCall, PackSlot, Truthiness, TypeSlot,
};

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
}

/// Tracks table construction before the table is read or captured.
///
/// An origin here means an initial empty table assignment, ie. `local x = {}`.
/// If it gets copied to a new variable, ie. `local y = x`, `y` will still point to `x`,
/// as the origin. If the construction gets broken by a read, for instance:
/// ```luau
/// local x = {}
/// x[1] = 1
/// print(x[1])
/// x[2] = 2`
/// ```
/// the origin is no longer active.
#[derive(Debug, Default)]
struct TableConstructionTracker {
    /// Maps each tracked symbol to its origin.
    origin_by_symbol: HashMap<SymbolId, SymbolId>,

    /// Contains origins whose tables are still under construction.
    active_origins: HashSet<SymbolId>,
}

impl TableConstructionTracker {
    /// Starts construction of a table assigned to `symbol`.
    fn start(&mut self, symbol: SymbolId) {
        self.origin_by_symbol.insert(symbol, symbol);
        self.active_origins.insert(symbol);
    }

    /// Adds `target` as an alias of `source`.
    fn add_alias(&mut self, target: SymbolId, source: SymbolId) -> bool {
        let Some(origin) = self.active_origin(source) else {
            return false;
        };

        self.origin_by_symbol.insert(target, origin);
        true
    }

    /// Returns true if `symbol` refers to an active construction.
    fn is_active(&self, symbol: SymbolId) -> bool {
        self.active_origin(symbol).is_some()
    }

    /// Returns the active origin of `symbol`.
    fn active_origin(&self, symbol: SymbolId) -> Option<SymbolId> {
        let origin = self.origin_by_symbol.get(&symbol).copied()?;
        self.active_origins.contains(&origin).then_some(origin)
    }

    /// Invalidates every active origin read or captured in `expression`.
    fn invalidate_expression(&mut self, expression: &Expr) {
        let origins: Vec<_> = ExpressionSymbolCollector::collect(expression)
            .into_iter()
            .filter_map(|symbol| self.active_origin(symbol))
            .collect();
        for origin in origins {
            self.active_origins.remove(&origin);
        }
    }

    /// Returns whether an expression reads any alias of `symbol`'s construction.
    fn expression_reads(&self, expression: &Expr, symbol: SymbolId) -> bool {
        let Some(root) = self.active_origin(symbol) else {
            return false;
        };
        ExpressionSymbolCollector::collect(expression)
            .into_iter()
            .filter_map(|read| self.active_origin(read))
            .any(|read_root| read_root == root)
    }
}

/// Immutable membership and ordering information for one function's symbols.
struct FunctionSymbolIndex {
    /// Signature position of every formal parameter.
    parameter_indices: HashMap<SymbolId, usize>,
    /// Symbols backed by nonlocal upvalue storage.
    upvalues: HashSet<SymbolId>,
}

impl FunctionSymbolIndex {
    /// Indexes formal parameters and upvalues from one lifted function.
    fn new(function: &LiftedFunction) -> Self {
        let parameter_indices = function
            .symbols
            .params
            .iter()
            .copied()
            .enumerate()
            .map(|(index, symbol)| (symbol, index))
            .collect();
        let mut upvalues: HashSet<_> = function.symbols.upvalues.iter().copied().collect();
        for versions in function.symbols.upvalue_version_groups() {
            upvalues.extend(versions.iter().copied());
        }
        Self {
            parameter_indices,
            upvalues,
        }
    }

    /// Returns whether `symbol` is a formal parameter.
    fn is_parameter(&self, symbol: SymbolId) -> bool {
        self.parameter_indices.contains_key(&symbol)
    }

    /// Returns whether `symbol` is backed by nonlocal upvalue storage.
    fn is_upvalue(&self, symbol: SymbolId) -> bool {
        self.upvalues.contains(&symbol)
    }
}

/// Immutable symbol provenance used by source-level call recognition.
struct SymbolProvenance<'cfg> {
    /// Direct definition indexed by its SSA symbol.
    definitions: HashMap<SymbolId, &'cfg Expr>,
}

impl<'cfg> SymbolProvenance<'cfg> {
    /// Indexes direct symbol definitions from one lifted SSA graph.
    fn analyze(function: &'cfg LiftedFunction) -> Self {
        let mut provenance = Self {
            definitions: HashMap::new(),
        };
        for block in function.cfg.blocks() {
            for statement in block.stmts() {
                match statement {
                    Stmt::Assign {
                        left: Expr::Symbol(symbol),
                        value,
                    } => provenance.insert(*symbol, value),
                    Stmt::AssignMany { left, values } => {
                        for (lvalue, value) in left.iter().zip(values.head()) {
                            if let Expr::Symbol(symbol) = lvalue {
                                provenance.insert(*symbol, value);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        provenance
    }

    /// Records the single direct definition of one SSA symbol.
    fn insert(&mut self, symbol: SymbolId, value: &'cfg Expr) {
        self.definitions.insert(symbol, value);
    }

    /// Resolves one named-field read through direct SSA definitions and copies.
    fn resolve_field_access(&self, expression: &Expr) -> Option<ResolvedFieldAccess> {
        let mut expr = expression;
        loop {
            match expr {
                Expr::GetField { obj, field } => {
                    return Some(ResolvedFieldAccess {
                        object: self.resolve_symbol_expression(obj)?,
                        field: field.clone(),
                    });
                }
                Expr::Symbol(symbol) => {
                    expr = *self.definitions.get(symbol)?;
                }
                _ => return None,
            }
        }
    }

    /// Resolves a direct symbol expression through SSA copy definitions.
    fn resolve_symbol_expression(&self, expression: &Expr) -> Option<SymbolId> {
        let Expr::Symbol(symbol) = expression else {
            return None;
        };
        self.resolve_symbol(*symbol)
    }

    /// Resolves one symbol through direct SSA copy definitions.
    fn resolve_symbol(&self, mut symbol: SymbolId) -> Option<SymbolId> {
        loop {
            match self.definitions.get(&symbol).copied() {
                Some(Expr::Symbol(source)) => symbol = *source,
                _ => return Some(symbol),
            }
        }
    }
}

/// Truthiness facts that hold on every incoming edge of each CFG block.
struct IncomingTruthiness {
    /// Must-facts indexed by dense CFG block index.
    by_block: Vec<HashMap<SymbolId, Truthiness>>,
}

impl IncomingTruthiness {
    /// Computes the intersection of truthiness facts on every incoming edge.
    fn analyze(function: &LiftedFunction) -> Self {
        let blocks: Vec<_> = function.cfg.blocks().collect();
        if blocks.is_empty() {
            return Self {
                by_block: Vec::new(),
            };
        }

        let mut incoming = vec![None; blocks.len()];
        incoming[0] = Some(HashMap::new());
        let mut queue = WorkQueue::new();
        queue.push(0);

        while let Some(block_index) = queue.pop() {
            let Some(base) = &incoming[block_index] else {
                continue;
            };

            let mut outgoing = Vec::new();
            match blocks[block_index].exit() {
                BlockExit::CondJump {
                    cond,
                    then_block,
                    else_block,
                } => {
                    // TODO: Find a better way to do this, or to even represent this whole data structure.
                    //       I haven't profiled it, but cloning a HashMap sounds heavy.
                    let mut truthy = base.clone();
                    let mut falsy = base.clone();
                    if let Some((symbol, condition_truthiness)) = condition_symbol(cond) {
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
                assert!(
                    target < incoming.len(),
                    "CFG exit targeted missing block {target}"
                );
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
                if changed && !queue.contains(target) {
                    queue.push(target);
                }
            }
        }

        Self {
            by_block: incoming
                .into_iter()
                .map(Option::unwrap_or_default)
                .collect(),
        }
    }

    /// Returns facts entering `block_index`.
    fn for_block(&self, block_index: usize) -> &HashMap<SymbolId, Truthiness> {
        self.by_block
            .get(block_index)
            .expect("collector block index must exist in truthiness analysis")
    }
}

/// Collects one lifted function into proto-qualified constraints.
pub(super) fn collect(
    function: &LiftedFunction,
    functions: &[LiftedFunction],
    builtins: &BuiltinEnvironment,
    primitives: PrimitiveIds,
) -> CollectedFunction {
    let symbols = FunctionSymbolIndex::new(function);
    let provenance = SymbolProvenance::analyze(function);
    let incoming_truthiness = IncomingTruthiness::analyze(function);
    let mut output = CollectedFunction::from_function(function);
    let mut has_return = false;

    for (block_index, block) in function.cfg.blocks().enumerate() {
        let mut collector = BlockCollector::new(
            block_index,
            incoming_truthiness.for_block(block_index),
            functions,
            builtins,
            &symbols,
            &provenance,
            primitives,
            &mut output,
        );
        for statement in block.stmts() {
            collector.collect_statement(statement);
        }
        has_return |= matches!(block.exit(), BlockExit::Return(_));
        collector.collect_exit(block.exit());
    }

    if !has_return {
        let returns = output.return_pack();
        output.push_pack(
            returns,
            CollectedPackConstraint::Sequence {
                head: Vec::new(),
                tail: None,
            },
        );
    }
    output
}

/// Collects constraints from one block of a lifted SSA function.
struct BlockCollector<'a, 'cfg> {
    /// Index of the block being collected.
    block_index: usize,
    /// Truthiness facts holding on every incoming edge of this block.
    incoming_truthiness: &'a HashMap<SymbolId, Truthiness>,
    /// All lifted functions, densely indexed by proto ID.
    functions: &'a [LiftedFunction],
    /// Shared builtin environment used only for path recognition.
    builtins: &'a BuiltinEnvironment,
    /// Formal and upvalue classification for the current function.
    symbols: &'a FunctionSymbolIndex,
    /// Immutable SSA copy and field provenance.
    provenance: &'a SymbolProvenance<'cfg>,
    /// Canonical primitive IDs copied from the inference session store.
    primitives: PrimitiveIds,
    /// Proto-local constraint output and identity allocator.
    output: &'a mut CollectedFunction,
    /// Table allocations that remain under construction in this block.
    table_construction: TableConstructionTracker,
}

impl<'a, 'cfg> BlockCollector<'a, 'cfg> {
    /// Creates a collector whose mutable state cannot outlive one block.
    fn new(
        block_index: usize,
        incoming_truthiness: &'a HashMap<SymbolId, Truthiness>,
        functions: &'a [LiftedFunction],
        builtins: &'a BuiltinEnvironment,
        symbols: &'a FunctionSymbolIndex,
        provenance: &'a SymbolProvenance<'cfg>,
        primitives: PrimitiveIds,
        output: &'a mut CollectedFunction,
    ) -> Self {
        Self {
            block_index,
            incoming_truthiness,
            functions,
            builtins,
            symbols,
            provenance,
            primitives,
            output,
            table_construction: TableConstructionTracker::default(),
        }
    }

    /// Returns the block-refined occurrence slot for a symbol read when needed.
    fn symbol_read_slot(&mut self, symbol: SymbolId) -> TypeSlot {
        let Some(truthiness) = self.incoming_truthiness.get(&symbol).copied() else {
            return self.output.symbol_slot(symbol);
        };
        self.output
            .refined_symbol_slot(self.block_index, symbol, truthiness)
    }

    /// Collects one statement and its value-flow effects.
    fn collect_statement(&mut self, statement: &Stmt) {
        match statement {
            Stmt::Assign { left, value } => {
                let definite = self.initializes_active_field(left, value);
                let value_slot = self.collect_expression(value);
                self.assign_lvalue(left, value_slot, definite);
                self.update_construction_after_assignment(left, value);
            }
            Stmt::AssignMany { left, values } => {
                let pack = self.collect_value_pack(values);
                for (index, lvalue) in left.iter().enumerate() {
                    let value = self.project_pack(pack, index);
                    self.assign_lvalue(lvalue, value, false);
                }
                for value in values.iter() {
                    self.table_construction.invalidate_expression(value);
                }
                for lvalue in left {
                    self.invalidate_noninitializing_lvalue(lvalue);
                }
            }
            Stmt::SetList { table, values, .. } => {
                let pack = self.collect_value_pack(values);
                let table = self.output.symbol_slot(*table);
                self.output
                    .push(table, CollectedConstraint::SetIndexPack { values: pack });
                for value in values.iter() {
                    self.table_construction.invalidate_expression(value);
                }
            }
            Stmt::Call(call) => {
                self.collect_call(call, Some(0));
                self.table_construction.invalidate_expression(call);
            }
            Stmt::Phi(phi) => {
                let target = self.output.symbol_slot(phi.target);
                for &(_, operand) in &phi.operands {
                    let operand = self.output.symbol_slot(operand);
                    self.output.push(target, CollectedConstraint::From(operand));
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
        self.table_construction.is_active(*table)
            && !self.table_construction.expression_reads(value, *table)
    }

    /// Updates block-local construction state after one ordinary assignment.
    fn update_construction_after_assignment(&mut self, lvalue: &Expr, value: &Expr) {
        match (lvalue, value) {
            (Expr::Symbol(target), Expr::Table { .. }) => {
                self.table_construction.invalidate_expression(value);
                if !self.symbols.is_upvalue(*target) {
                    self.table_construction.start(*target);
                }
            }
            (Expr::Symbol(target), Expr::Symbol(source))
                if !self.symbols.is_upvalue(*target)
                    && self.table_construction.add_alias(*target, *source) => {}
            (Expr::GetField { obj, .. }, _) | (Expr::GetIndex { obj, .. }, _) if matches!(obj.as_ref(), Expr::Symbol(table) if self.table_construction.is_active(*table)) =>
            {
                self.table_construction.invalidate_expression(value);
                if let Expr::GetIndex { index, .. } = lvalue {
                    self.table_construction.invalidate_expression(index);
                }
            }
            _ => {
                self.table_construction.invalidate_expression(value);
                self.invalidate_noninitializing_lvalue(lvalue);
            }
        }
    }

    /// Invalidates construction values read by a non-initializing lvalue.
    fn invalidate_noninitializing_lvalue(&mut self, lvalue: &Expr) {
        match lvalue {
            Expr::GetField { obj, .. } => self.table_construction.invalidate_expression(obj),
            Expr::GetIndex { obj, index } => {
                self.table_construction.invalidate_expression(obj);
                self.table_construction.invalidate_expression(index);
            }
            _ => {}
        }
    }

    /// Collects an expression list while preserving its scalar head and multivalue tail.
    fn collect_value_pack(&mut self, values: &ValuePack) -> PackSlot {
        let head = values
            .head()
            .iter()
            .map(|value| self.collect_expression(value))
            .collect();
        let tail = values
            .tail()
            .map(|value| self.collect_expression_pack(value));
        self.sequence_pack(head, tail)
    }

    /// Collects one expression in multivalue context.
    fn collect_expression_pack(&mut self, expression: &Expr) -> PackSlot {
        match expression {
            Expr::Call { .. } | Expr::MethodCall { .. } => self.collect_call(expression, None),
            Expr::VarArgs => self.output.vararg_pack(),
            _ => {
                let value = self.collect_expression(expression);
                self.sequence_pack(vec![value], None)
            }
        }
    }

    /// Creates one pack from a fixed prefix and optional remaining pack.
    fn sequence_pack(&mut self, head: Vec<TypeSlot>, tail: Option<PackSlot>) -> PackSlot {
        let pack = self.output.synthetic_pack();
        self.output
            .push_pack(pack, CollectedPackConstraint::Sequence { head, tail });
        pack
    }

    /// Creates one scalar slot for a positional pack projection.
    fn project_pack(&mut self, pack: PackSlot, index: usize) -> TypeSlot {
        let value = self.output.synthetic_slot();
        self.output
            .push(value, CollectedConstraint::FromPack { pack, index });
        value
    }

    /// Adds assignment relations for one supported HIL lvalue.
    fn assign_lvalue(&mut self, lvalue: &Expr, value: TypeSlot, definite: bool) {
        match lvalue {
            Expr::Symbol(symbol) => {
                let target = self.output.symbol_slot(*symbol);
                if matches!(value, TypeSlot::Symbol(_, _)) {
                    self.output.push(target, CollectedConstraint::Equal(value));
                } else {
                    self.output.push(target, CollectedConstraint::From(value));
                }
            }
            Expr::GetField { obj, field } => {
                let object = self.collect_expression(obj);
                self.output.push(
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
                self.output
                    .push(object, CollectedConstraint::SetIndex { index, value });
            }
            _ => {
                // Malformed lvalues can appear only after an upstream lifting
                // defect. Keeping value flow one-way avoids manufacturing an
                // equality relation for an expression that is not storage.
                let target = self.collect_expression(lvalue);
                self.output.push(target, CollectedConstraint::From(value));
            }
        }
    }

    /// Collects one call expression and returns its complete result pack.
    fn collect_call(&mut self, expression: &Expr, return_count_hint: Option<usize>) -> PackSlot {
        let returns = self.output.synthetic_pack();
        match expression {
            Expr::Call { fun, args } => {
                if let Some(callee) = self.provenance.resolve_field_access(fun) {
                    let object = self.symbol_read_slot(callee.object);
                    let field_arguments: Vec<_> = args
                        .head()
                        .iter()
                        .enumerate()
                        .filter_map(|(index, argument)| {
                            let argument = self.provenance.resolve_field_access(argument)?;
                            (argument.object == callee.object).then_some((index, argument.field))
                        })
                        .collect();
                    if self.symbols.is_parameter(callee.object) && !field_arguments.is_empty() {
                        self.output.record_generic_field_call(GenericFieldCall {
                            parameter: callee.object,
                            callee: callee.field.clone(),
                            field_arguments,
                            return_count: return_count_hint,
                        });
                    }
                    let head = args
                        .head()
                        .iter()
                        .map(|argument| {
                            if let Some(argument) = self.provenance.resolve_field_access(argument)
                                && argument.object == callee.object
                            {
                                return CollectedCallArgument::Field(argument.field);
                            }
                            CollectedCallArgument::Value(self.collect_expression(argument))
                        })
                        .collect();
                    let tail = args
                        .tail()
                        .map(|argument| self.collect_expression_pack(argument));
                    self.output.push(
                        object,
                        CollectedConstraint::FieldCall {
                            callee: callee.field,
                            head,
                            tail,
                            returns,
                        },
                    );
                } else {
                    let callee = self.collect_expression(fun);
                    let args = self.collect_value_pack(args);
                    self.output
                        .push(callee, CollectedConstraint::Call { args, returns });
                }
            }
            Expr::MethodCall {
                object,
                method,
                args,
            } => {
                let object = self.collect_expression(object);
                let callee = self.output.synthetic_slot();
                self.output.push(
                    object,
                    CollectedConstraint::GetField {
                        field: method.clone(),
                        value: callee,
                    },
                );
                let user_args = self.collect_value_pack(args);
                let args = self.sequence_pack(vec![object], Some(user_args));
                self.output
                    .push(callee, CollectedConstraint::Call { args, returns });
            }
            _ => unreachable!("call collector requires a HIL call expression"),
        }
        returns
    }

    /// Collects one expression and returns the slot containing its value.
    ///
    /// This is intentionally recursive rather than a `Visitor`: each child must
    /// return a distinct inference slot to its parent relation.
    fn collect_expression(&mut self, expression: &Expr) -> TypeSlot {
        if let Some(path) = BuiltinPath::from_expr(expression)
            && self.builtins.get_path(&path).is_some()
        {
            let slot = self.output.synthetic_slot();
            self.output.push(slot, CollectedConstraint::Builtin(path));
            return slot;
        }

        match expression {
            Expr::Symbol(symbol) => self.symbol_read_slot(*symbol),
            Expr::Nil => {
                let slot = self.output.synthetic_slot();
                self.output
                    .push(slot, CollectedConstraint::Concrete(self.primitives.nil));
                slot
            }
            Expr::Number(_) => {
                let slot = self.output.synthetic_slot();
                self.output
                    .push(slot, CollectedConstraint::Concrete(self.primitives.number));
                slot
            }
            Expr::String(_) => {
                let slot = self.output.synthetic_slot();
                self.output
                    .push(slot, CollectedConstraint::Concrete(self.primitives.string));
                slot
            }
            Expr::Bool(_) => {
                let slot = self.output.synthetic_slot();
                self.output
                    .push(slot, CollectedConstraint::Concrete(self.primitives.boolean));
                slot
            }
            Expr::Closure { proto, captures } => {
                let slot = self.output.synthetic_slot();
                self.output.push(slot, CollectedConstraint::Closure(*proto));
                let function = self
                    .functions
                    .get(proto.0 as usize)
                    .filter(|function| function.proto == *proto)
                    .expect("closure proto must index its lifted function");
                assert_eq!(
                    captures.len(),
                    function.symbols.upvalues.len(),
                    "closure captures must match child upvalues"
                );
                for (&capture, &upvalue) in captures.iter().zip(&function.symbols.upvalues) {
                    let parent = self.output.symbol_slot(capture);
                    let child = TypeSlot::Symbol(*proto, upvalue);
                    self.output.push(parent, CollectedConstraint::Equal(child));
                }
                slot
            }
            Expr::Global(_) => self.output.synthetic_slot(),
            Expr::VarArgs => {
                let pack = self.output.vararg_pack();
                self.project_pack(pack, 0)
            }
            Expr::Table { items } => {
                let table = self.output.synthetic_slot();
                let key = self.output.table_key();
                self.output.push(table, CollectedConstraint::NewTable(key));
                for item in items {
                    match item {
                        TableItem::List(values) => {
                            let values = self.collect_value_pack(values);
                            self.output
                                .push(table, CollectedConstraint::SetIndexPack { values });
                        }
                        TableItem::Index(Expr::String(field), value) => {
                            let value = self.collect_expression(value);
                            self.output.push(
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
                            self.output
                                .push(table, CollectedConstraint::SetIndex { index, value });
                        }
                    }
                }
                table
            }
            Expr::Call { .. } | Expr::MethodCall { .. } => {
                let results = self.collect_call(expression, Some(1));
                self.project_pack(results, 0)
            }
            Expr::Binary { lhs, op, rhs } => {
                let lhs = self.collect_expression(lhs);
                let rhs = self.collect_expression(rhs);
                let result = self.output.synthetic_slot();
                self.output.push(
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
                let result = self.output.synthetic_slot();
                self.output
                    .push(operand, CollectedConstraint::Unary { op: *op, result });
                result
            }
            Expr::GetField { obj, field } => {
                let object = self.collect_expression(obj);
                let value = self.output.synthetic_slot();
                self.output.push(
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
                let value = self.output.synthetic_slot();
                self.output
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
                let result = self.output.synthetic_slot();
                self.output
                    .push(result, CollectedConstraint::From(then_value));
                self.output
                    .push(result, CollectedConstraint::From(else_value));
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
                let values = self.collect_value_pack(values);
                let returns = self.output.return_pack();
                self.output.push_pack(
                    returns,
                    CollectedPackConstraint::Sequence {
                        head: Vec::new(),
                        tail: Some(values),
                    },
                );
            }
            BlockExit::FornPrep {
                var,
                start,
                end,
                step,
                ..
            } => {
                let variable = self.output.symbol_slot(*var);
                self.output.push(
                    variable,
                    CollectedConstraint::Concrete(self.primitives.number),
                );
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
                    self.output.symbol_slot(*variable);
                }
            }
            BlockExit::FornLoop { .. } | BlockExit::Jump(_) | BlockExit::Fallthrough(_) => {}
        }
    }
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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use id_arena::Arena;

    use super::{Expr, SymbolProvenance};
    use crate::hil::lifter::ssa::Symbol;

    /// A direct SSA definition provides stable field provenance.
    #[test]
    fn symbol_provenance_resolves_direct_definition() {
        let mut arena: Arena<Symbol> = Arena::new();
        let receiver = arena.alloc(Symbol::param(0));
        let alias = arena.alloc(Symbol::reg(0));
        let field = Expr::GetField {
            obj: Box::new(Expr::Symbol(receiver)),
            field: "value".into(),
        };
        let mut provenance = SymbolProvenance {
            definitions: HashMap::new(),
        };

        provenance.insert(alias, &field);
        let resolved = provenance
            .resolve_field_access(&Expr::Symbol(alias))
            .expect("direct field definition should resolve");
        assert_eq!(resolved.object, receiver);
        assert_eq!(resolved.field, "value");
    }
}
