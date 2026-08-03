//! Lowering from lifted SSA HIL to immutable inference relations.

use std::collections::{HashMap, HashSet, VecDeque};

use super::captures::{CaptureResolver, StorageMutability};
use super::keys::{ObjectKey, PackKey, ValueKey};
use super::program::{InferenceProgram, PackRelation, ValueRelation};
use crate::hil::cflow::cfg::{Block, BlockExit, ControlFlowGraph};
use crate::hil::cflow::graph::GraphView as _;
use crate::hil::ir::{Capture, Expr, Stmt, TableItem, ValuePack};
use crate::hil::lifted::LiftedFunction;
use crate::hil::lifter::ssa::SymbolId;
use crate::hil::ty::builtins::{BuiltinEnvironment, BuiltinPath};
use crate::hil::ty::canonical::{PrimitiveIds, TypeId};
use crate::hil::ty::inference::keys::BranchPredicate;
use crate::hil::visitor::{Visitor, walk_block_exit, walk_expr};

/// Lowers all lifted functions into one whole-program relation graph.
pub fn lower_functions(
    functions: &[LiftedFunction],
    builtins: &BuiltinEnvironment,
    primitives: &PrimitiveIds,
) -> InferenceProgram {
    let mut program = InferenceProgram::default();
    let captures = CaptureResolver::new(functions);
    for function in functions {
        FunctionLowerer::new(
            function,
            functions,
            &captures,
            builtins,
            primitives,
            &mut program,
        )
        .lower();
    }
    program
}

/// Proto-local allocator and relation writer.
struct FunctionLowerer<'a> {
    function: &'a LiftedFunction,
    functions: &'a [LiftedFunction],
    builtins: &'a BuiltinEnvironment,
    primitives: &'a PrimitiveIds,
    program: &'a mut InferenceProgram,

    branch_facts: BranchFacts,
    next_value: u32,
    next_pack: u32,
    next_object: u32,
    has_return: bool,
}

impl<'a> FunctionLowerer<'a> {
    fn new(
        function: &'a LiftedFunction,
        functions: &'a [LiftedFunction],
        captures: &'a CaptureResolver,
        builtins: &'a BuiltinEnvironment,
        primitives: &'a PrimitiveIds,
        program: &'a mut InferenceProgram,
    ) -> Self {
        Self {
            function,
            functions,
            builtins,
            primitives,
            program,
            branch_facts: BranchFacts::analyze(function, captures),
            next_value: 0,
            next_pack: 0,
            next_object: 0,
            has_return: false,
        }
    }

    /// Lowers one function body into the shared program.
    fn lower(mut self) {
        self.program.touch_pack(self.return_pack());
        if self.function.is_vararg {
            self.program.touch_pack(self.vararg_pack());
        }
        for parameter in self.function.symbols.params() {
            self.program.touch_value(self.symbol_value(*parameter));
        }
        for upvalue in self.function.symbols.upvalues() {
            self.program.touch_value(self.symbol_value(*upvalue));
        }
        for (first, version) in self.function.symbols.same_storage_links() {
            let first = self.symbol_value(first);
            self.program.push_value(
                first,
                ValueRelation::SameStorage(self.symbol_value(version)),
            );
        }

        for i in 0..self.function.cfg.len() {
            if !self.branch_facts.is_reachable(i) {
                continue;
            }

            let state = self.branch_facts.incoming(i).clone();
            BlockLowerer {
                flw: &mut self,
                block: i,
                state,
            }
            .lower();
        }

        // TODO: This seems too defensive? No return pack = no return. Only a case for genuinely infinite loop functions.
        if !self.has_return {
            self.program.push_pack(
                self.return_pack(),
                PackRelation::Sequence {
                    head: Vec::new(),
                    tail: None,
                },
            );
        }
    }

    /// Returns the key for a symbol in the current proto.
    fn symbol_value(&self, symbol: SymbolId) -> ValueKey {
        ValueKey::Symbol(self.function.proto, symbol)
    }

    /// Allocates a temporary scalar value.
    fn temp_value(&mut self) -> ValueKey {
        let value = ValueKey::Temp(self.function.proto, self.next_value);
        self.next_value = self
            .next_value
            .checked_add(1)
            .expect("one proto exhausted temporary value IDs");
        self.program.touch_value(value);
        value
    }

    /// Allocates a temporary pack.
    fn temp_pack(&mut self) -> PackKey {
        let pack = PackKey::Temp(self.function.proto, self.next_pack);
        self.next_pack = self
            .next_pack
            .checked_add(1)
            .expect("one proto exhausted temporary pack IDs");
        self.program.touch_pack(pack);
        pack
    }

    /// Allocates a table object key.
    fn object_key(&mut self) -> ObjectKey {
        let key = ObjectKey {
            proto: self.function.proto,
            index: self.next_object,
        };
        self.next_object = self
            .next_object
            .checked_add(1)
            .expect("one proto exhausted object keys");
        key
    }

    /// Returns the current function's vararg pack.
    fn vararg_pack(&self) -> PackKey {
        PackKey::VarArgs(self.function.proto)
    }

    /// Returns the current function's return pack.
    fn return_pack(&self) -> PackKey {
        PackKey::Returns(self.function.proto)
    }

    /// Creates a scalar projection from one pack.
    fn project_pack(&mut self, pack: PackKey, index: usize) -> ValueKey {
        let value = self.temp_value();
        self.program
            .push_value(value, ValueRelation::FromPack { pack, index });
        value
    }

    /// Creates a temporary that produces one known type.
    fn produced_temp(&mut self, ty: TypeId) -> ValueKey {
        let value = self.temp_value();
        self.program.push_value(value, ValueRelation::Produce(ty));
        value
    }
}

/// Block-local allocator and relation writer.
struct BlockLowerer<'a, 'f> {
    flw: &'a mut FunctionLowerer<'f>,
    block: usize,
    /// Branch facts at the current point in the block.
    state: BlockState,
}

impl BlockLowerer<'_, '_> {
    fn lower(mut self) {
        let block = self.flw.function.cfg.get(self.block);
        for stmt in block.stmts() {
            self.lower_statement(stmt);
        }
        self.lower_exit(block.exit());
    }

    /// Lowers one statement.
    fn lower_statement(&mut self, statement: &Stmt) {
        match statement {
            Stmt::Assign { left, value } => {
                let value = self.lower_expr(value);
                self.assign_lvalue(left, value);
            }
            Stmt::AssignMany { left, values } => {
                let values = self.lower_value_pack(values);
                for (index, lvalue) in left.iter().enumerate() {
                    let value = self.flw.project_pack(values, index);
                    self.assign_lvalue(lvalue, value);
                }
            }
            Stmt::SetList { table, values, .. } => {
                let object = self.flw.symbol_value(*table);
                let values = self.lower_value_pack(values);
                let aggregate = self.flw.temp_value();
                self.flw
                    .program
                    .push_value(aggregate, ValueRelation::FromPackValues { pack: values });
                let index = self.flw.temp_value();
                self.flw
                    .program
                    .push_value(index, ValueRelation::Produce(self.flw.primitives.number));
                self.flw.program.push_value(
                    object,
                    ValueRelation::WriteIndex {
                        index,
                        value: aggregate,
                    },
                );
            }
            Stmt::Call(call) => {
                self.lower_call(call);
            }
            Stmt::Phi(phi) => {
                let target = self.flw.symbol_value(phi.target);
                for (_, operand) in &phi.operands {
                    let operand = self.flw.symbol_value(*operand);
                    self.flw
                        .program
                        .push_value(target, ValueRelation::FlowFrom(operand));
                }
            }
        }
    }

    /// Assigns a lowered value to one lvalue expression.
    fn assign_lvalue(&mut self, lvalue: &Expr, value: ValueKey) {
        match lvalue {
            Expr::Symbol(symbol) => {
                let target = self.flw.symbol_value(*symbol);
                if matches!(value, ValueKey::Symbol(_, _)) {
                    self.flw
                        .program
                        .push_value(target, ValueRelation::SameAs(value));
                } else {
                    self.flw
                        .program
                        .push_value(target, ValueRelation::FlowFrom(value));
                }
            }
            Expr::GetField { obj, field } => {
                let object = self.lower_expr(obj);
                self.flw.program.push_value(
                    object,
                    ValueRelation::WriteField {
                        field: field.clone(),
                        value,
                        definite: false,
                    },
                );
            }
            Expr::GetIndex { obj, index } => {
                let object = self.lower_expr(obj);
                let index = self.lower_expr(index);
                self.flw
                    .program
                    .push_value(object, ValueRelation::WriteIndex { index, value });
            }
            _ => {
                let target = self.lower_expr(lvalue);
                self.flw
                    .program
                    .push_value(target, ValueRelation::FlowFrom(value));
            }
        }
    }

    /// Lowers one expression list.
    fn lower_value_pack(&mut self, values: &ValuePack) -> PackKey {
        let head = values
            .head()
            .iter()
            .map(|value| self.lower_expr(value))
            .collect();
        let tail = values.tail().map(|value| self.lower_expr_pack(value));
        let pack = self.flw.temp_pack();
        self.flw
            .program
            .push_pack(pack, PackRelation::Sequence { head, tail });
        pack
    }

    /// Lowers one expression in multivalue context.
    fn lower_expr_pack(&mut self, expression: &Expr) -> PackKey {
        match expression {
            Expr::Call { .. } | Expr::MethodCall { .. } => self.lower_call(expression),
            Expr::VarArgs => self.flw.vararg_pack(),
            _ => {
                let value = self.lower_expr(expression);
                let pack = self.flw.temp_pack();
                self.flw.program.push_pack(
                    pack,
                    PackRelation::Sequence {
                        head: vec![value],
                        tail: None,
                    },
                );
                pack
            }
        }
    }

    /// Lowers one call expression and returns its result pack.
    fn lower_call(&mut self, expression: &Expr) -> PackKey {
        let returns = self.flw.temp_pack();
        match expression {
            Expr::Call { fun, args } => {
                let callee = self.lower_expr(fun);
                let args = self.lower_value_pack(args);
                self.flw
                    .program
                    .push_value(callee, ValueRelation::Call { args, returns });
            }
            Expr::MethodCall {
                object,
                method,
                args,
            } => {
                let object = self.lower_expr(object);
                let callee = self.flw.temp_value();
                self.flw.program.push_value(
                    object,
                    ValueRelation::ReadField {
                        field: method.clone(),
                        output: callee,
                    },
                );
                let user_args = self.lower_value_pack(args);
                let args = self.flw.temp_pack();
                self.flw.program.push_pack(
                    args,
                    PackRelation::Sequence {
                        head: vec![object],
                        tail: Some(user_args),
                    },
                );
                self.flw
                    .program
                    .push_value(callee, ValueRelation::Call { args, returns });
            }
            _ => unreachable!("call lowering requires a call expression"),
        }
        self.state
            .invalidate(&self.flw.branch_facts.mutable_indices);
        returns
    }

    /// Lowers one scalar expression.
    fn lower_expr(&mut self, expression: &Expr) -> ValueKey {
        if let Some(path) = BuiltinPath::from_expr(expression)
            && self.flw.builtins.get_path(&path).is_some()
        {
            let value = self.flw.temp_value();
            self.flw
                .program
                .push_value(value, ValueRelation::Builtin(path));
            return value;
        }

        match expression {
            Expr::Nil => self.flw.produced_temp(self.flw.primitives.nil),
            Expr::Number(_) => self.flw.produced_temp(self.flw.primitives.number),
            Expr::String(_) => self.flw.produced_temp(self.flw.primitives.string),
            Expr::Bool(_) => self.flw.produced_temp(self.flw.primitives.boolean),
            Expr::Symbol(sym) => match self.flw.branch_facts.predicate(&self.state, *sym) {
                Some(predicate) => {
                    let key = ValueKey::Occurrence(self.flw.function.proto, self.block, *sym);
                    self.flw.program.push_value(
                        key,
                        ValueRelation::Filter {
                            source: self.flw.symbol_value(*sym),
                            predicate,
                        },
                    );
                    key
                }
                None => self.flw.symbol_value(*sym),
            },
            Expr::Closure { proto, captures } => {
                let value = self.flw.temp_value();
                self.flw
                    .program
                    .push_value(value, ValueRelation::Closure(*proto));
                let function = self
                    .flw
                    .functions
                    .get(proto.0 as usize)
                    .filter(|function| function.proto == *proto)
                    .expect("closure proto must index its lifted function");
                assert_eq!(
                    captures.len(),
                    function.symbols.upvalues().len(),
                    "closure captures must match child upvalues"
                );
                for (&capture, &upvalue) in captures.iter().zip(function.symbols.upvalues()) {
                    let parent = match capture {
                        Capture::Value(symbol) => self.lower_expr(&Expr::Symbol(symbol)),
                        Capture::Ref(symbol) | Capture::Upvalue(symbol) => {
                            self.flw.symbol_value(symbol)
                        }
                    };
                    let child = ValueKey::Symbol(*proto, upvalue);
                    let relation = match capture {
                        Capture::Value(_) => ValueRelation::FlowFrom(parent),
                        Capture::Ref(_) | Capture::Upvalue(_) => ValueRelation::SameStorage(parent),
                    };
                    self.flw.program.push_value(child, relation);
                }
                value
            }
            Expr::Global(_) => self.flw.temp_value(),
            Expr::VarArgs => {
                let pack = self.flw.vararg_pack();
                self.flw.project_pack(pack, 0)
            }
            Expr::Table { items } => {
                let value = self.flw.temp_value();
                let object = self.flw.object_key();
                self.flw
                    .program
                    .push_value(value, ValueRelation::NewObject(object));
                for item in items {
                    match item {
                        TableItem::List(values) => {
                            let values = self.lower_value_pack(values);
                            let aggregate = self.flw.temp_value();
                            self.flw.program.push_value(
                                aggregate,
                                ValueRelation::FromPackValues { pack: values },
                            );
                            let index = self.flw.produced_temp(self.flw.primitives.number);
                            self.flw.program.push_value(
                                value,
                                ValueRelation::WriteIndex {
                                    index,
                                    value: aggregate,
                                },
                            );
                        }
                        TableItem::Index(index @ Expr::String(field), item_value) => {
                            let item_value = self.lower_expr(item_value);
                            if let Some(field) = field.as_utf8() {
                                self.flw.program.push_value(
                                    value,
                                    ValueRelation::WriteField {
                                        field: field.into(),
                                        value: item_value,
                                        definite: true,
                                    },
                                );
                            } else {
                                let index = self.lower_expr(index);
                                self.flw.program.push_value(
                                    value,
                                    ValueRelation::WriteIndex {
                                        index,
                                        value: item_value,
                                    },
                                );
                            }
                        }
                        TableItem::Index(index, item_value) => {
                            let index = self.lower_expr(index);
                            let item_value = self.lower_expr(item_value);
                            self.flw.program.push_value(
                                value,
                                ValueRelation::WriteIndex {
                                    index,
                                    value: item_value,
                                },
                            );
                        }
                    }
                }
                value
            }
            Expr::Call { .. } | Expr::MethodCall { .. } => {
                let returns = self.lower_call(expression);
                self.flw.project_pack(returns, 0)
            }
            Expr::Binary { lhs, op, rhs } => {
                let lhs = self.lower_expr(lhs);
                let rhs = self.lower_expr(rhs);
                let output = self.flw.temp_value();
                self.flw.program.push_value(
                    lhs,
                    ValueRelation::Binary {
                        op: *op,
                        rhs,
                        output,
                    },
                );
                output
            }
            Expr::Unary { op, expr } => {
                let operand = self.lower_expr(expr);
                let output = self.flw.temp_value();
                self.flw
                    .program
                    .push_value(operand, ValueRelation::Unary { op: *op, output });
                output
            }
            Expr::GetField { obj, field } => {
                let object = self.lower_expr(obj);
                let output = self.flw.temp_value();
                self.flw.program.push_value(
                    object,
                    ValueRelation::ReadField {
                        field: field.clone(),
                        output,
                    },
                );
                output
            }
            Expr::GetIndex { obj, index } => {
                let object = self.lower_expr(obj);
                let index = self.lower_expr(index);
                let output = self.flw.temp_value();
                self.flw
                    .program
                    .push_value(object, ValueRelation::ReadIndex { index, output });
                output
            }
            Expr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => {
                self.lower_expr(condition);
                let then_value = self.lower_expr(then_expr);
                let else_value = self.lower_expr(else_expr);
                let output = self.flw.temp_value();
                self.flw
                    .program
                    .push_value(output, ValueRelation::FlowFrom(then_value));
                self.flw
                    .program
                    .push_value(output, ValueRelation::FlowFrom(else_value));
                output
            }
        }
    }

    /// Lowers one CFG exit.
    fn lower_exit(&mut self, exit: &BlockExit) {
        match exit {
            BlockExit::CondJump { cond, .. } => {
                self.lower_expr(cond);
            }
            BlockExit::Return(values) => {
                self.flw.has_return = true;
                let values = self.lower_value_pack(values);
                self.flw.program.push_pack(
                    self.flw.return_pack(),
                    PackRelation::Sequence {
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
                let variable = self.flw.symbol_value(*var);
                self.flw
                    .program
                    .push_value(variable, ValueRelation::Produce(self.flw.primitives.number));
                self.lower_expr(start);
                self.lower_expr(end);
                self.lower_expr(step);
            }
            BlockExit::ForgPrep { exprs, .. } => {
                for expression in exprs {
                    self.lower_expr(expression);
                }
            }
            BlockExit::ForgLoop { vars, .. } => {
                for variable in vars {
                    self.flw
                        .program
                        .touch_value(self.flw.symbol_value(*variable));
                }
            }
            BlockExit::FornLoop { .. } | BlockExit::Jump(_) | BlockExit::Fallthrough(_) => {}
        }
    }
}
/// Contains information about symbol branch refinements for a function.
#[derive(Default)]
struct BranchFacts {
    map: SymbolMap,
    incoming: Vec<BlockState>,
    mutable_indices: Vec<usize>,
}

impl BranchFacts {
    /// Analyzes the branch facts for the given function.
    fn analyze(function: &LiftedFunction, captures: &CaptureResolver) -> Self {
        let mutable_symbols = MutableSymbolCollector::collect(function, captures);
        let map = SymbolMap::build(function, captures, &mutable_symbols);

        let mut mutable_indices: Vec<_> = mutable_symbols
            .into_iter()
            .filter_map(|symbol| map.get(symbol))
            .collect();
        mutable_indices.sort_unstable();
        mutable_indices.dedup();

        let mut facts = Self {
            incoming: vec![BlockState::Unreachable; function.cfg.len()],
            map,
            mutable_indices,
        };

        facts.incoming[function.cfg.entry()] =
            BlockState::Reachable(vec![SymbolFact::Unrefined; facts.map.len()]);
        facts.propagate_down(&function.cfg);
        facts
    }

    /// Returns whether the block is reachable.
    #[inline]
    fn is_reachable(&self, block: usize) -> bool {
        matches!(self.incoming.get(block), Some(BlockState::Reachable(_)))
    }

    /// Returns the incoming facts for one block.
    #[inline]
    fn incoming(&self, block: usize) -> &BlockState {
        &self.incoming[block]
    }

    /// Returns the branch predicate for a symbol in the current state, if one is known.
    #[inline]
    fn predicate(&self, state: &BlockState, symbol: SymbolId) -> Option<BranchPredicate> {
        let index = self.map.get(symbol)?;

        match state {
            BlockState::Unreachable => None,
            BlockState::Reachable(predicates) => match predicates[index] {
                SymbolFact::Unrefined => None,
                SymbolFact::Refined(predicate) => Some(predicate),
            },
        }
    }

    /// Iteratively propagates branch facts down the control flow graph.
    fn propagate_down(&mut self, cfg: &ControlFlowGraph) {
        let mut queue = VecDeque::from([cfg.entry()]);

        while let Some(source) = queue.pop_front() {
            let mut state = match self.incoming[source].clone() {
                BlockState::Unreachable => continue,
                state => state,
            };

            let block = cfg.get(source);
            if CallDetector::in_block(block) {
                state.invalidate(&self.mutable_indices);
            }

            match block.exit() {
                BlockExit::CondJump {
                    cond: Expr::Symbol(sym),
                    then_block,
                    else_block,
                } => {
                    let index = self.map.get(*sym).expect(
                        "symbols used in CondJump should have been propagated by SymbolMapBuilder",
                    );
                    let truthy = state.with_predicate(index, BranchPredicate::Truthy);
                    let falsy = state.with_predicate(index, BranchPredicate::Falsy);

                    if self.merge_into(*then_block, truthy) {
                        queue.push_back(*then_block);
                    }
                    if self.merge_into(*else_block, falsy) {
                        queue.push_back(*else_block);
                    }
                }
                other => {
                    for target in other.targets() {
                        if self.merge_into(target, state.clone()) {
                            queue.push_back(target);
                        }
                    }
                }
            }
        }
    }

    /// Merges a candidate block into the incoming block at the given target index, only
    /// if the facts strictly match.
    fn merge_into(&mut self, target: usize, candidate: BlockState) -> bool {
        match (&mut self.incoming[target], &candidate) {
            (BlockState::Unreachable, BlockState::Reachable(_)) => {
                self.incoming[target] = candidate;
                true
            }
            (BlockState::Reachable(existing), BlockState::Reachable(candidate)) => {
                let mut changed = false;
                for (existing, candidate) in existing.iter_mut().zip(candidate) {
                    let merged = existing.meet(*candidate);
                    changed |= *existing != merged;
                    *existing = merged;
                }
                changed
            }
            _ => false,
        }
    }
}

/// Collects symbols whose bindings can be changed by a closure call.
#[derive(Default)]
struct MutableSymbolCollector {
    /// Symbols backed by bindings that a call may change.
    symbols: HashSet<SymbolId>,
}

impl MutableSymbolCollector {
    /// Returns mutable binding symbols used by one function.
    fn collect(function: &LiftedFunction, captures: &CaptureResolver) -> HashSet<SymbolId> {
        let mut collector = Self::default();

        for slot in 0..function.symbols.upvalues().len() {
            if captures.storage(function.proto, slot) == StorageMutability::Mutable {
                collector.symbols.extend(function.symbols.for_upvalue(slot));
            }
        }
        collector
            .symbols
            .extend(function.symbols.captured_storage_symbols());
        collector.visit_graph(&function.cfg);

        collector.symbols
    }
}

impl Visitor for MutableSymbolCollector {
    /// Records a local binding captured through a reference.
    fn visit_capture(&mut self, _index: usize, capture: Capture) {
        if let Capture::Ref(symbol) = capture {
            self.symbols.insert(symbol);
        }
    }
}

/// Detects calls in one HIL node.
///
/// The branch analysis treats every call as a possible write to shared
/// storage because call targets are solved after relations are lowered.
#[derive(Default)]
struct CallDetector {
    /// Whether the visited node contains a call.
    found: bool,
}

impl CallDetector {
    /// Returns whether a block contains a call.
    fn in_block(block: &Block) -> bool {
        let mut detector = Self::default();
        detector.visit_block(block);
        detector.found
    }
}

impl Visitor for CallDetector {
    /// Records calls and continues into their arguments and callee expressions.
    fn visit_expr(&mut self, expression: &Expr) {
        if matches!(expression, Expr::Call { .. } | Expr::MethodCall { .. }) {
            self.found = true;
            return;
        }
        walk_expr(self, expression);
    }
}

struct SymbolMapBuilder<'a> {
    map: &'a mut SymbolMap,
}

impl Visitor for SymbolMapBuilder<'_> {
    fn visit_block_exit(&mut self, exit: &BlockExit) {
        if let BlockExit::CondJump { cond, .. } = exit
            && let Expr::Symbol(sym) = cond
        {
            self.map.add(*sym);
        }

        walk_block_exit(self, exit);
    }
}

/// A sparse-to-dense symbol map.
#[derive(Default)]
struct SymbolMap {
    /// Dense branch index for each canonical symbol.
    symbol_to_index: HashMap<SymbolId, usize>,
    /// Stable value aliases used to find canonical branch symbols.
    aliases: HashMap<SymbolId, SymbolId>,
    /// Canonical symbols in dense index order.
    symbols: Vec<SymbolId>,
}

impl SymbolMap {
    /// Builds branch symbols and aliases for read-only upvalue bindings.
    fn build(
        function: &LiftedFunction,
        captures: &CaptureResolver,
        mutable_symbols: &HashSet<SymbolId>,
    ) -> Self {
        let mut map = Self::default();
        for slot in 0..function.symbols.upvalues().len() {
            if captures.storage(function.proto, slot) == StorageMutability::ReadOnly {
                map.alias_group(function.symbols.for_upvalue(slot));
            }
        }
        // Upvalue reads become direct assignments to fresh register symbols.
        // Stable copies must use one branch key across those reads.
        for block in function.cfg.blocks() {
            for statement in block.stmts() {
                let Stmt::Assign {
                    left: Expr::Symbol(target),
                    value: Expr::Symbol(source),
                } = statement
                else {
                    continue;
                };
                if !mutable_symbols.contains(target) && !mutable_symbols.contains(source) {
                    map.alias(*target, *source);
                }
            }
        }
        SymbolMapBuilder { map: &mut map }.visit_graph(&function.cfg);
        map
    }

    /// Gives every symbol in one read-only binding the same branch key.
    fn alias_group<I>(&mut self, symbols: I)
    where
        I: IntoIterator<Item = SymbolId>,
    {
        let mut symbols = symbols.into_iter();
        let Some(first) = symbols.next() else {
            return;
        };
        for symbol in std::iter::once(first).chain(symbols) {
            self.alias(symbol, first);
        }
    }

    /// Records that `target` contains the same stable value as `source`.
    fn alias(&mut self, target: SymbolId, source: SymbolId) {
        self.aliases.insert(target, source);
    }

    /// Returns the branch key for one symbol.
    fn canonical(&self, mut symbol: SymbolId) -> SymbolId {
        let mut remaining = self.aliases.len();
        while let Some(&source) = self.aliases.get(&symbol) {
            if source == symbol {
                return symbol;
            }
            assert!(remaining > 0, "branch symbol aliases must not form a cycle");
            remaining -= 1;
            symbol = source;
        }
        symbol
    }

    /// Adds a symbol to the map, if it is not already present. Returns the dense index of the symbol.
    #[inline]
    fn add(&mut self, symbol: SymbolId) -> usize {
        let symbol = self.canonical(symbol);
        *self.symbol_to_index.entry(symbol).or_insert_with(|| {
            let index = self.symbols.len();
            self.symbols.push(symbol);
            index
        })
    }

    /// Returns the dense index of the symbol, if it is present in the map.
    #[inline]
    fn get(&self, symbol: SymbolId) -> Option<usize> {
        self.symbol_to_index.get(&self.canonical(symbol)).copied()
    }

    /// Returns the length of the symbol map.
    #[inline]
    fn len(&self) -> usize {
        self.symbols.len()
    }
}

/// Represents the refinement state of a block in the control flow graph.
#[derive(Default, Clone)]
enum BlockState {
    /// The block is not reachable.
    #[default]
    Unreachable,
    /// The block is reachable. Contains a dense map from symbol IDs to their branch predicates.
    /// None means the symbol is not refined on this edge.
    Reachable(Vec<SymbolFact>),
}

impl BlockState {
    /// Removes branch facts for mutable storage after a possible call.
    fn invalidate(&mut self, mutable_indices: &[usize]) {
        let BlockState::Reachable(predicates) = self else {
            return;
        };
        for &index in mutable_indices {
            predicates[index] = SymbolFact::Unrefined;
        }
    }

    /// Returns a new `BlockState` with the given state vector.
    #[inline]
    fn with_predicate(&self, symbol: usize, predicate: BranchPredicate) -> Self {
        match self {
            BlockState::Unreachable => BlockState::Unreachable,
            BlockState::Reachable(state) => match state[symbol].refine(predicate) {
                Ok(fact) => {
                    let mut state = state.clone();
                    state[symbol] = fact;
                    BlockState::Reachable(state)
                }
                Err(Contradiction) => BlockState::Unreachable,
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SymbolFact {
    Unrefined,
    Refined(BranchPredicate),
}

struct Contradiction;

impl SymbolFact {
    /// Applies another predicate along the same execution path.
    fn refine(self, predicate: BranchPredicate) -> Result<Self, Contradiction> {
        match self {
            Self::Unrefined => Ok(Self::Refined(predicate)),
            Self::Refined(existing) if existing == predicate => Ok(self),
            Self::Refined(_) => Err(Contradiction),
        }
    }

    /// Retains facts guaranteed by both incoming paths.
    fn meet(self, other: Self) -> Self {
        if self == other { self } else { Self::Unrefined }
    }
}
