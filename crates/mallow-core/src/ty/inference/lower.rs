//! Lowering from FIR to immutable inference constraints.

use std::collections::{HashMap, HashSet, VecDeque};

use super::TypeStore;
use super::keys::{BranchPredicate, ObjectKey, PackKey, ValueKey};
use super::program::{Constraint, InferenceProgram};
use crate::il::ProtoId;
use crate::ir::Unit;
use crate::ir::fir::analysis::TableConstructorWrites;
use crate::ir::fir::{
    BlockExit, Capture, CellId, Constant, Edge, Function, Instr, Number, PackId, ValueId,
};
use crate::ir::graph::GraphView as _;
use crate::operator::BinOp;
use crate::ty::canonical::{TypeId, TypeLiteral};

/// Lowers all FIR functions into one whole-program constraint set.
pub fn lower_functions(unit: &Unit<Function>, store: &mut TypeStore) -> InferenceProgram {
    let cell_facts = CellFacts::analyze(unit);
    let mut program = InferenceProgram::default();
    for function in unit.functions() {
        FunctionLowerer::new(function, unit, &cell_facts, store, &mut program).lower();
    }
    program
}

/// Coordinates FIR traversal and constraint writing for a function.
struct FunctionLowerer<'u, 's, 'p> {
    /// Immutable FIR source.
    source: FunctionSource<'u>,
    /// Facts known at each block entry.
    branch_facts: BranchFacts,
    /// Writes that initialize fresh table allocations.
    table_constructor_writes: TableConstructorWrites,
    /// Mutable constraint writer.
    writer: ConstraintWriter<'s, 'p>,
}

impl<'u, 's, 'p> FunctionLowerer<'u, 's, 'p> {
    /// Creates a lowerer for a function.
    fn new(
        function: &'u Function,
        unit: &'u Unit<Function>,
        cell_facts: &CellFacts,
        store: &'s mut TypeStore,
        program: &'p mut InferenceProgram,
    ) -> Self {
        Self {
            source: FunctionSource { function, unit },
            branch_facts: BranchFacts::analyze(function, cell_facts),
            table_constructor_writes: TableConstructorWrites::analyze(function),
            writer: ConstraintWriter {
                store,
                program,
                next_value: 0,
                next_pack: 0,
            },
        }
    }

    /// Lowers the complete function.
    fn lower(self) {
        let Self {
            source,
            branch_facts,
            table_constructor_writes,
            mut writer,
        } = self;

        writer.touch_owned_keys(source);
        writer.lower_entry(source);

        for block_index in source.function.cfg.nodes() {
            if !branch_facts.is_reachable(block_index) {
                continue;
            }

            let state = branch_facts.incoming(block_index);
            let block = &source.function.cfg[block_index];
            for (instruction_index, instruction) in block.instrs.iter().enumerate() {
                writer.lower_instruction(
                    source,
                    block_index,
                    instruction_index,
                    state,
                    &table_constructor_writes,
                    instruction,
                );
            }
            writer.lower_exit(
                source,
                block_index,
                state,
                branch_facts.aliases(),
                &block.exit,
            );
        }
    }
}

/// Immutable FIR data used while lowering a function.
#[derive(Clone, Copy)]
struct FunctionSource<'u> {
    /// Function being lowered.
    function: &'u Function,
    /// Unit containing the function and its children.
    unit: &'u Unit<Function>,
}

impl FunctionSource<'_> {
    /// Returns the function identity.
    fn id(self) -> ProtoId {
        self.function.id
    }

    /// Returns a scalar key owned by this function.
    fn value_key(self, value: ValueId) -> ValueKey {
        ValueKey::Value(self.id(), value)
    }

    /// Returns a pack key owned by this function.
    fn pack_key(self, pack: PackId) -> PackKey {
        PackKey::Pack(self.id(), pack)
    }

    /// Returns a cell key owned by this function.
    fn cell_key(self, cell: CellId) -> ValueKey {
        ValueKey::Cell(self.id(), cell)
    }
}

/// Mutable state used to write inference constraints.
struct ConstraintWriter<'s, 'p> {
    /// Canonical types shared by this inference run.
    store: &'s mut TypeStore,
    /// Whole-program constraint set being built.
    program: &'p mut InferenceProgram,
    /// Next scalar identity for a fused FIR operation.
    next_value: u32,
    /// Next pack identity for a fused FIR operation.
    next_pack: u32,
}

impl ConstraintWriter<'_, '_> {
    /// Creates keys for all FIR-owned identities and function interface packs.
    fn touch_owned_keys(&mut self, src: FunctionSource<'_>) {
        for (value, _) in src.function.values.iter() {
            self.program.touch_value(src.value_key(value));
        }
        for (pack, _) in src.function.packs.iter() {
            self.program.touch_pack(src.pack_key(pack));
        }
        for (cell, _) in src.function.cells.iter() {
            self.program.touch_value(src.cell_key(cell));
        }

        self.program.touch_pack(PackKey::Returns(src.id()));
        if src.function.is_vararg {
            self.program.touch_pack(PackKey::VarArgs(src.id()));
        }
    }

    /// Connects entry-edge arguments to the FIR entry block parameters.
    fn lower_entry(&mut self, src: FunctionSource<'_>) {
        let target = &src.function.cfg[src.function.entry.target];
        for (&source, &target) in src.function.entry.params.iter().zip(&target.params) {
            self.program.push(Constraint::Flow {
                source: src.value_key(source),
                target: src.value_key(target),
            });
        }
    }

    /// Lowers a flat FIR instruction.
    fn lower_instruction(
        &mut self,
        src: FunctionSource<'_>,
        block: usize,
        instruction_index: usize,
        state: &BlockState,
        table_constructor_writes: &TableConstructorWrites,
        instruction: &Instr,
    ) {
        match instruction {
            Instr::Const { out, value } => {
                let ty = self.constant_type(value);
                self.program.push(Constraint::Produce {
                    value: src.value_key(*out),
                    ty,
                });
            }
            Instr::Copy { out, value } => {
                let source = self.used_value(src, block, state, *value);
                self.program.push(Constraint::Flow {
                    source,
                    target: src.value_key(*out),
                });
            }
            Instr::Closure {
                out,
                proto,
                captures,
            } => self.lower_closure(src, block, state, *out, *proto, captures),
            Instr::GetTable { out, table, key } => {
                let table = self.used_value(src, block, state, *table);
                let key = self.used_value(src, block, state, *key);
                self.program.push(Constraint::GetTable {
                    table,
                    key,
                    output: src.value_key(*out),
                });
            }
            Instr::SetTable { table, key, value } => {
                let table = self.used_value(src, block, state, *table);
                let key = self.used_value(src, block, state, *key);
                let value = self.used_value(src, block, state, *value);
                let constraint = if table_constructor_writes.contains(block, instruction_index) {
                    Constraint::InitTable { table, key, value }
                } else {
                    Constraint::SetTable { table, key, value }
                };
                self.program.push(constraint);
            }
            Instr::GetGlobal { out, name } => {
                let global = ValueKey::Global(name.clone());
                if let Some(ty) = self.store.builtin(name) {
                    self.program.push(Constraint::Produce {
                        value: global.clone(),
                        ty,
                    });
                }
                self.program.push(Constraint::Flow {
                    source: global,
                    target: src.value_key(*out),
                });
            }
            Instr::SetGlobal { name, value } => {
                let value = self.used_value(src, block, state, *value);
                self.program.push(Constraint::Flow {
                    source: value,
                    target: ValueKey::Global(name.clone()),
                });
            }
            Instr::Binary { out, lhs, op, rhs } => {
                let lhs = self.used_value(src, block, state, *lhs);
                let rhs = self.used_value(src, block, state, *rhs);
                self.program.push(Constraint::Binary {
                    lhs,
                    op: *op,
                    rhs,
                    output: src.value_key(*out),
                });
            }
            Instr::Unary { out, op, value } => {
                let value = self.used_value(src, block, state, *value);
                self.program.push(Constraint::Unary {
                    operand: value,
                    op: *op,
                    output: src.value_key(*out),
                });
            }
            Instr::Concat { out, operands } => {
                self.lower_concat(src, block, state, *out, operands);
            }
            Instr::Select {
                out,
                condition,
                then_value,
                else_value,
            } => {
                let _ = self.used_value(src, block, state, *condition);
                let then_value = self.used_value(src, block, state, *then_value);
                let else_value = self.used_value(src, block, state, *else_value);
                let output = src.value_key(*out);
                self.program.push(Constraint::Flow {
                    source: then_value,
                    target: output.clone(),
                });
                self.program.push(Constraint::Flow {
                    source: else_value,
                    target: output,
                });
            }
            Instr::NewTable { out } => {
                self.program.push(Constraint::IncludeObject {
                    value: src.value_key(*out),
                    object: ObjectKey {
                        proto: src.id(),
                        value: *out,
                    },
                });
            }
            Instr::MakePack { out, head, tail } => {
                let head = head
                    .iter()
                    .map(|value| self.used_value(src, block, state, *value))
                    .collect();
                self.program.push(Constraint::Sequence {
                    pack: src.pack_key(*out),
                    head,
                    tail: tail.map(|pack| src.pack_key(pack)),
                });
            }
            Instr::Project { out, pack, index } => {
                self.program.push(Constraint::ProjectPack {
                    pack: src.pack_key(*pack),
                    index: *index,
                    output: src.value_key(*out),
                });
            }
            Instr::Call {
                out,
                function,
                args,
            } => {
                let function = self.used_value(src, block, state, *function);
                self.program.push(Constraint::Call {
                    callee: function,
                    args: src.pack_key(*args),
                    returns: src.pack_key(*out),
                });
            }
            Instr::MethodCall {
                out,
                object,
                method,
                args,
            } => {
                let object = self.used_value(src, block, state, *object);
                let key = self.fresh_value(src.id());
                let key_type = self
                    .store
                    .literal(TypeLiteral::String(method.clone().into()));
                self.program.push(Constraint::Produce {
                    value: key.clone(),
                    ty: key_type,
                });

                let callee = self.fresh_value(src.id());
                self.program.push(Constraint::GetTable {
                    table: object.clone(),
                    key,
                    output: callee.clone(),
                });

                let call_args = self.fresh_pack(src.id());
                self.program.push(Constraint::Sequence {
                    pack: call_args,
                    head: vec![object],
                    tail: Some(src.pack_key(*args)),
                });
                self.program.push(Constraint::Call {
                    callee,
                    args: call_args,
                    returns: src.pack_key(*out),
                });
            }
            Instr::VarArgs { out } => {
                assert!(
                    src.function.is_vararg,
                    "non-variadic function must not read variadic arguments"
                );
                self.program.push(Constraint::Sequence {
                    pack: src.pack_key(*out),
                    head: Vec::new(),
                    tail: Some(PackKey::VarArgs(src.id())),
                });
            }
            Instr::OpenCell { cell, value } | Instr::StoreCell { cell, value } => {
                let value = self.used_value(src, block, state, *value);
                self.program.push(Constraint::Flow {
                    source: value,
                    target: src.cell_key(*cell),
                });
            }
            Instr::LoadCell { out, cell } => {
                self.program.push(Constraint::Flow {
                    source: src.cell_key(*cell),
                    target: src.value_key(*out),
                });
            }
            Instr::SetList {
                table,
                index: _,
                values,
            } => {
                let table = self.used_value(src, block, state, *table);
                self.program.push(Constraint::WriteList {
                    table,
                    values: src.pack_key(*values),
                });
            }
        }
    }

    /// Lowers closure identity and its explicit FIR captures.
    fn lower_closure(
        &mut self,
        src: FunctionSource<'_>,
        block: usize,
        state: &BlockState,
        out: ValueId,
        proto: ProtoId,
        captures: &[Capture],
    ) {
        self.program.push(Constraint::IncludeClosure {
            value: src.value_key(out),
            proto,
        });

        let child = &src.unit[proto];

        for (&capture, &upvalue) in captures.iter().zip(&child.upvalues) {
            let target = ValueKey::Cell(proto, upvalue);
            match capture {
                Capture::Copy(value) => {
                    let source = self.used_value(src, block, state, value);
                    self.program.push(Constraint::Flow { source, target });
                }
                Capture::Share(cell) => {
                    let source = src.cell_key(cell);
                    self.program.push(Constraint::Flow {
                        source: source.clone(),
                        target: target.clone(),
                    });
                    self.program.push(Constraint::Flow {
                        source: target,
                        target: source,
                    });
                }
            }
        }
    }

    /// Lowers an FIR concat as its right-associative binary operations.
    fn lower_concat(
        &mut self,
        src: FunctionSource<'_>,
        block: usize,
        state: &BlockState,
        out: ValueId,
        operands: &[ValueId],
    ) {
        // Lifter ensures there are at least two operands.
        let mut rhs = self.used_value(src, block, state, operands[operands.len() - 1]);
        for index in (0..operands.len() - 1).rev() {
            let lhs = self.used_value(src, block, state, operands[index]);
            let output = if index == 0 {
                src.value_key(out)
            } else {
                self.fresh_value(src.id())
            };
            self.program.push(Constraint::Binary {
                lhs,
                op: BinOp::Concat,
                rhs,
                output: output.clone(),
            });
            rhs = output;
        }
    }

    /// Lowers constraints and edges carried by a block exit.
    fn lower_exit(
        &mut self,
        src: FunctionSource<'_>,
        block: usize,
        state: &BlockState,
        aliases: &ValueAliases,
        exit: &BlockExit,
    ) {
        match exit {
            BlockExit::Fallthrough(edge) | BlockExit::Jump(edge) => {
                self.lower_edge(src, state, edge);
            }
            BlockExit::Branch {
                condition,
                then_edge,
                else_edge,
            } => {
                let _ = self.used_value(src, block, state, *condition);
                let then_state = state.with_predicate(*condition, BranchPredicate::Truthy, aliases);
                let else_state = state.with_predicate(*condition, BranchPredicate::Falsy, aliases);
                self.lower_edge(src, &then_state, then_edge);
                self.lower_edge(src, &else_state, else_edge);
            }
            BlockExit::NumericFor {
                body_edge,
                exit_edge,
                variable,
                start,
                end,
                step,
            } => {
                let number = self.store.primitives().number;
                self.program.push(Constraint::Produce {
                    value: src.value_key(*variable),
                    ty: number,
                });
                for value in [*start, *end, *step] {
                    let value = self.used_value(src, block, state, value);
                    self.program.push(Constraint::Require { value, ty: number });
                }
                self.lower_edge(src, state, body_edge);
                self.lower_edge(src, state, exit_edge);
            }
            BlockExit::NumericForLoop {
                body_edge,
                exit_edge,
            }
            | BlockExit::GenericForLoop {
                body_edge,
                exit_edge,
                ..
            } => {
                self.lower_edge(src, state, body_edge);
                self.lower_edge(src, state, exit_edge);
            }
            BlockExit::GenericFor {
                body_edge,
                variables,
                values,
                ..
            } => {
                self.lower_generic_for(src, block, state, variables, *values);
                self.lower_edge(src, state, body_edge);
            }
            BlockExit::Return(values) => {
                self.program.push(Constraint::Sequence {
                    pack: PackKey::Returns(src.id()),
                    head: Vec::new(),
                    tail: Some(src.pack_key(*values)),
                });
            }
        }
    }

    /// Lowers the implicit iterator call represented by a generic-for exit.
    fn lower_generic_for(
        &mut self,
        src: FunctionSource<'_>,
        block: usize,
        state: &BlockState,
        variables: &[ValueId],
        values: [ValueId; 3],
    ) {
        let iterator = self.used_value(src, block, state, values[0]);
        let iterator_state = self.used_value(src, block, state, values[1]);
        let control = self.used_value(src, block, state, values[2]);
        let args = self.fresh_pack(src.id());
        self.program.push(Constraint::Sequence {
            pack: args,
            head: vec![iterator_state, control],
            tail: None,
        });

        let returns = self.fresh_pack(src.id());
        self.program.push(Constraint::Call {
            callee: iterator,
            args,
            returns,
        });
        for (index, &variable) in variables.iter().enumerate() {
            self.program.push(Constraint::ProjectPack {
                pack: returns,
                index,
                output: src.value_key(variable),
            });
        }
    }

    /// Connects outgoing edge arguments to the target block parameters.
    fn lower_edge(&mut self, src: FunctionSource<'_>, state: &BlockState, edge: &Edge) {
        if matches!(state, BlockState::Unreachable) {
            return;
        }

        let target = &src.function.cfg[edge.target];
        for (&source, &target) in edge.params.iter().zip(&target.params) {
            self.program.push(Constraint::Flow {
                source: src.value_key(source),
                target: src.value_key(target),
            });
        }
    }

    /// Returns the canonical type produced by a FIR constant.
    fn constant_type(&mut self, value: &Constant) -> TypeId {
        let primitives = self.store.primitives();
        match value {
            Constant::Nil => primitives.nil,
            Constant::Number(Number::Integer(_)) => primitives.integer,
            Constant::Number(Number::Float(_)) => primitives.number,
            Constant::String(value) => self.store.literal(TypeLiteral::String(value.clone())),
            Constant::Bool(value) => self.store.literal(TypeLiteral::Boolean(*value)),
        }
    }

    /// Returns the branch-refined key used at a value occurrence.
    fn used_value(
        &mut self,
        src: FunctionSource<'_>,
        block: usize,
        state: &BlockState,
        value: ValueId,
    ) -> ValueKey {
        let Some(predicate) = state.predicate(value) else {
            return src.value_key(value);
        };

        let occurrence = ValueKey::Occurrence(src.id(), block, value);
        self.program.push(Constraint::Filter {
            source: src.value_key(value),
            target: occurrence.clone(),
            predicate,
        });
        occurrence
    }

    /// Allocates a scalar key for semantics fused into an FIR operation.
    fn fresh_value(&mut self, proto: ProtoId) -> ValueKey {
        let value = ValueKey::Synthetic(proto, self.next_value);
        self.next_value += 1;
        self.program.touch_value(value.clone());
        value
    }

    /// Allocates a pack key for semantics fused into an FIR operation.
    fn fresh_pack(&mut self, proto: ProtoId) -> PackKey {
        let pack = PackKey::Synthetic(proto, self.next_pack);
        self.next_pack += 1;
        self.program.touch_pack(pack);
        pack
    }
}

/// Mutability of explicit FIR cells after shared captures are resolved.
#[derive(Default)]
struct CellFacts {
    /// Cells that can be changed after their initial value is captured.
    mutable: HashSet<ValueKey>,
}

impl CellFacts {
    /// Finds mutable storage by following only explicit shared captures.
    fn analyze(unit: &Unit<Function>) -> Self {
        let mut facts = Self::default();
        let mut shared = HashMap::<_, Vec<_>>::new();
        let mut queue = VecDeque::new();

        for function in unit.functions() {
            for block in function.cfg.nodes() {
                for instruction in &function.cfg[block].instrs {
                    match instruction {
                        Instr::StoreCell { cell, .. } => {
                            let cell = ValueKey::Cell(function.id, *cell);
                            if facts.mutable.insert(cell.clone()) {
                                queue.push_back(cell);
                            }
                        }
                        Instr::Closure {
                            proto, captures, ..
                        } => {
                            let child = &unit[*proto];
                            for (&capture, &upvalue) in captures.iter().zip(&child.upvalues) {
                                let Capture::Share(cell) = capture else {
                                    continue;
                                };
                                let parent = ValueKey::Cell(function.id, cell);
                                let child = ValueKey::Cell(*proto, upvalue);
                                shared
                                    .entry(parent.clone())
                                    .or_default()
                                    .push(child.clone());
                                shared.entry(child).or_default().push(parent);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        while let Some(cell) = queue.pop_front() {
            for shared_cell in shared.get(&cell).into_iter().flatten() {
                if facts.mutable.insert(shared_cell.clone()) {
                    queue.push_back(shared_cell.clone());
                }
            }
        }

        facts
    }

    /// Returns whether one cell can change after it is opened.
    fn is_mutable(&self, proto: ProtoId, cell: CellId) -> bool {
        self.mutable.contains(&ValueKey::Cell(proto, cell))
    }
}

/// Immutable FIR values that always carry the same runtime value.
#[derive(Default)]
struct ValueAliases {
    /// Alias source for copied values and loads from immutable cells.
    source: HashMap<ValueId, ValueId>,
}

impl ValueAliases {
    /// Finds stable copies and reads from immutable storage.
    fn analyze(function: &Function, cell_facts: &CellFacts) -> Self {
        let mut aliases = Self::default();
        let mut first_load = HashMap::new();
        for block in function.cfg.nodes() {
            for instruction in &function.cfg[block].instrs {
                match instruction {
                    Instr::Copy { out, value } => {
                        aliases.source.insert(*out, *value);
                    }
                    Instr::LoadCell { out, cell } if !cell_facts.is_mutable(function.id, *cell) => {
                        let source = *first_load.entry(*cell).or_insert(*out);
                        if source != *out {
                            aliases.source.insert(*out, source);
                        }
                    }
                    _ => {}
                }
            }
        }
        aliases
    }

    /// Returns the oldest stable identity for a value.
    fn canonical(&self, mut value: ValueId) -> ValueId {
        let mut remaining = self.source.len();
        while let Some(source) = self.source.get(&value).copied() {
            assert!(remaining > 0, "FIR value aliases must not form a cycle");
            remaining -= 1;
            value = source;
        }
        value
    }

    /// Copies canonical predicates to every equivalent value.
    fn expand(&self, predicates: &mut HashMap<ValueId, BranchPredicate>) {
        for &value in self.source.keys() {
            let canonical = self.canonical(value);
            if let Some(predicate) = predicates.get(&canonical).copied() {
                predicates.insert(value, predicate);
            }
        }
    }
}

/// Contains immutable-value branch facts at each block entry.
struct BranchFacts {
    /// Incoming facts indexed by block.
    incoming: Vec<BlockState>,
    /// Stable value aliases used by branch conditions.
    aliases: ValueAliases,
}

impl BranchFacts {
    /// Propagates branch facts through FIR edges and block parameters.
    fn analyze(function: &Function, cell_facts: &CellFacts) -> Self {
        let aliases = ValueAliases::analyze(function, cell_facts);
        let mut facts = Self {
            incoming: vec![BlockState::Unreachable; function.cfg.len()],
            aliases,
        };
        facts.incoming[function.entry.target] = BlockState::reachable();

        let mut queue = VecDeque::from([function.entry.target]);
        while let Some(source) = queue.pop_front() {
            let state = facts.incoming[source].clone();
            match &function.cfg[source].exit {
                BlockExit::Branch {
                    condition,
                    then_edge,
                    else_edge,
                } => {
                    let then_state = state
                        .with_predicate(*condition, BranchPredicate::Truthy, &facts.aliases)
                        .through_edge(function, then_edge, &facts.aliases);
                    if facts.merge_into(then_edge.target, then_state) {
                        queue.push_back(then_edge.target);
                    }

                    let else_state = state
                        .with_predicate(*condition, BranchPredicate::Falsy, &facts.aliases)
                        .through_edge(function, else_edge, &facts.aliases);
                    if facts.merge_into(else_edge.target, else_state) {
                        queue.push_back(else_edge.target);
                    }
                }
                exit => {
                    for edge in exit.edges() {
                        let candidate = state.clone().through_edge(function, edge, &facts.aliases);
                        if facts.merge_into(edge.target, candidate) {
                            queue.push_back(edge.target);
                        }
                    }
                }
            }
        }

        facts
    }

    /// Returns the stable aliases used by branch propagation.
    fn aliases(&self) -> &ValueAliases {
        &self.aliases
    }

    /// Returns whether a block can be reached.
    fn is_reachable(&self, block: usize) -> bool {
        matches!(self.incoming.get(block), Some(BlockState::Reachable(_)))
    }

    /// Returns facts known when control enters a block.
    fn incoming(&self, block: usize) -> &BlockState {
        &self.incoming[block]
    }

    /// Merges facts that hold on every known path into a block.
    fn merge_into(&mut self, target: usize, candidate: BlockState) -> bool {
        match (&mut self.incoming[target], candidate) {
            (_, BlockState::Unreachable) => false,
            (entry @ BlockState::Unreachable, candidate) => {
                *entry = candidate;
                true
            }
            (BlockState::Reachable(existing), BlockState::Reachable(candidate)) => {
                let old_len = existing.len();
                existing.retain(|value, predicate| candidate.get(value) == Some(predicate));
                existing.len() != old_len
            }
        }
    }
}

/// Facts known along a control-flow path.
#[derive(Clone)]
enum BlockState {
    /// The path cannot execute.
    Unreachable,
    /// Predicates known for immutable FIR values.
    Reachable(HashMap<ValueId, BranchPredicate>),
}

impl BlockState {
    /// Creates a reachable state with no refinements.
    fn reachable() -> Self {
        Self::Reachable(HashMap::new())
    }

    /// Returns the known predicate for a immutable value.
    fn predicate(&self, value: ValueId) -> Option<BranchPredicate> {
        match self {
            Self::Unreachable => None,
            Self::Reachable(predicates) => predicates.get(&value).copied(),
        }
    }

    /// Adds a predicate or marks a contradictory path unreachable.
    fn with_predicate(
        &self,
        value: ValueId,
        predicate: BranchPredicate,
        aliases: &ValueAliases,
    ) -> Self {
        let Self::Reachable(predicates) = self else {
            return Self::Unreachable;
        };
        let value = aliases.canonical(value);
        if predicates
            .get(&value)
            .is_some_and(|known| *known != predicate)
        {
            return Self::Unreachable;
        }

        let mut predicates = predicates.clone();
        predicates.insert(value, predicate);
        aliases.expand(&mut predicates);
        Self::Reachable(predicates)
    }

    /// Transfers known predicates to the target block parameters of an edge.
    fn through_edge(mut self, function: &Function, edge: &Edge, aliases: &ValueAliases) -> Self {
        let Self::Reachable(predicates) = &mut self else {
            return self;
        };
        let target = &function.cfg[edge.target];
        let transferred: Vec<_> = edge
            .params
            .iter()
            .zip(&target.params)
            .filter_map(|(&source, &target)| {
                predicates
                    .get(&source)
                    .copied()
                    .map(|predicate| (aliases.canonical(target), predicate))
            })
            .collect();
        for target in &target.params {
            predicates.remove(target);
            predicates.remove(&aliases.canonical(*target));
        }
        predicates.extend(transferred);
        aliases.expand(predicates);
        self
    }
}
