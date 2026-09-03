//! Queue-based fixed-point engine.

use std::collections::{HashMap, HashSet, VecDeque};

use smol_str::SmolStr;

use super::Output;
use super::keys::{BranchPredicate, PackKey, ValueKey};
use super::program::{Constraint, InferenceProgram, ProgramConstraint};
use super::world::{ObjectId, PackAlternative, PackId, ValueId, World, WorldChange};
use crate::il::ProtoId;
use crate::ir::Unit;
use crate::ir::fir::Function;
use crate::operator::{BinOp, UnOp};
use crate::ty::canonical::{Type, TypeId, TypeLiteral};
use crate::ty::store::TypeStore;

/// a installed constraint using dense world identities.
type Rule = Constraint<ValueId, PackId, ObjectId>;

/// Solves all constraints in a program to a fixed point.
pub(super) fn run(program: InferenceProgram, unit: &Unit<Function>, types: TypeStore) -> Output {
    Engine::new(program, unit, types).run()
}

/// a concrete connection installed by a dynamic rule.
///
/// A rule can say "for every object" or "for every closure" before the
/// engine knows which objects or closures exist. This set remembers each
/// connection that has already been installed, so running the rule again does
/// not install the same connection twice.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Activation {
    /// Connects a call argument to a closure parameter.
    CallParameter {
        /// Rule that owns the connection.
        rule: usize,
        /// Closure receiving the argument.
        proto: ProtoId,
        /// Zero-based parameter position.
        index: usize,
    },
    /// Connects extra call arguments to a closure vararg pack.
    CallVarArgs {
        /// Rule that owns the connection.
        rule: usize,
        /// Closure receiving the extra arguments.
        proto: ProtoId,
    },
    /// Connects a closure result to a call result.
    CallReturn {
        /// Rule that owns the connection.
        rule: usize,
        /// Closure producing the result.
        proto: ProtoId,
        /// Zero-based result position.
        index: usize,
    },
    /// Connects a table write to a concrete object.
    SetTable {
        /// Rule that owns the connection.
        rule: usize,
        /// Object receiving the write.
        object: ObjectId,
        /// Exact field, or `None` for a dynamic index.
        field: Option<SmolStr>,
    },
    /// Connects a table read to a concrete object.
    GetTable {
        /// Rule that owns the connection.
        rule: usize,
        /// Object providing the value.
        object: ObjectId,
        /// Exact field, or `None` for a dynamic index.
        field: Option<SmolStr>,
    },
}

/// Flow rule variant used for deduplication.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FlowKind {
    /// Sends all known types and identities.
    Full,
    /// Sends known types after removing `nil`.
    NonNil,
}

/// Keys currently described by a table access.
enum TableKey {
    /// A finite set of exact string fields.
    Fields(Vec<SmolStr>),
    /// A key that requires the table indexer.
    Dynamic,
}

/// Pending rule queue with duplicate suppression.
#[derive(Debug, Default)]
struct RuleQueue {
    queue: VecDeque<usize>,
    queued: HashSet<usize>,
}

impl RuleQueue {
    /// Adds a rule to the queue if it is not already pending.
    #[inline]
    fn push(&mut self, rule: usize) {
        if self.queued.insert(rule) {
            self.queue.push_back(rule);
        }
    }

    /// Removes the next pending rule.
    #[inline]
    fn pop(&mut self) -> Option<usize> {
        let rule = self.queue.pop_front()?;
        self.queued.remove(&rule);
        Some(rule)
    }

    /// Extends the queue with the given rules.
    #[inline]
    fn extend(&mut self, rules: impl IntoIterator<Item = usize>) {
        for rule in rules {
            self.push(rule);
        }
    }
}

/// Reverse dependency index from changed facts to rules.
#[derive(Debug, Default)]
struct Subscriptions {
    values: HashMap<ValueId, HashSet<usize>>,
    packs: HashMap<PackId, HashSet<usize>>,
}

impl Subscriptions {
    /// Records that `rule` must rerun when `value` changes.
    fn value(&mut self, value: ValueId, rule: usize) {
        self.values.entry(value).or_default().insert(rule);
    }

    /// Records that `rule` must rerun when `pack` shape changes.
    fn pack(&mut self, pack: PackId, rule: usize) {
        self.packs.entry(pack).or_default().insert(rule);
    }
}

/// Solver over immutable constraints and mutable domain state.
struct Engine<'u> {
    types: TypeStore,
    world: World,
    unit: &'u Unit<Function>,
    rules: Vec<Rule>,
    subscriptions: Subscriptions,
    queue: RuleQueue,
    activations: HashSet<Activation>,
    flow_rules: HashSet<(ValueId, ValueId, FlowKind)>,
    slice_rules: HashSet<(PackId, usize, PackId)>,
    write_list_rules: HashSet<(ValueId, PackId)>,
}

impl<'u> Engine<'u> {
    /// Builds an engine and installs every constraint from `program`.
    fn new(program: InferenceProgram, unit: &'u Unit<Function>, types: TypeStore) -> Self {
        let (never, unknown) = (types.primitives().never, types.primitives().unknown);
        let mut engine = Self {
            types,
            world: World::new(never, unknown),
            unit,
            rules: Vec::new(),
            subscriptions: Subscriptions::default(),
            queue: RuleQueue::default(),
            activations: HashSet::new(),
            flow_rules: HashSet::new(),
            slice_rules: HashSet::new(),
            write_list_rules: HashSet::new(),
        };
        engine.install_program(program);
        engine
    }

    /// Solves and materializes a complete inference result.
    fn run(mut self) -> Output {
        // Pack shapes must settle before return signatures request projections.
        self.solve();

        let protos: Vec<_> = self.unit.functions().map(|function| function.id).collect();
        for proto in protos {
            let returns = self.pack_for_key(PackKey::Returns(proto));
            let width = self.pack_width(returns, &mut HashSet::new());
            for index in 0..width {
                self.ensure_projection(returns, index);
            }
        }
        self.solve();

        self.materialize()
    }

    /// Applies queued constraints until no known fact changes.
    fn solve(&mut self) {
        while let Some(rule_id) = self.queue.pop() {
            let rule = self.rules[rule_id].clone();
            self.apply(rule_id, rule);
        }
    }

    /// Returns or creates the value for `key`.
    pub(super) fn value_for_key(&mut self, key: ValueKey) -> ValueId {
        self.world.value_for_key(key)
    }

    /// Returns or creates the pack for `key`.
    pub(super) fn pack_for_key(&mut self, key: PackKey) -> PackId {
        self.world.pack_for_key(key)
    }

    /// Adds a rule and subscribes it to its direct inputs.
    fn add_rule(&mut self, rule: Rule) -> usize {
        let id = self.rules.len();
        self.subscribe_rule(id, &rule);
        self.rules.push(rule);
        self.queue.push(id);
        id
    }

    /// Adds a flow rule once.
    fn add_flow_rule(&mut self, source: ValueId, target: ValueId) {
        if self.flow_rules.insert((source, target, FlowKind::Full)) {
            self.add_rule(Rule::Flow { source, target });
        }
    }

    /// Adds a non-nil flow rule once.
    fn add_non_nil_flow_rule(&mut self, source: ValueId, target: ValueId) {
        if self.flow_rules.insert((source, target, FlowKind::NonNil)) {
            self.add_rule(Rule::NonNilFlow { source, target });
        }
    }

    /// Adds a pack-slice rule once.
    fn add_slice_rule(&mut self, source: PackId, offset: usize, target: PackId) {
        if self.slice_rules.insert((source, offset, target)) {
            self.add_rule(Rule::SlicePack {
                source,
                offset,
                target,
            });
        }
    }

    /// Adds a list write rule once.
    fn add_write_list_rule(&mut self, table: ValueId, values: PackId) {
        if self.write_list_rules.insert((table, values)) {
            self.add_rule(Rule::WriteList { table, values });
        }
    }

    /// Registers the facts that can wake `rule`.
    fn subscribe_rule(&mut self, id: usize, rule: &Rule) {
        match rule {
            Rule::Produce { .. }
            | Rule::Require { .. }
            | Rule::IncludeObject { .. }
            | Rule::IncludeClosure { .. }
            | Rule::Sequence { .. } => {}
            Rule::Flow { source, target } | Rule::NonNilFlow { source, target } => {
                self.subscriptions.value(*source, id);
                self.subscriptions.value(*target, id);
            }
            Rule::Filter { source, .. } => self.subscriptions.value(*source, id),
            Rule::ProjectPack { pack, .. } => self.subscriptions.pack(*pack, id),
            Rule::SlicePack { source, .. } => self.subscriptions.pack(*source, id),
            Rule::SetTable { table, key, value } => {
                self.subscriptions.value(*table, id);
                self.subscriptions.value(*key, id);
                self.subscriptions.value(*value, id);
            }
            Rule::WriteList { table, values, .. } => {
                self.subscriptions.value(*table, id);
                self.subscriptions.pack(*values, id);
            }
            Rule::GetTable { table, key, .. } => {
                self.subscriptions.value(*table, id);
                self.subscriptions.value(*key, id);
            }
            Rule::Call {
                callee,
                args,
                returns,
            } => {
                self.subscriptions.value(*callee, id);
                self.subscriptions.pack(*args, id);
                self.subscriptions.pack(*returns, id);
            }
            Rule::Binary { lhs, rhs, .. } => {
                self.subscriptions.value(*lhs, id);
                self.subscriptions.value(*rhs, id);
            }
            Rule::Unary { operand, .. } => self.subscriptions.value(*operand, id),
        }
    }

    /// Installs stable FIR constraints into the dense solver world.
    fn install_program(&mut self, program: InferenceProgram) {
        for key in program.values() {
            let _ = self.world.value_for_key(key.clone());
        }
        for key in program.packs() {
            let _ = self.world.pack_for_key(key);
        }

        for constraint in program.into_constraints() {
            self.install_constraint(constraint);
        }
    }

    /// Translates a stable constraint into dense world identities.
    fn install_constraint(&mut self, constraint: ProgramConstraint) {
        let rule = match constraint {
            Constraint::Produce { value, ty } => Rule::Produce {
                value: self.world.value_for_key(value),
                ty,
            },
            Constraint::Require { value, ty } => Rule::Require {
                value: self.world.value_for_key(value),
                ty,
            },
            Constraint::Flow { source, target } => {
                let source = self.world.value_for_key(source);
                let target = self.world.value_for_key(target);
                self.add_flow_rule(source, target);
                return;
            }
            Constraint::NonNilFlow { source, target } => {
                let source = self.world.value_for_key(source);
                let target = self.world.value_for_key(target);
                self.add_non_nil_flow_rule(source, target);
                return;
            }
            Constraint::Filter {
                source,
                target,
                predicate,
            } => Rule::Filter {
                source: self.world.value_for_key(source),
                target: self.world.value_for_key(target),
                predicate,
            },
            Constraint::IncludeObject { value, object } => Rule::IncludeObject {
                value: self.world.value_for_key(value),
                object: self.world.object_for_key(object),
            },
            Constraint::IncludeClosure { value, proto } => Rule::IncludeClosure {
                value: self.world.value_for_key(value),
                proto,
            },
            Constraint::ProjectPack {
                pack,
                index,
                output,
            } => {
                let pack = self.world.pack_for_key(pack);
                let projection = self.ensure_projection(pack, index);
                let output = self.world.value_for_key(output);
                self.add_flow_rule(projection, output);
                return;
            }
            Constraint::Sequence { pack, head, tail } => Rule::Sequence {
                pack: self.world.pack_for_key(pack),
                head: head
                    .into_iter()
                    .map(|key| self.world.value_for_key(key))
                    .collect(),
                tail: tail.map(|key| self.world.pack_for_key(key)),
            },
            Constraint::SlicePack {
                source,
                offset,
                target,
            } => {
                let source = self.world.pack_for_key(source);
                let target = self.world.pack_for_key(target);
                self.add_slice_rule(source, offset, target);
                return;
            }
            Constraint::SetTable { table, key, value } => Rule::SetTable {
                table: self.world.value_for_key(table),
                key: self.world.value_for_key(key),
                value: self.world.value_for_key(value),
            },
            Constraint::WriteList { table, values } => {
                let table = self.world.value_for_key(table);
                let values = self.world.pack_for_key(values);
                self.add_write_list_rule(table, values);
                return;
            }
            Constraint::GetTable { table, key, output } => Rule::GetTable {
                table: self.world.value_for_key(table),
                key: self.world.value_for_key(key),
                output: self.world.value_for_key(output),
            },
            Constraint::Call {
                callee,
                args,
                returns,
            } => Rule::Call {
                callee: self.world.value_for_key(callee),
                args: self.world.pack_for_key(args),
                returns: self.world.pack_for_key(returns),
            },
            Constraint::Binary {
                lhs,
                op,
                rhs,
                output,
            } => Rule::Binary {
                lhs: self.world.value_for_key(lhs),
                op,
                rhs: self.world.value_for_key(rhs),
                output: self.world.value_for_key(output),
            },
            Constraint::Unary {
                operand,
                op,
                output,
            } => Rule::Unary {
                operand: self.world.value_for_key(operand),
                op,
                output: self.world.value_for_key(output),
            },
        };
        self.add_rule(rule);
    }

    /// Applies a rule.
    fn apply(&mut self, rule_id: usize, rule: Rule) {
        match rule {
            Rule::Produce { value, ty } => {
                self.produce(value, ty);
            }
            Rule::Require { value, ty } => {
                self.require(value, ty);
            }
            Rule::Flow { source, target } => self.flow(source, target),
            Rule::NonNilFlow { source, target } => self.non_nil_flow(source, target),
            Rule::Filter {
                source,
                target,
                predicate,
            } => self.filter(source, target, predicate),
            Rule::IncludeObject { value, object } => {
                self.include_object(value, object);
            }
            Rule::IncludeClosure { value, proto } => {
                self.include_closure(value, proto);
            }
            Rule::ProjectPack {
                pack,
                index,
                output,
            } => self.project_pack(pack, index, output),
            Rule::Sequence { pack, head, tail } => {
                if let WorldChange::Changed(()) = self
                    .world
                    .add_pack_alternative(pack, PackAlternative { head, tail })
                {
                    self.pack_changed(pack);
                }
            }
            Rule::SlicePack {
                source,
                offset,
                target,
            } => self.slice_pack(source, offset, target),
            Rule::SetTable { table, key, value } => self.set_table(rule_id, table, key, value),
            Rule::WriteList { table, values } => self.write_list(table, values),
            Rule::GetTable { table, key, output } => self.get_table(rule_id, table, key, output),
            Rule::Call {
                callee,
                args,
                returns,
            } => self.call(rule_id, callee, args, returns),
            Rule::Binary {
                lhs,
                op,
                rhs,
                output,
            } => self.binary(lhs, op, rhs, output),
            Rule::Unary {
                operand,
                op,
                output,
            } => self.unary(operand, op, output),
        }
    }

    /// Adds a produced type to a value.
    fn produce(&mut self, value: ValueId, ty: TypeId) {
        let old = self.world.values[value].lower;
        let next = self.types.join(old, ty);
        if old == next {
            return;
        }
        self.world.values[value].lower = next;
        self.value_changed(value);
    }

    /// Adds a type that a value must support.
    fn require(&mut self, value: ValueId, ty: TypeId) {
        let old = self.world.values[value].upper;
        let next = self.types.meet(old, ty);
        if old == next {
            return;
        }
        self.world.values[value].upper = next;
        self.value_changed(value);
    }

    /// Copies facts from `source` to `target`.
    fn flow(&mut self, source: ValueId, target: ValueId) {
        let source_state = self.world.values[source].clone();
        let target_upper = self.world.values[target].upper;
        self.produce(target, source_state.lower);
        self.require(source, target_upper);
        for object in source_state.identities.objects {
            self.include_object(target, object);
        }
        for proto in source_state.identities.closures {
            self.include_closure(target, proto);
        }
    }

    /// Copies producer facts after removing `nil`.
    fn non_nil_flow(&mut self, source: ValueId, target: ValueId) {
        let source = self.world.values[source].clone();
        let non_nil = self
            .types
            .exclude(source.lower, &[self.types.primitives().nil]);
        self.produce(target, non_nil);
        for object in source.identities.objects {
            self.include_object(target, object);
        }
        for proto in source.identities.closures {
            self.include_closure(target, proto);
        }
    }

    /// Applies branch filtering when a produced type exists.
    fn filter(&mut self, source: ValueId, target: ValueId, predicate: BranchPredicate) {
        if let Some(source_ty) = self.evidence_type(source) {
            let filtered = match predicate {
                BranchPredicate::Truthy => self.types.truthy_part(source_ty),
                BranchPredicate::Falsy => self.types.falsy_part(source_ty),
            };
            self.produce(target, filtered);
        }
        if predicate == BranchPredicate::Truthy {
            let identities = self.world.values[source].identities.clone();
            for object in identities.objects {
                self.include_object(target, object);
            }
            for proto in identities.closures {
                self.include_closure(target, proto);
            }
        }
    }

    /// Adds a object identity to a value.
    fn include_object(&mut self, value: ValueId, object: ObjectId) {
        if !self.world.values[value].identities.objects.insert(object) {
            return;
        }
        self.value_changed(value);
    }

    /// Adds a closure identity to a value.
    fn include_closure(&mut self, value: ValueId, proto: ProtoId) {
        if !self.world.values[value].identities.closures.insert(proto) {
            return;
        }
        self.value_changed(value);
    }

    /// Wires a pack projection to every current alternative.
    fn project_pack(&mut self, pack: PackId, index: usize, output: ValueId) {
        let alternatives = self.world.packs[pack].alternatives.clone();
        if alternatives.is_empty() {
            return;
        }
        for alternative in alternatives {
            if let Some(source) = alternative.head.get(index).copied() {
                self.add_flow_rule(source, output);
            } else if let Some(tail) = alternative.tail {
                let source = self.ensure_projection(tail, index - alternative.head.len());
                self.add_flow_rule(source, output);
            } else {
                self.produce(output, self.types.primitives().nil);
            }
        }
    }

    /// Sends every known suffix alternative from a pack to another.
    fn slice_pack(&mut self, source: PackId, offset: usize, target: PackId) {
        let alternatives = self.world.packs[source].alternatives.clone();
        for alternative in alternatives {
            if offset <= alternative.head.len() {
                let suffix = PackAlternative {
                    head: alternative.head[offset..].to_vec(),
                    tail: alternative.tail,
                };
                if let WorldChange::Changed(()) = self.world.add_pack_alternative(target, suffix) {
                    self.pack_changed(target);
                }
                continue;
            }

            if let Some(tail) = alternative.tail {
                self.add_slice_rule(tail, offset - alternative.head.len(), target);
            } else if let WorldChange::Changed(()) = self.world.add_pack_alternative(
                target,
                PackAlternative {
                    head: Vec::new(),
                    tail: None,
                },
            ) {
                self.pack_changed(target);
            }
        }
    }

    /// Returns the exact fields or dynamic index described by a key value.
    fn table_key(&self, key: ValueId) -> Option<TableKey> {
        let ty = self.world.values[key].lower;
        if ty == self.types.primitives().never {
            return None;
        }

        let mut fields = Vec::new();
        if self.collect_string_fields(ty, &mut fields) {
            fields.sort_unstable();
            fields.dedup();
            Some(TableKey::Fields(fields))
        } else {
            Some(TableKey::Dynamic)
        }
    }

    /// Collects exact UTF-8 string fields from a canonical type.
    fn collect_string_fields(&self, ty: TypeId, fields: &mut Vec<SmolStr>) -> bool {
        match self.types.get(ty) {
            Type::Literal(TypeLiteral::String(value)) => {
                let Some(value) = value.as_utf8() else {
                    return false;
                };
                fields.push(value.into());
                true
            }
            Type::Union(parts) => parts
                .iter()
                .all(|part| self.collect_string_fields(*part, fields)),
            _ => false,
        }
    }

    /// Applies a table write to every known object identity.
    fn set_table(&mut self, rule_id: usize, table: ValueId, key: ValueId, value: ValueId) {
        let Some(key_kind) = self.table_key(key) else {
            return;
        };
        let objects: Vec<_> = self.world.values[table]
            .identities
            .objects
            .iter()
            .copied()
            .collect();
        for object in objects {
            match &key_kind {
                TableKey::Fields(fields) => {
                    for field in fields {
                        if !self.activations.insert(Activation::SetTable {
                            rule: rule_id,
                            object,
                            field: Some(field.clone()),
                        }) {
                            continue;
                        }
                        let target = self.world.object_field(object, field.clone()).value();
                        self.add_non_nil_flow_rule(value, target);
                    }
                }
                TableKey::Dynamic => {
                    if !self.activations.insert(Activation::SetTable {
                        rule: rule_id,
                        object,
                        field: None,
                    }) {
                        continue;
                    }
                    let keys = self.world.objects[object].keys;
                    let values = self.world.objects[object].values;
                    self.add_flow_rule(key, keys);
                    self.add_non_nil_flow_rule(value, values);
                }
            }
        }
    }

    /// Applies a list write to every known table and pack alternative.
    fn write_list(&mut self, table: ValueId, values: PackId) {
        let objects: Vec<_> = self.world.values[table]
            .identities
            .objects
            .iter()
            .copied()
            .collect();
        let alternatives = self.world.packs[values].alternatives.clone();

        for object in objects {
            let keys = self.world.objects[object].keys;
            let indexed_values = self.world.objects[object].values;
            self.produce(keys, self.types.primitives().number);

            for alternative in &alternatives {
                for &value in &alternative.head {
                    self.add_non_nil_flow_rule(value, indexed_values);
                }
                if let Some(tail) = alternative.tail {
                    self.add_write_list_rule(table, tail);
                }
            }
        }
    }

    /// Applies a table read to every known object identity.
    fn get_table(&mut self, rule_id: usize, table: ValueId, key: ValueId, output: ValueId) {
        let Some(key_kind) = self.table_key(key) else {
            return;
        };
        let objects: Vec<_> = self.world.values[table]
            .identities
            .objects
            .iter()
            .copied()
            .collect();
        for object in objects {
            match &key_kind {
                TableKey::Fields(fields) => {
                    for field in fields {
                        if !self.activations.insert(Activation::GetTable {
                            rule: rule_id,
                            object,
                            field: Some(field.clone()),
                        }) {
                            continue;
                        }
                        let source = self.world.object_field(object, field.clone()).value();
                        self.add_flow_rule(source, output);
                        self.produce(output, self.types.primitives().nil);
                    }
                }
                TableKey::Dynamic => {
                    if !self.activations.insert(Activation::GetTable {
                        rule: rule_id,
                        object,
                        field: None,
                    }) {
                        continue;
                    }
                    let values = self.world.objects[object].values;
                    self.add_flow_rule(values, output);
                    self.produce(output, self.types.primitives().nil);
                }
            }
        }
    }

    /// Connects a callsite to every known closure identity.
    fn call(&mut self, rule_id: usize, callee: ValueId, args: PackId, returns: PackId) {
        let closures: Vec<_> = self.world.values[callee]
            .identities
            .closures
            .iter()
            .copied()
            .collect();
        for proto in closures {
            let Some(function) = self.unit.get(proto) else {
                continue;
            };

            for (index, parameter) in function.params.iter().copied().enumerate() {
                if self.activations.insert(Activation::CallParameter {
                    rule: rule_id,
                    proto,
                    index,
                }) {
                    let argument = self.ensure_projection(args, index);
                    let formal = self.value_for_key(ValueKey::Value(proto, parameter));
                    self.add_flow_rule(argument, formal);
                }
            }

            if function.is_vararg
                && self.activations.insert(Activation::CallVarArgs {
                    rule: rule_id,
                    proto,
                })
            {
                let varargs = self.pack_for_key(PackKey::VarArgs(proto));
                self.add_slice_rule(args, function.params.len(), varargs);
            }

            let return_pack = self.pack_for_key(PackKey::Returns(proto));
            let projections: Vec<_> = self.world.packs[returns]
                .projections
                .iter()
                .map(|(index, value)| (*index, *value))
                .collect();
            for (index, target) in projections {
                if self.activations.insert(Activation::CallReturn {
                    rule: rule_id,
                    proto,
                    index,
                }) {
                    let source = self.ensure_projection(return_pack, index);
                    self.add_flow_rule(source, target);
                }
            }
        }
    }

    /// Applies primitive binary operator facts.
    #[inline]
    fn binary(&mut self, lhs: ValueId, op: BinOp, rhs: ValueId, output: ValueId) {
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => {
                self.produce(output, self.types.primitives().boolean);
                if matches!(op, BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte) {
                    let accepted = self.types.union(
                        self.types.primitives().number,
                        self.types.primitives().string,
                    );
                    self.require(lhs, accepted);
                    self.require(rhs, accepted);
                }
            }
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::IDiv
            | BinOp::Mod
            | BinOp::Pow => {
                let number = self.types.primitives().number;
                let vector = self.types.primitives().vector;

                match op {
                    BinOp::Add | BinOp::Sub => {
                        let accepted = self.types.union(number, vector);
                        self.require(lhs, accepted);
                        self.require(rhs, accepted);
                        self.require_matching_additive_operands(lhs, rhs);
                    }
                    BinOp::Mul | BinOp::Div | BinOp::IDiv => {
                        let accepted = self.types.union(number, vector);
                        self.require(lhs, accepted);
                        self.require(rhs, accepted);
                    }
                    BinOp::Mod | BinOp::Pow => {
                        self.require(lhs, number);
                        self.require(rhs, number);
                    }
                    _ => unreachable!("checked in the parent match"),
                }

                self.produce_arithmetic_result(lhs, op, rhs, output);
            }
            BinOp::Concat => {
                let accepted = self.types.union(
                    self.types.primitives().string,
                    self.types.primitives().number,
                );
                self.require(lhs, accepted);
                self.require(rhs, accepted);
                self.produce(output, self.types.primitives().string);
            }
            BinOp::And => {
                if let Some(lhs_ty) = self.evidence_type(lhs) {
                    let falsy = self.types.falsy_part(lhs_ty);
                    self.produce(output, falsy);
                }
                if let Some(rhs_ty) = self.evidence_type(rhs) {
                    self.produce(output, rhs_ty);
                }
            }
            BinOp::Or => {
                if let Some(lhs_ty) = self.evidence_type(lhs) {
                    let truthy = self.types.truthy_part(lhs_ty);
                    self.produce(output, truthy);
                }
                if let Some(rhs_ty) = self.evidence_type(rhs) {
                    self.produce(output, rhs_ty);
                }
            }
        }
    }

    /// Applies primitive unary operator facts.
    #[inline]
    fn unary(&mut self, operand: ValueId, op: UnOp, output: ValueId) {
        match op {
            UnOp::Not => {
                self.produce(output, self.types.primitives().boolean);
            }
            UnOp::Minus => {
                self.require(operand, self.types.primitives().number);
                self.produce(output, self.types.primitives().number);
            }
            UnOp::Length => {
                let accepted = self.types.union(
                    self.types.primitives().string,
                    self.types.primitives().table,
                );
                self.require(operand, accepted);
                self.produce(output, self.types.primitives().number);
            }
        }
    }

    /// Returns a stable projection and installs its maintenance rule.
    pub(super) fn ensure_projection(&mut self, pack: PackId, index: usize) -> ValueId {
        match self.world.projection(pack, index) {
            WorldChange::Unchanged(value) => value,
            WorldChange::Changed(value) => {
                self.add_rule(Rule::ProjectPack {
                    pack,
                    index,
                    output: value,
                });
                self.pack_changed(pack);
                value
            }
        }
    }

    /// Returns the types known to come from a value, including identity types.
    fn evidence_type(&mut self, value: ValueId) -> Option<TypeId> {
        let state = self.world.values[value].clone();
        let mut evidence = state.lower;
        if !state.identities.objects.is_empty() {
            evidence = self.types.join(evidence, self.types.primitives().table);
        }
        if !state.identities.closures.is_empty() {
            evidence = self.types.join(evidence, self.types.primitives().function);
        }
        (evidence != self.types.primitives().never).then_some(evidence)
    }

    /// Re-enqueues every rule subscribed to a changed value.
    #[inline]
    fn value_changed(&mut self, value: ValueId) {
        if let Some(rules) = self.subscriptions.values.get(&value) {
            self.queue.extend(rules.iter().copied());
        }
    }

    /// Re-enqueues every rule subscribed to a changed pack.
    #[inline]
    fn pack_changed(&mut self, pack: PackId) {
        if let Some(rules) = self.subscriptions.packs.get(&pack) {
            self.queue.extend(rules.iter().copied());
        }
    }

    /// Returns the finite width currently described by a pack.
    fn pack_width(&self, pack: PackId, visiting: &mut HashSet<PackId>) -> usize {
        if !visiting.insert(pack) {
            return 0;
        }
        let width = self.world.packs[pack]
            .alternatives
            .iter()
            .map(|alternative| {
                alternative.head.len()
                    + alternative
                        .tail
                        .map(|tail| self.pack_width(tail, visiting))
                        .unwrap_or(0)
            })
            .max()
            .unwrap_or(0);
        visiting.remove(&pack);
        width
    }

    /// Returns the best materializable candidate for a value.
    fn candidate_type(&self, value: ValueId) -> Option<TypeId> {
        let state = &self.world.values[value];
        if state.lower != self.types.primitives().never {
            return self
                .types
                .is_subtype(state.lower, state.upper)
                .then_some(state.lower);
        }
        (state.upper != self.types.primitives().unknown).then_some(state.upper)
    }

    /// Materializes every stable value and transfers ownership of the type graph.
    fn materialize(mut self) -> Output {
        let keys: Vec<_> = self.world.value_keys().collect();
        let mut values = HashMap::new();
        for (key, value) in keys {
            if let Some(ty) = self.materialize_value(value, &mut HashSet::new()) {
                let ty = self.types.widen_literals(ty);
                values.insert(key, ty);
            }
        }
        Output {
            store: self.types,
            values,
        }
    }

    /// Materializes a solved value into the canonical graph.
    fn materialize_value(
        &mut self,
        value: ValueId,
        visiting: &mut HashSet<ValueId>,
    ) -> Option<TypeId> {
        if !visiting.insert(value) {
            return Some(self.types.primitives().unknown);
        }

        let state = self.world.values[value].clone();
        let mut parts = Vec::new();
        if state.lower != self.types.primitives().never {
            parts.push(state.lower);
        }
        for object in state.identities.objects {
            parts.push(self.materialize_object(object, visiting));
        }
        for proto in state.identities.closures {
            parts.push(self.materialize_function(proto, visiting));
        }

        let ty = if parts.is_empty() {
            self.candidate_type(value)
        } else {
            let ty = self.types.join_all(parts);
            self.types.is_subtype(ty, state.upper).then_some(ty)
        };
        visiting.remove(&value);
        ty.filter(|ty| *ty != self.types.primitives().never)
    }

    /// Materializes a mutable object as a structural table.
    fn materialize_object(&mut self, object: ObjectId, visiting: &mut HashSet<ValueId>) -> TypeId {
        let state = &self.world.objects[object];
        let mut field_values: Vec<_> = state
            .fields
            .iter()
            .map(|(name, value)| (name.clone(), *value))
            .collect();
        let keys = state.keys;
        let values = state.values;

        field_values.sort_unstable_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
        let mut fields = Vec::with_capacity(field_values.len());
        for (name, value) in field_values {
            if let Some(value) = self.materialize_value(value, visiting) {
                let value = self.types.join(value, self.types.primitives().nil);
                fields.push((name, value));
            }
        }

        let indexer = match (
            self.materialize_value(keys, visiting),
            self.materialize_value(values, visiting),
        ) {
            (Some(key), Some(value)) => {
                let value = self.types.join(value, self.types.primitives().nil);
                Some((key, value))
            }
            _ => None,
        };
        self.types.table_shape(fields, indexer)
    }

    /// Materializes a closure as a function signature.
    fn materialize_function(&mut self, proto: ProtoId, visiting: &mut HashSet<ValueId>) -> TypeId {
        let Some(function) = self.unit.get(proto) else {
            return self.types.primitives().function;
        };
        let params = function.params.clone();
        let is_vararg = function.is_vararg;
        let unknown = self.types.primitives().unknown;
        let params: Vec<_> = params
            .into_iter()
            .map(|parameter| {
                let value = self.value_for_key(ValueKey::Value(proto, parameter));
                self.materialize_value(value, visiting).unwrap_or(unknown)
            })
            .collect();
        let tail = is_vararg.then_some(crate::ty::canonical::TypePackTail::Homogeneous(unknown));
        let params = self.types.pack(params, tail);
        let returns = self.pack_for_key(PackKey::Returns(proto));
        let mut projections: Vec<_> = self.world.packs[returns]
            .projections
            .iter()
            .map(|(index, value)| (*index, *value))
            .collect();
        projections.sort_by_key(|(index, _)| *index);
        let returns = projections
            .into_iter()
            .map(|(_, value)| self.materialize_value(value, visiting).unwrap_or(unknown))
            .collect();
        let returns = self.types.pack(returns, None);
        self.types.function_signature(params, returns)
    }

    /// Produces results for arithmetic overloads supported by current evidence.
    fn produce_arithmetic_result(
        &mut self,
        lhs: ValueId,
        op: BinOp,
        rhs: ValueId,
        output: ValueId,
    ) {
        let Some(lhs) = self.evidence_type(lhs) else {
            return;
        };
        let Some(rhs) = self.evidence_type(rhs) else {
            return;
        };

        let number = self.types.primitives().number;
        let vector = self.types.primitives().vector;

        let lhs_number = self.types.overlaps(lhs, number);
        let lhs_vector = self.types.overlaps(lhs, vector);
        let rhs_number = self.types.overlaps(rhs, number);
        let rhs_vector = self.types.overlaps(rhs, vector);

        match op {
            BinOp::Add | BinOp::Sub => {
                if lhs_number && rhs_number {
                    self.produce(output, number);
                }
                if lhs_vector && rhs_vector {
                    self.produce(output, vector);
                }
            }
            BinOp::Mul | BinOp::Div | BinOp::IDiv => {
                if lhs_number && rhs_number {
                    self.produce(output, number);
                }
                if (lhs_vector && (rhs_number || rhs_vector))
                    || (rhs_vector && (lhs_number || lhs_vector))
                {
                    self.produce(output, vector);
                }
            }
            BinOp::Mod | BinOp::Pow => {
                if lhs_number && rhs_number {
                    self.produce(output, number);
                }
            }
            _ => unreachable!("guarded by caller"),
        }
    }

    /// Narrows additive operands when either operand has concrete evidence.
    fn require_matching_additive_operands(&mut self, lhs: ValueId, rhs: ValueId) {
        let number = self.types.primitives().number;
        let vector = self.types.primitives().vector;

        if let Some(lhs_ty) = self.evidence_type(lhs) {
            if self.types.overlaps(lhs_ty, number) {
                self.require(rhs, number);
            }
            if self.types.overlaps(lhs_ty, vector) {
                self.require(rhs, vector);
            }
        }

        if let Some(rhs_ty) = self.evidence_type(rhs) {
            if self.types.overlaps(rhs_ty, number) {
                self.require(lhs, number);
            }
            if self.types.overlaps(rhs_ty, vector) {
                self.require(lhs, vector);
            }
        }
    }
}
