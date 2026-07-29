//! Agenda-based fixed-point engine.

use std::collections::{HashMap, HashSet, VecDeque};

use smol_str::SmolStr;

use crate::{
    hil::{
        lifted::LiftedFunction,
        ty2::{
            builtins::{BuiltinEnvironment, BuiltinPath},
            canonical::{Type, TypeId},
            store::TypeStore,
        },
    },
    il::ProtoId,
    operator::{BinOp, UnOp},
};

use super::{
    keys::{BranchPredicate, PackKey, ValueKey},
    program::{InferenceProgram, PackRelation, ValueRelation},
    world::{ObjectId, PackAlternative, PackId, ValueId, World},
};

/// One semantic rule applied by the engine.
#[derive(Debug, Clone)]
enum Rule {
    /// Adds producer evidence.
    Observe { value: ValueId, ty: TypeId },
    /// Adds consumer evidence.
    Require { value: ValueId, ty: TypeId },
    /// Copies value facts from `source` to `target`.
    Flow { source: ValueId, target: ValueId },
    /// Copies value facts except `nil` from `source` to `target`.
    NonNilFlow { source: ValueId, target: ValueId },
    /// Copies facts both ways between two values.
    Same { lhs: ValueId, rhs: ValueId },
    /// Applies a branch filter.
    Filter {
        source: ValueId,
        target: ValueId,
        predicate: BranchPredicate,
    },
    /// Adds one table identity.
    IncludeObject { value: ValueId, object: ObjectId },
    /// Adds one closure identity.
    IncludeClosure { value: ValueId, proto: ProtoId },
    /// Adds one builtin identity.
    IncludeBuiltin { value: ValueId, path: BuiltinPath },
    /// Maintains one pack projection.
    ProjectPack {
        pack: PackId,
        index: usize,
        output: ValueId,
    },
    /// Maintains one aggregate pack value.
    PackValues { pack: PackId, output: ValueId },
    /// Writes a named object field.
    WriteField {
        object: ValueId,
        field: SmolStr,
        value: ValueId,
        definite: bool,
    },
    /// Reads a named object field.
    ReadField {
        object: ValueId,
        field: SmolStr,
        output: ValueId,
    },
    /// Writes a dynamic object index.
    WriteIndex {
        object: ValueId,
        index: ValueId,
        value: ValueId,
    },
    /// Reads a dynamic object index.
    ReadIndex {
        object: ValueId,
        index: ValueId,
        output: ValueId,
    },
    /// Connects a callable value to known callable identities.
    Call {
        callee: ValueId,
        args: PackId,
        returns: PackId,
    },
    /// Applies primitive binary operator facts.
    Binary {
        lhs: ValueId,
        op: BinOp,
        rhs: ValueId,
        output: ValueId,
    },
    /// Applies primitive unary operator facts.
    Unary {
        operand: ValueId,
        op: UnOp,
        output: ValueId,
    },
}

/// One dynamic connection that must be installed once.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Activation {
    /// A call argument has been linked to a formal parameter.
    CallParameter {
        rule: usize,
        proto: ProtoId,
        index: usize,
    },
    /// A call result projection has been linked to a closure return.
    CallReturn {
        rule: usize,
        proto: ProtoId,
        index: usize,
    },
    /// A named write has been linked to one object.
    WriteField { rule: usize, object: ObjectId },
    /// A named read has been linked to one object.
    ReadField { rule: usize, object: ObjectId },
    /// A dynamic write has been linked to one object.
    WriteIndex { rule: usize, object: ObjectId },
    /// A dynamic read has been linked to one object.
    ReadIndex { rule: usize, object: ObjectId },
}

/// Flow rule variant used for deduplication.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FlowKind {
    /// Ordinary producer and consumer flow.
    Full,
    /// Producer flow that removes `nil`.
    NonNil,
}

/// Pending rule queue with duplicate suppression.
#[derive(Debug, Default)]
struct Agenda {
    queue: VecDeque<usize>,
    queued: HashSet<usize>,
}

impl Agenda {
    /// Adds one rule to the queue if it is not already pending.
    fn push(&mut self, rule: usize) {
        if self.queued.insert(rule) {
            self.queue.push_back(rule);
        }
    }

    /// Removes the next pending rule.
    fn pop(&mut self) -> Option<usize> {
        let rule = self.queue.pop_front()?;
        self.queued.remove(&rule);
        Some(rule)
    }
}

/// Reverse dependency index from changed facts to rules.
#[derive(Debug, Default)]
struct Subscriptions {
    values: HashMap<ValueId, HashSet<usize>>,
    packs: HashMap<PackId, HashSet<usize>>,
    objects: HashMap<ObjectId, HashSet<usize>>,
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

    /// Records that `rule` must rerun when `object` shape changes.
    fn object(&mut self, object: ObjectId, rule: usize) {
        self.objects.entry(object).or_default().insert(rule);
    }
}

/// Solver over immutable relations and mutable domain state.
pub struct Engine<'a> {
    pub(super) types: &'a mut TypeStore,
    pub(super) world: World,
    pub(super) functions: &'a [LiftedFunction],
    builtins: &'a BuiltinEnvironment,
    rules: Vec<Rule>,
    subscriptions: Subscriptions,
    agenda: Agenda,
    activations: HashSet<Activation>,
    flow_rules: HashSet<(ValueId, ValueId, FlowKind)>,
}

impl<'a> Engine<'a> {
    /// Builds an engine and installs every relation from `program`.
    pub fn new(
        program: InferenceProgram,
        functions: &'a [LiftedFunction],
        builtins: &'a BuiltinEnvironment,
        types: &'a mut TypeStore,
    ) -> Self {
        let primitives = *types.primitives();
        let mut engine = Self {
            types,
            world: World::new(primitives.never, primitives.unknown),
            functions,
            builtins,
            rules: Vec::new(),
            subscriptions: Subscriptions::default(),
            agenda: Agenda::default(),
            activations: HashSet::new(),
            flow_rules: HashSet::new(),
        };
        engine.install_program(program);
        engine
    }

    /// Runs the agenda until no subscribed fact changes.
    pub fn solve(&mut self) {
        while let Some(rule_id) = self.agenda.pop() {
            let rule = self.rules[rule_id].clone();
            self.apply(rule_id, rule);
        }
    }

    /// Returns every allocated symbol key.
    pub fn symbol_keys(&self) -> Vec<(ProtoId, crate::hil::lifter::ssa::SymbolId, ValueKey)> {
        self.world
            .value_keys()
            .into_iter()
            .filter_map(|(key, _)| match key {
                ValueKey::Symbol(proto, symbol) => Some((proto, symbol, key)),
                ValueKey::Temp(_, _) | ValueKey::Occurrence(_, _, _) => None,
            })
            .collect()
    }

    /// Returns or creates the value for `key`.
    pub(super) fn value_for_key(&mut self, key: ValueKey) -> ValueId {
        self.world.value_for_key(key)
    }

    /// Returns or creates the pack for `key`.
    pub(super) fn pack_for_key(&mut self, key: PackKey) -> PackId {
        self.world.pack_for_key(key)
    }

    /// Returns the value ID for a key if it exists.
    pub(super) fn get_value_key(&self, key: ValueKey) -> Option<ValueId> {
        self.world.get_value_key(key)
    }

    /// Returns the pack ID for a key if it exists.
    pub(super) fn get_pack_key(&self, key: PackKey) -> Option<PackId> {
        self.world.get_pack_key(key)
    }

    /// Adds one rule and subscribes it to its direct inputs.
    fn add_rule(&mut self, rule: Rule) -> usize {
        let id = self.rules.len();
        self.subscribe_rule(id, &rule);
        self.rules.push(rule);
        self.agenda.push(id);
        id
    }

    /// Adds a flow rule once.
    fn add_flow_rule(&mut self, source: ValueId, target: ValueId) {
        if self.flow_rules.insert((source, target, FlowKind::Full)) {
            self.add_rule(Rule::Flow { source, target });
        }
    }

    /// Adds a non-nil producer flow rule once.
    fn add_non_nil_flow_rule(&mut self, source: ValueId, target: ValueId) {
        if self.flow_rules.insert((source, target, FlowKind::NonNil)) {
            self.add_rule(Rule::NonNilFlow { source, target });
        }
    }

    /// Registers the facts that can wake `rule`.
    fn subscribe_rule(&mut self, id: usize, rule: &Rule) {
        match rule {
            Rule::Observe { .. }
            | Rule::Require { .. }
            | Rule::IncludeObject { .. }
            | Rule::IncludeClosure { .. }
            | Rule::IncludeBuiltin { .. } => {}
            Rule::Flow { source, target } | Rule::NonNilFlow { source, target } => {
                self.subscriptions.value(*source, id);
                self.subscriptions.value(*target, id);
            }
            Rule::Same { lhs, rhs } => {
                self.subscriptions.value(*lhs, id);
                self.subscriptions.value(*rhs, id);
            }
            Rule::Filter { source, .. } => self.subscriptions.value(*source, id),
            Rule::ProjectPack { pack, .. } | Rule::PackValues { pack, .. } => {
                self.subscriptions.pack(*pack, id);
            }
            Rule::WriteField { object, value, .. } => {
                self.subscriptions.value(*object, id);
                self.subscriptions.value(*value, id);
            }
            Rule::ReadField { object, .. } => self.subscriptions.value(*object, id),
            Rule::WriteIndex {
                object,
                index,
                value,
            } => {
                self.subscriptions.value(*object, id);
                self.subscriptions.value(*index, id);
                self.subscriptions.value(*value, id);
            }
            Rule::ReadIndex { object, index, .. } => {
                self.subscriptions.value(*object, id);
                self.subscriptions.value(*index, id);
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

    /// Installs lowered relations into the world.
    fn install_program(&mut self, program: InferenceProgram) {
        for (key, _) in program.value_relations() {
            self.world.value_for_key(key);
        }
        for (key, _) in program.pack_relations() {
            self.world.pack_for_key(key);
        }

        for (key, relations) in program.pack_relations() {
            let pack = self.world.pack_for_key(key);
            for relation in relations {
                match relation {
                    PackRelation::Sequence { head, tail } => {
                        let head = head
                            .into_iter()
                            .map(|key| self.world.value_for_key(key))
                            .collect();
                        let tail = tail.map(|key| self.world.pack_for_key(key));
                        if self
                            .world
                            .add_pack_alternative(pack, PackAlternative { head, tail })
                        {
                            self.pack_changed(pack);
                        }
                    }
                }
            }
        }

        for (key, relations) in program.value_relations() {
            let value = self.world.value_for_key(key);
            for relation in relations {
                self.install_value_relation(value, relation);
            }
        }

        for (key, types) in program.seeds() {
            let value = self.world.value_for_key(key);
            for ty in types {
                self.add_rule(Rule::Observe { value, ty });
                self.add_rule(Rule::Require { value, ty });
            }
        }
    }

    /// Installs one scalar relation as one or more engine rules.
    fn install_value_relation(&mut self, value: ValueId, relation: ValueRelation) {
        match relation {
            ValueRelation::Observe(ty) => {
                self.add_rule(Rule::Observe { value, ty });
            }
            ValueRelation::Require(ty) => {
                self.add_rule(Rule::Require { value, ty });
            }
            ValueRelation::FlowFrom(source) => {
                let source = self.world.value_for_key(source);
                self.add_flow_rule(source, value);
            }
            ValueRelation::SameAs(other) => {
                let other = self.world.value_for_key(other);
                self.add_rule(Rule::Same {
                    lhs: value,
                    rhs: other,
                });
            }
            ValueRelation::FromPack { pack, index } => {
                let pack = self.world.pack_for_key(pack);
                let projection = self.ensure_projection(pack, index);
                self.add_flow_rule(projection, value);
            }
            ValueRelation::FromPackValues { pack } => {
                let pack = self.world.pack_for_key(pack);
                let aggregate = self.ensure_pack_values(pack);
                self.add_flow_rule(aggregate, value);
            }
            ValueRelation::Filter { source, predicate } => {
                let source = self.world.value_for_key(source);
                self.add_rule(Rule::Filter {
                    source,
                    target: value,
                    predicate,
                });
            }
            ValueRelation::NewObject(key) => {
                let object = self.world.object_for_key(key);
                self.add_rule(Rule::IncludeObject { value, object });
            }
            ValueRelation::Closure(proto) => {
                self.add_rule(Rule::IncludeClosure { value, proto });
            }
            ValueRelation::Builtin(path) => {
                self.add_rule(Rule::IncludeBuiltin { value, path });
            }
            ValueRelation::WriteField {
                field,
                value: source,
                definite,
            } => {
                let source = self.world.value_for_key(source);
                self.add_rule(Rule::WriteField {
                    object: value,
                    field,
                    value: source,
                    definite,
                });
            }
            ValueRelation::ReadField { field, output } => {
                let output = self.world.value_for_key(output);
                self.add_rule(Rule::ReadField {
                    object: value,
                    field,
                    output,
                });
            }
            ValueRelation::WriteIndex {
                index,
                value: source,
            } => {
                let index = self.world.value_for_key(index);
                let source = self.world.value_for_key(source);
                self.add_rule(Rule::WriteIndex {
                    object: value,
                    index,
                    value: source,
                });
            }
            ValueRelation::ReadIndex { index, output } => {
                let index = self.world.value_for_key(index);
                let output = self.world.value_for_key(output);
                self.add_rule(Rule::ReadIndex {
                    object: value,
                    index,
                    output,
                });
            }
            ValueRelation::Call { args, returns } => {
                let args = self.world.pack_for_key(args);
                let returns = self.world.pack_for_key(returns);
                self.add_rule(Rule::Call {
                    callee: value,
                    args,
                    returns,
                });
            }
            ValueRelation::Binary { op, rhs, output } => {
                let rhs = self.world.value_for_key(rhs);
                let output = self.world.value_for_key(output);
                self.add_rule(Rule::Binary {
                    lhs: value,
                    op,
                    rhs,
                    output,
                });
            }
            ValueRelation::Unary { op, output } => {
                let output = self.world.value_for_key(output);
                self.add_rule(Rule::Unary {
                    operand: value,
                    op,
                    output,
                });
            }
        }
    }

    /// Applies one rule.
    fn apply(&mut self, rule_id: usize, rule: Rule) {
        match rule {
            Rule::Observe { value, ty } => {
                self.observe(value, ty);
            }
            Rule::Require { value, ty } => {
                self.require(value, ty);
            }
            Rule::Flow { source, target } => self.flow(source, target),
            Rule::NonNilFlow { source, target } => self.non_nil_flow(source, target),
            Rule::Same { lhs, rhs } => {
                self.flow(lhs, rhs);
                self.flow(rhs, lhs);
            }
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
            Rule::IncludeBuiltin { value, path } => {
                self.include_builtin(value, path);
            }
            Rule::ProjectPack {
                pack,
                index,
                output,
            } => self.project_pack(rule_id, pack, index, output),
            Rule::PackValues { pack, output } => self.pack_values(rule_id, pack, output),
            Rule::WriteField {
                object,
                field,
                value,
                definite,
            } => self.write_field(rule_id, object, field, value, definite),
            Rule::ReadField {
                object,
                field,
                output,
            } => self.read_field(rule_id, object, field, output),
            Rule::WriteIndex {
                object,
                index,
                value,
            } => self.write_index(rule_id, object, index, value),
            Rule::ReadIndex {
                object,
                index,
                output,
            } => self.read_index(rule_id, object, index, output),
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

    /// Adds producer evidence to one value.
    fn observe(&mut self, value: ValueId, ty: TypeId) -> bool {
        let old = self.world.values[value].lower;
        let next = self.types.join(old, ty);
        if old == next {
            return false;
        }
        self.world.values[value].lower = next;
        self.value_changed(value);
        true
    }

    /// Adds consumer evidence to one value.
    fn require(&mut self, value: ValueId, ty: TypeId) -> bool {
        let old = self.world.values[value].upper;
        let next = self.types.meet(old, ty);
        if old == next {
            return false;
        }
        self.world.values[value].upper = next;
        self.value_changed(value);
        true
    }

    /// Copies facts from `source` to `target`.
    fn flow(&mut self, source: ValueId, target: ValueId) {
        let source_state = self.world.values[source].clone();
        let target_upper = self.world.values[target].upper;
        self.observe(target, source_state.lower);
        self.require(source, target_upper);
        for object in source_state.identities.objects {
            self.include_object(target, object);
        }
        for proto in source_state.identities.closures {
            self.include_closure(target, proto);
        }
        for path in source_state.identities.builtins {
            self.include_builtin(target, path);
        }
    }

    /// Copies producer facts after removing `nil`.
    fn non_nil_flow(&mut self, source: ValueId, target: ValueId) {
        let lower = self.world.values[source].lower;
        let non_nil = self.types.exclude(lower, &[self.types.primitives().nil]);
        self.observe(target, non_nil);
    }

    /// Applies branch filtering when producer evidence exists.
    fn filter(&mut self, source: ValueId, target: ValueId, predicate: BranchPredicate) {
        if let Some(source_ty) = self.evidence_type(source) {
            let filtered = match predicate {
                BranchPredicate::Truthy => self.types.truthy_part(source_ty),
                BranchPredicate::Falsy => self.types.falsy_part(source_ty),
            };
            self.observe(target, filtered);
        }
        if predicate == BranchPredicate::Truthy {
            let identities = self.world.values[source].identities.clone();
            for object in identities.objects {
                self.include_object(target, object);
            }
            for proto in identities.closures {
                self.include_closure(target, proto);
            }
            for path in identities.builtins {
                self.include_builtin(target, path);
            }
        }
    }

    /// Adds one object identity to a value.
    fn include_object(&mut self, value: ValueId, object: ObjectId) -> bool {
        if !self.world.values[value].identities.objects.insert(object) {
            return false;
        }
        self.value_changed(value);
        true
    }

    /// Adds one closure identity to a value.
    fn include_closure(&mut self, value: ValueId, proto: ProtoId) -> bool {
        if !self.world.values[value].identities.closures.insert(proto) {
            return false;
        }
        self.value_changed(value);
        true
    }

    /// Adds one builtin identity to a value.
    fn include_builtin(&mut self, value: ValueId, path: BuiltinPath) -> bool {
        if self.builtins.get_path(&path).is_none() {
            return false;
        }
        if !self.world.values[value].identities.builtins.insert(path) {
            return false;
        }
        self.value_changed(value);
        true
    }

    /// Wires a pack projection to every current alternative.
    fn project_pack(&mut self, _rule_id: usize, pack: PackId, index: usize, output: ValueId) {
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
                self.observe(output, self.types.primitives().nil);
            }
        }
    }

    /// Wires an aggregate pack value to every current alternative.
    fn pack_values(&mut self, _rule_id: usize, pack: PackId, output: ValueId) {
        let alternatives = self.world.packs[pack].alternatives.clone();
        for alternative in alternatives {
            for source in alternative.head {
                self.add_flow_rule(source, output);
            }
            if let Some(tail) = alternative.tail {
                let source = self.ensure_pack_values(tail);
                self.add_flow_rule(source, output);
            }
        }
    }

    /// Applies a named field write to every known object identity.
    fn write_field(
        &mut self,
        rule_id: usize,
        object: ValueId,
        field: SmolStr,
        value: ValueId,
        definite: bool,
    ) {
        let objects: Vec<_> = self.world.values[object]
            .identities
            .objects
            .iter()
            .copied()
            .collect();
        for target in objects {
            if !self.activations.insert(Activation::WriteField {
                rule: rule_id,
                object: target,
            }) {
                continue;
            }
            let (field_value, changed) = self.world.object_field(target, field.clone(), definite);
            self.add_flow_rule(value, field_value);
            if changed {
                self.object_changed(target);
            }
        }
    }

    /// Applies a named field read to every known object identity.
    fn read_field(&mut self, rule_id: usize, object: ValueId, field: SmolStr, output: ValueId) {
        let objects: Vec<_> = self.world.values[object]
            .identities
            .objects
            .iter()
            .copied()
            .collect();
        for source in objects {
            if !self.activations.insert(Activation::ReadField {
                rule: rule_id,
                object: source,
            }) {
                continue;
            }
            let (field_value, changed) = self.world.object_field(source, field.clone(), false);
            self.add_flow_rule(field_value, output);
            self.observe(output, self.types.primitives().nil);
            if changed {
                self.object_changed(source);
            }
        }
    }

    /// Applies a dynamic index write to every known object identity.
    fn write_index(&mut self, rule_id: usize, object: ValueId, index: ValueId, value: ValueId) {
        let objects: Vec<_> = self.world.values[object]
            .identities
            .objects
            .iter()
            .copied()
            .collect();
        for target in objects {
            if !self.activations.insert(Activation::WriteIndex {
                rule: rule_id,
                object: target,
            }) {
                continue;
            }
            let keys = self.world.objects[target].keys;
            let values = self.world.objects[target].values;
            self.add_flow_rule(index, keys);
            self.add_non_nil_flow_rule(value, values);
            self.object_changed(target);
        }
    }

    /// Applies a dynamic index read to every known object identity.
    fn read_index(&mut self, rule_id: usize, object: ValueId, _index: ValueId, output: ValueId) {
        let objects: Vec<_> = self.world.values[object]
            .identities
            .objects
            .iter()
            .copied()
            .collect();
        for source in objects {
            if !self.activations.insert(Activation::ReadIndex {
                rule: rule_id,
                object: source,
            }) {
                continue;
            }
            let values = self.world.objects[source].values;
            self.add_flow_rule(values, output);
            self.observe(output, self.types.primitives().nil);
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
            let Some(function) = self.functions.get(proto.0 as usize) else {
                continue;
            };
            if function.proto != proto {
                continue;
            }

            for (index, parameter) in function.symbols.params.iter().copied().enumerate() {
                if self.activations.insert(Activation::CallParameter {
                    rule: rule_id,
                    proto,
                    index,
                }) {
                    let argument = self.ensure_projection(args, index);
                    let formal = self.value_for_key(ValueKey::Symbol(proto, parameter));
                    self.add_flow_rule(argument, formal);
                }
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
    fn binary(&mut self, lhs: ValueId, op: BinOp, rhs: ValueId, output: ValueId) {
        let primitives = *self.types.primitives();
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => {
                self.observe(output, primitives.boolean);
                if matches!(op, BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte) {
                    let accepted = self.types.union(primitives.number, primitives.string);
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
                self.require(lhs, primitives.number);
                self.require(rhs, primitives.number);
                self.observe(output, primitives.number);
            }
            BinOp::Concat => {
                let accepted = self.types.union(primitives.string, primitives.number);
                self.require(lhs, accepted);
                self.require(rhs, accepted);
                self.observe(output, primitives.string);
            }
            BinOp::And => {
                if let Some(lhs_ty) = self.evidence_type(lhs) {
                    let falsy = self.types.falsy_part(lhs_ty);
                    self.observe(output, falsy);
                }
                if let Some(rhs_ty) = self.evidence_type(rhs) {
                    self.observe(output, rhs_ty);
                }
            }
            BinOp::Or => {
                if let Some(lhs_ty) = self.evidence_type(lhs) {
                    let truthy = self.types.truthy_part(lhs_ty);
                    self.observe(output, truthy);
                }
                if let Some(rhs_ty) = self.evidence_type(rhs) {
                    self.observe(output, rhs_ty);
                }
            }
        }
    }

    /// Applies primitive unary operator facts.
    fn unary(&mut self, operand: ValueId, op: UnOp, output: ValueId) {
        let primitives = *self.types.primitives();
        match op {
            UnOp::Not => {
                self.observe(output, primitives.boolean);
            }
            UnOp::Minus => {
                self.require(operand, primitives.number);
                self.observe(output, primitives.number);
            }
            UnOp::Length => {
                let accepted = self.types.union(primitives.string, primitives.table);
                self.require(operand, accepted);
                self.observe(output, primitives.number);
            }
        }
    }

    /// Returns a stable projection and installs its maintenance rule.
    pub(super) fn ensure_projection(&mut self, pack: PackId, index: usize) -> ValueId {
        let (value, created) = self.world.projection(pack, index);
        if created {
            self.add_rule(Rule::ProjectPack {
                pack,
                index,
                output: value,
            });
            self.pack_changed(pack);
        }
        value
    }

    /// Returns a stable aggregate value and installs its maintenance rule.
    pub(super) fn ensure_pack_values(&mut self, pack: PackId) -> ValueId {
        let (value, created) = self.world.pack_values(pack);
        if created {
            self.add_rule(Rule::PackValues {
                pack,
                output: value,
            });
            self.pack_changed(pack);
        }
        value
    }

    /// Returns producer evidence with broad markers for identity-only values.
    pub(super) fn evidence_type(&mut self, value: ValueId) -> Option<TypeId> {
        let state = self.world.values[value].clone();
        let primitives = *self.types.primitives();
        let mut evidence = state.lower;
        if !state.identities.objects.is_empty() {
            evidence = self.types.join(evidence, primitives.table);
        }
        if !state.identities.closures.is_empty() || !state.identities.builtins.is_empty() {
            evidence = self.types.join(evidence, primitives.function);
        }
        (evidence != primitives.never).then_some(evidence)
    }

    /// Re-enqueues every rule subscribed to a changed value.
    fn value_changed(&mut self, value: ValueId) {
        let rules = self
            .subscriptions
            .values
            .get(&value)
            .cloned()
            .unwrap_or_default();
        for rule in rules {
            self.agenda.push(rule);
        }
    }

    /// Re-enqueues every rule subscribed to a changed pack.
    fn pack_changed(&mut self, pack: PackId) {
        let rules = self
            .subscriptions
            .packs
            .get(&pack)
            .cloned()
            .unwrap_or_default();
        for rule in rules {
            self.agenda.push(rule);
        }
    }

    /// Re-enqueues every rule subscribed to a changed object.
    fn object_changed(&mut self, object: ObjectId) {
        let rules = self
            .subscriptions
            .objects
            .get(&object)
            .cloned()
            .unwrap_or_default();
        for rule in rules {
            self.agenda.push(rule);
        }
    }

    /// Returns a produced type when lower and upper bounds are consistent.
    pub(super) fn produced_type(&self, value: ValueId) -> Option<TypeId> {
        let state = &self.world.values[value];
        if state.lower == self.types.primitives().never
            || !self.types.is_subtype(state.lower, state.upper)
        {
            return None;
        }
        Some(state.lower)
    }

    /// Returns the best materializable candidate for one value.
    pub(super) fn candidate_type(&self, value: ValueId) -> Option<TypeId> {
        let state = &self.world.values[value];
        if state.lower != self.types.primitives().never {
            return self
                .types
                .is_subtype(state.lower, state.upper)
                .then_some(state.lower);
        }
        self.types
            .is_emittable_upper_bound(state.upper)
            .then_some(state.upper)
    }

    /// Collects concrete function signatures contained in `ty`.
    pub(super) fn collect_function_signatures(&self, ty: TypeId, output: &mut Vec<TypeId>) {
        match self.types.get(ty) {
            Type::FunctionSignature { .. } => output.push(ty),
            Type::Union(members) | Type::Intersection(members) => {
                for member in members {
                    self.collect_function_signatures(*member, output);
                }
            }
            Type::WithMetatable { methods, .. } => {
                for method in methods {
                    self.collect_function_signatures(method.ty, output);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::hil::ty2::{builtins::BuiltinEnvironment, store::TypeStore};
    use crate::hil::ty3::inference::{
        engine::Engine,
        keys::ValueKey,
        program::{InferenceProgram, ValueRelation},
    };
    use crate::il::ProtoId;

    /// Basic value flow reaches a fixed point through the agenda.
    #[test]
    fn value_flow_propagates_producer_evidence() {
        let mut store = TypeStore::new();
        let builtins = BuiltinEnvironment::new(&mut store);
        let source = ValueKey::Temp(ProtoId(0), 0);
        let target = ValueKey::Temp(ProtoId(0), 1);
        let number = store.primitives().number;
        let mut program = InferenceProgram::default();
        program.push_value(source, ValueRelation::Observe(number));
        program.push_value(target, ValueRelation::FlowFrom(source));

        let mut engine = Engine::new(program, &[], &builtins, &mut store);
        engine.solve();
        let target = engine
            .get_value_key(target)
            .expect("target value should be allocated");

        assert_eq!(engine.produced_type(target), Some(number));
    }
}
