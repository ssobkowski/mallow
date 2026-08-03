//! Queue-based fixed-point engine.

use std::collections::{HashMap, HashSet, VecDeque};

use smol_str::SmolStr;

use super::keys::{BranchPredicate, PackKey, ValueKey};
use super::program::{InferenceProgram, PackRelation, ValueRelation};
use super::world::{ObjectId, PackAlternative, PackId, ValueId, World, WorldChange};
use crate::hil::lifted::LiftedFunction;
use crate::hil::lifter::ssa::SymbolId;
use crate::hil::ty::builtins::{BuiltinEnvironment, BuiltinPath};
use crate::hil::ty::canonical::TypeId;
use crate::hil::ty::store::TypeStore;
use crate::il::ProtoId;
use crate::operator::{BinOp, UnOp};

/// One propagation rule applied by the engine.
///
/// Most rules come from a [`ValueRelation`]. The engine also creates some
/// rules while it discovers pack projections and concrete object identities.
#[derive(Debug, Clone)]
enum Rule {
    /// Adds `ty` to the types known to come from `value`.
    Produce { value: ValueId, ty: TypeId },
    /// Records that `value` must fit within `ty`.
    Require { value: ValueId, ty: TypeId },
    /// Sends type and identity facts from `source` to `target`.
    Flow { source: ValueId, target: ValueId },
    /// Sends produced types from `source` to `target`, except `nil`.
    NonNilFlow { source: ValueId, target: ValueId },
    /// Treats two values as aliases and sends facts in both directions.
    Same { lhs: ValueId, rhs: ValueId },
    /// Sends possible contents of one mutable storage cell in both directions.
    SameStorage { lhs: ValueId, rhs: ValueId },
    /// Sends the truthy or falsy part of `source` to `target`.
    Filter {
        /// Value being tested by the branch.
        source: ValueId,
        /// Value used inside the branch.
        target: ValueId,
        /// Branch test to apply.
        predicate: BranchPredicate,
    },
    /// Adds one concrete table identity to `value`.
    IncludeObject { value: ValueId, object: ObjectId },
    /// Adds one concrete closure identity to `value`.
    IncludeClosure { value: ValueId, proto: ProtoId },
    /// Adds one known builtin identity to `value`.
    IncludeBuiltin { value: ValueId, path: BuiltinPath },
    /// Keeps `output` equal to position `index` of every `pack` alternative.
    ProjectPack {
        /// Pack being read.
        pack: PackId,
        /// Zero-based position being read.
        index: usize,
        /// Value receiving the position.
        output: ValueId,
    },
    /// Collects every value that `pack` can produce into `output`.
    PackValues {
        /// Pack being collected.
        pack: PackId,
        /// Value receiving the collected types.
        output: ValueId,
    },
    /// Writes `value` into a named field on every known object.
    WriteField {
        /// Value carrying the objects.
        object: ValueId,
        /// Name of the field being written.
        field: SmolStr,
        /// Value written to the field.
        value: ValueId,
        /// Whether table construction definitely created the field.
        definite: bool,
    },
    /// Reads a named field from every known object into `output`.
    ReadField {
        /// Value carrying the objects.
        object: ValueId,
        /// Name of the field being read.
        field: SmolStr,
        /// Value receiving the field contents.
        output: ValueId,
    },
    /// Writes a dynamic index and value into every known object.
    WriteIndex {
        /// Value carrying the objects.
        object: ValueId,
        /// Value used as the index.
        index: ValueId,
        /// Value written at the index.
        value: ValueId,
    },
    /// Reads the dynamic values from every known object into `output`.
    ReadIndex {
        /// Value carrying the objects.
        object: ValueId,
        /// Value used as the index.
        index: ValueId,
        /// Value receiving the table contents.
        output: ValueId,
    },
    /// Connects a call to every closure identity known for its callee.
    Call {
        /// Value being called.
        callee: ValueId,
        /// Arguments supplied at the call site.
        args: PackId,
        /// Results received at the call site.
        returns: PackId,
    },
    /// Applies the type behavior of a binary operator.
    Binary {
        /// Left-hand value.
        lhs: ValueId,
        /// Operation being evaluated.
        op: BinOp,
        /// Right-hand value.
        rhs: ValueId,
        /// Value receiving the result.
        output: ValueId,
    },
    /// Applies the type behavior of a unary operator.
    Unary {
        /// Value being operated on.
        operand: ValueId,
        /// Operation being evaluated.
        op: UnOp,
        /// Value receiving the result.
        output: ValueId,
    },
}

/// One concrete connection installed by a dynamic rule.
///
/// A rule can say "for every object" or "for every closure" before the
/// engine knows which objects or closures exist. This set remembers each
/// connection that has already been installed, so running the rule again does
/// not install the same connection twice.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Activation {
    /// Connects one call argument to one closure parameter.
    CallParameter {
        /// Rule that owns the connection.
        rule: usize,
        /// Closure receiving the argument.
        proto: ProtoId,
        /// Zero-based parameter position.
        index: usize,
    },
    /// Connects one closure result to one call result.
    CallReturn {
        /// Rule that owns the connection.
        rule: usize,
        /// Closure producing the result.
        proto: ProtoId,
        /// Zero-based result position.
        index: usize,
    },
    /// Connects one named write to one concrete object.
    WriteField {
        /// Rule that owns the connection.
        rule: usize,
        /// Object receiving the field write.
        object: ObjectId,
    },
    /// Connects one named read to one concrete object.
    ReadField {
        /// Rule that owns the connection.
        rule: usize,
        /// Object providing the field value.
        object: ObjectId,
    },
    /// Connects one dynamic write to one concrete object.
    WriteIndex {
        /// Rule that owns the connection.
        rule: usize,
        /// Object receiving the indexed write.
        object: ObjectId,
    },
    /// Connects one dynamic read to one concrete object.
    ReadIndex {
        /// Rule that owns the connection.
        rule: usize,
        /// Object providing the indexed value.
        object: ObjectId,
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

/// Pending rule queue with duplicate suppression.
#[derive(Debug, Default)]
struct RuleQueue {
    queue: VecDeque<usize>,
    queued: HashSet<usize>,
}

impl RuleQueue {
    /// Adds one rule to the queue if it is not already pending.
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
    queue: RuleQueue,
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
        let (never, unknown) = (types.primitives().never, types.primitives().unknown);
        let mut engine = Self {
            types,
            world: World::new(never, unknown),
            functions,
            builtins,
            rules: Vec::new(),
            subscriptions: Subscriptions::default(),
            queue: RuleQueue::default(),
            activations: HashSet::new(),
            flow_rules: HashSet::new(),
        };
        engine.install_program(program);
        engine
    }

    /// Runs the queue until no subscribed fact changes.
    pub fn solve(&mut self) {
        while let Some(rule_id) = self.queue.pop() {
            // TODO: Figure out a way to get rid of this clone.
            let rule = self.rules[rule_id].clone();
            self.apply(rule_id, rule);
        }
    }

    /// Returns every allocated symbol key.
    pub fn symbol_keys(&self) -> Vec<(ProtoId, SymbolId, ValueKey)> {
        self.world
            .value_keys()
            .filter_map(|(key, _)| match key {
                ValueKey::Symbol(proto, symbol) => Some((proto, symbol, key)),
                ValueKey::Temp(_, _) | ValueKey::Occurrence(_, _, _) => None,
            })
            .collect()
    }

    /// Returns or creates the value for `key`.
    #[inline]
    pub(super) fn value_for_key(&mut self, key: ValueKey) -> ValueId {
        self.world.value_for_key(key)
    }

    /// Returns or creates the pack for `key`.
    #[inline]
    pub(super) fn pack_for_key(&mut self, key: PackKey) -> PackId {
        self.world.pack_for_key(key)
    }

    /// Returns the value ID for a key if it exists.
    #[inline]
    pub(super) fn get_value_key(&self, key: ValueKey) -> Option<ValueId> {
        self.world.get_value_key(key)
    }

    /// Adds one rule and subscribes it to its direct inputs.
    #[inline]
    fn add_rule(&mut self, rule: Rule) -> usize {
        let id = self.rules.len();
        self.subscribe_rule(id, &rule);
        self.rules.push(rule);
        self.queue.push(id);
        id
    }

    /// Adds a flow rule once.
    #[inline]
    fn add_flow_rule(&mut self, source: ValueId, target: ValueId) {
        if self.flow_rules.insert((source, target, FlowKind::Full)) {
            self.add_rule(Rule::Flow { source, target });
        }
    }

    /// Adds a non-nil flow rule once.
    #[inline]
    fn add_non_nil_flow_rule(&mut self, source: ValueId, target: ValueId) {
        if self.flow_rules.insert((source, target, FlowKind::NonNil)) {
            self.add_rule(Rule::NonNilFlow { source, target });
        }
    }

    /// Registers the facts that can wake `rule`.
    #[inline]
    fn subscribe_rule(&mut self, id: usize, rule: &Rule) {
        match rule {
            Rule::Produce { .. }
            | Rule::Require { .. }
            | Rule::IncludeObject { .. }
            | Rule::IncludeClosure { .. }
            | Rule::IncludeBuiltin { .. } => {}
            Rule::Flow { source, target } | Rule::NonNilFlow { source, target } => {
                self.subscriptions.value(*source, id);
                self.subscriptions.value(*target, id);
            }
            Rule::Same { lhs, rhs } | Rule::SameStorage { lhs, rhs } => {
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
                            .iter()
                            .copied()
                            .map(|key| self.world.value_for_key(key))
                            .collect();
                        let tail = tail.as_ref().map(|key| self.world.pack_for_key(*key));
                        if let WorldChange::Changed(()) = self
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
                self.add_rule(Rule::Produce { value, ty: *ty });
                self.add_rule(Rule::Require { value, ty: *ty });
            }
        }
    }

    /// Installs one scalar relation as one or more engine rules.
    #[inline]
    fn install_value_relation(&mut self, value: ValueId, relation: &ValueRelation) {
        match relation {
            ValueRelation::Produce(ty) => {
                self.add_rule(Rule::Produce { value, ty: *ty });
            }
            ValueRelation::Require(ty) => {
                self.add_rule(Rule::Require { value, ty: *ty });
            }
            ValueRelation::FlowFrom(source) => {
                let source = self.world.value_for_key(*source);
                self.add_flow_rule(source, value);
            }
            ValueRelation::SameAs(other) => {
                let other = self.world.value_for_key(*other);
                self.add_rule(Rule::Same {
                    lhs: value,
                    rhs: other,
                });
            }
            ValueRelation::SameStorage(other) => {
                let other = self.world.value_for_key(*other);
                self.add_rule(Rule::SameStorage {
                    lhs: value,
                    rhs: other,
                });
            }
            ValueRelation::FromPack { pack, index } => {
                let pack = self.world.pack_for_key(*pack);
                let projection = self.ensure_projection(pack, *index);
                self.add_flow_rule(projection, value);
            }
            ValueRelation::FromPackValues { pack } => {
                let pack = self.world.pack_for_key(*pack);
                let aggregate = self.ensure_pack_values(pack);
                self.add_flow_rule(aggregate, value);
            }
            ValueRelation::Filter { source, predicate } => {
                let source = self.world.value_for_key(*source);
                self.add_rule(Rule::Filter {
                    source,
                    target: value,
                    predicate: *predicate,
                });
            }
            ValueRelation::NewObject(key) => {
                let object = self.world.object_for_key(*key);
                self.add_rule(Rule::IncludeObject { value, object });
            }
            ValueRelation::Closure(proto) => {
                self.add_rule(Rule::IncludeClosure {
                    value,
                    proto: *proto,
                });
            }
            ValueRelation::Builtin(path) => {
                self.add_rule(Rule::IncludeBuiltin {
                    value,
                    path: path.clone(),
                });
            }
            ValueRelation::WriteField {
                field,
                value: source,
                definite,
            } => {
                let source = self.world.value_for_key(*source);
                self.add_rule(Rule::WriteField {
                    object: value,
                    field: field.clone(),
                    value: source,
                    definite: *definite,
                });
            }
            ValueRelation::ReadField { field, output } => {
                let output = self.world.value_for_key(*output);
                self.add_rule(Rule::ReadField {
                    object: value,
                    field: field.clone(),
                    output,
                });
            }
            ValueRelation::WriteIndex {
                index,
                value: source,
            } => {
                let index = self.world.value_for_key(*index);
                let source = self.world.value_for_key(*source);
                self.add_rule(Rule::WriteIndex {
                    object: value,
                    index,
                    value: source,
                });
            }
            ValueRelation::ReadIndex { index, output } => {
                let index = self.world.value_for_key(*index);
                let output = self.world.value_for_key(*output);
                self.add_rule(Rule::ReadIndex {
                    object: value,
                    index,
                    output,
                });
            }
            ValueRelation::Call { args, returns } => {
                let args = self.world.pack_for_key(*args);
                let returns = self.world.pack_for_key(*returns);
                self.add_rule(Rule::Call {
                    callee: value,
                    args,
                    returns,
                });
            }
            ValueRelation::Binary { op, rhs, output } => {
                let rhs = self.world.value_for_key(*rhs);
                let output = self.world.value_for_key(*output);
                self.add_rule(Rule::Binary {
                    lhs: value,
                    op: *op,
                    rhs,
                    output,
                });
            }
            ValueRelation::Unary { op, output } => {
                let output = self.world.value_for_key(*output);
                self.add_rule(Rule::Unary {
                    operand: value,
                    op: *op,
                    output,
                });
            }
        }
    }

    /// Applies one rule.
    #[inline]
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
            Rule::Same { lhs, rhs } | Rule::SameStorage { lhs, rhs } => {
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

    /// Adds one produced type to a value.
    #[inline]
    fn produce(&mut self, value: ValueId, ty: TypeId) {
        let old = self.world.values[value].lower;
        let next = self.types.join(old, ty);
        if old == next {
            return;
        }
        self.world.values[value].lower = next;
        self.value_changed(value);
    }

    /// Adds one type that a value must support.
    #[inline]
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
    #[inline]
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
        for path in source_state.identities.builtins {
            self.include_builtin(target, path);
        }
    }

    /// Copies producer facts after removing `nil`.
    #[inline]
    fn non_nil_flow(&mut self, source: ValueId, target: ValueId) {
        let lower = self.world.values[source].lower;
        let non_nil = self.types.exclude(lower, &[self.types.primitives().nil]);
        self.produce(target, non_nil);
    }

    /// Applies branch filtering when a produced type exists.
    #[inline]
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
            for path in identities.builtins {
                self.include_builtin(target, path);
            }
        }
    }

    /// Adds one object identity to a value.
    #[inline]
    fn include_object(&mut self, value: ValueId, object: ObjectId) {
        if !self.world.values[value].identities.objects.insert(object) {
            return;
        }
        self.value_changed(value);
    }

    /// Adds one closure identity to a value.
    #[inline]
    fn include_closure(&mut self, value: ValueId, proto: ProtoId) {
        if !self.world.values[value].identities.closures.insert(proto) {
            return;
        }
        self.value_changed(value);
    }

    /// Adds one builtin identity to a value.
    #[inline]
    fn include_builtin(&mut self, value: ValueId, path: BuiltinPath) {
        if self.builtins.get_path(&path).is_none() {
            return;
        }
        if !self.world.values[value].identities.builtins.insert(path) {
            return;
        }
        self.value_changed(value);
    }

    /// Wires a pack projection to every current alternative.
    #[inline]
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
                self.produce(output, self.types.primitives().nil);
            }
        }
    }

    /// Wires an aggregate pack value to every current alternative.
    #[inline]
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
            match self.world.object_field(target, field.clone(), definite) {
                WorldChange::Unchanged(field_value) => self.add_flow_rule(value, field_value),
                WorldChange::Changed(field_value) => {
                    self.add_flow_rule(value, field_value);
                    self.object_changed(target);
                }
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
            match self.world.object_field(source, field.clone(), false) {
                WorldChange::Unchanged(field_value) => self.add_flow_rule(field_value, output),
                WorldChange::Changed(field_value) => {
                    self.add_flow_rule(field_value, output);
                    self.object_changed(source);
                }
            }
            self.produce(output, self.types.primitives().nil);
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
            self.produce(output, self.types.primitives().nil);
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

            for (index, parameter) in function.symbols.params().iter().copied().enumerate() {
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
    #[inline]
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

    /// Returns a stable aggregate value and installs its maintenance rule.
    #[inline]
    fn ensure_pack_values(&mut self, pack: PackId) -> ValueId {
        match self.world.pack_values(pack) {
            WorldChange::Unchanged(value) => value,
            WorldChange::Changed(value) => {
                self.add_rule(Rule::PackValues {
                    pack,
                    output: value,
                });
                self.pack_changed(pack);
                value
            }
        }
    }

    /// Returns the types known to come from a value, including identity types.
    #[inline]
    fn evidence_type(&mut self, value: ValueId) -> Option<TypeId> {
        let state = self.world.values[value].clone();
        let mut evidence = state.lower;
        if !state.identities.objects.is_empty() {
            evidence = self.types.join(evidence, self.types.primitives().table);
        }
        if !state.identities.closures.is_empty() || !state.identities.builtins.is_empty() {
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

    /// Re-enqueues every rule subscribed to a changed object.
    #[inline]
    fn object_changed(&mut self, object: ObjectId) {
        if let Some(rules) = self.subscriptions.objects.get(&object) {
            self.queue.extend(rules.iter().copied());
        }
    }

    /// Returns the best materializable candidate for one value.
    #[inline]
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
