//! Fixed-point engine and invariant-preserving solver operations.

mod calls;
mod heap;
mod model;
mod operators;
mod output;
mod packs;
mod tables;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use id_arena::Arena;

use crate::hil::{
    lifted::LiftedFunction,
    ty2::{
        builtins::{BuiltinEnvironment, BuiltinPath},
        canonical::{Type, TypeId},
        inference::queue::WorkQueue,
        store::TypeStore,
    },
};
use crate::il::ProtoId;

use super::program::{
    CollectedCallArgument, CollectedConstraint, CollectedPackConstraint, CollectedProgram,
    Truthiness, TypeSlot,
};
use model::{
    CallSite, ConstraintRecord, DeferredRefinement, InferenceVarId, InferenceVariable,
    PackAlternative, PackVariable, SolverCallArgument, SolverConstraint, TableObjectId,
};

pub(super) use model::TypeSolver;

impl<'a> TypeSolver<'a> {
    /// Builds solver arenas over the shared canonical graph and seeds durable slots.
    pub(super) fn new(
        program: CollectedProgram,
        functions: &'a [LiftedFunction],
        builtins: &'a BuiltinEnvironment,
        type_store: &'a mut TypeStore,
        seeds: HashMap<TypeSlot, Vec<TypeId>>,
    ) -> Self {
        let mut solver = Self {
            types: type_store,
            variables: Arena::new(),
            variables_by_slot: HashMap::new(),
            packs: Arena::<PackVariable>::new(),
            packs_by_slot: HashMap::new(),
            pack_uses: HashMap::new(),
            pack_dependents: HashMap::new(),
            output_pack_views: HashMap::new(),
            constraints: HashMap::new(),
            dependencies: HashMap::new(),
            queue: WorkQueue::new(),
            tables: Arena::new(),
            tables_by_key: HashMap::new(),
            table_users: HashMap::new(),
            functions,
            builtins,
            generic_field_calls: program.generic_field_calls,
            generic_value_relations: program.generic_value_relations,
            closure_argument_packs: HashMap::new(),
            callsites: Vec::new(),
            deferred_callable_requirements: HashMap::new(),
            callsites_by_callee: HashMap::new(),
            activated_closures: HashSet::new(),
            activated_builtins: HashSet::new(),
            deferred_builtin_effects: HashSet::new(),
            activated_builtin_effects: HashSet::new(),
            activated_call_signatures: HashSet::new(),
            activated_table_constraints: HashSet::new(),
            activated_index_dispatches: HashSet::new(),
            activated_dynamic_fields: HashSet::new(),
            deferred_refinements: HashMap::new(),
            activated_refinement_fallbacks: HashSet::new(),
            deferred_operators: HashMap::new(),
            activated_operator_fallbacks: HashSet::new(),
            next_constraint_id: 0,
        };

        for slot in program.pack_constraints.keys().copied() {
            solver.pack_for_slot(slot);
        }
        for (slot, constraints) in program.pack_constraints {
            let pack = solver.pack_for_slot(slot);
            for constraint in constraints {
                match constraint {
                    CollectedPackConstraint::Sequence { head, tail } => {
                        let head = head
                            .into_iter()
                            .map(|slot| solver.variable_for_slot(slot))
                            .collect();
                        let tail = tail.map(|slot| solver.pack_for_slot(slot));
                        solver.include_pack_alternative(pack, PackAlternative { head, tail });
                    }
                }
            }
        }
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
                solver.add_constraint(variable, SolverConstraint::Observe(ty));
                solver.add_constraint(variable, SolverConstraint::Require(ty));
            }
        }
        solver
    }

    /// Returns every durable symbol slot currently represented by the solver.
    pub(in crate::hil::ty2::inference) fn symbol_slots(
        &self,
    ) -> Vec<(ProtoId, crate::hil::lifter::ssa::SymbolId, TypeSlot)> {
        let mut slots: Vec<_> = self
            .variables_by_slot
            .keys()
            .filter_map(|slot| match slot {
                TypeSlot::Symbol(proto, symbol) => Some((*proto, *symbol, *slot)),
                _ => None,
            })
            .collect();
        slots.sort_by_key(|(proto, symbol, _)| (proto.0, symbol.index()));
        slots
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
            CollectedConstraint::Concrete(ty) => {
                self.add_constraint(variable, SolverConstraint::Observe(ty));
            }
            CollectedConstraint::From(source) => {
                let source = self.variable_for_slot(source);
                self.add_constraint(variable, SolverConstraint::FlowFrom(source));
            }
            CollectedConstraint::Equal(other) => {
                let other = self.variable_for_slot(other);
                self.add_constraint(variable, SolverConstraint::Equal(other));
            }
            CollectedConstraint::FromPack { pack, index } => {
                let pack = self.pack_for_slot(pack);
                let source = self.project_pack(pack, index);
                self.add_constraint(variable, SolverConstraint::FlowFrom(source));
            }
            CollectedConstraint::Narrowed { source, truthiness } => {
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
            CollectedConstraint::SetIndexPack { values } => {
                let values = self.pack_for_slot(values);
                self.add_constraint(variable, SolverConstraint::SetIndexPack { values });
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
                let args = self.pack_for_slot(args);
                let returns = self.pack_for_slot(returns);
                self.add_constraint(variable, SolverConstraint::Call { args, returns });
            }
            CollectedConstraint::FieldCall {
                callee,
                head,
                tail,
                returns,
            } => {
                let head = head
                    .into_iter()
                    .map(|argument| match argument {
                        CollectedCallArgument::Value(slot) => {
                            SolverCallArgument::Value(self.variable_for_slot(slot))
                        }
                        CollectedCallArgument::Field(field) => SolverCallArgument::Field(field),
                    })
                    .collect();
                let tail = tail.map(|slot| self.pack_for_slot(slot));
                let returns = self.pack_for_slot(returns);
                self.add_constraint(
                    variable,
                    SolverConstraint::FieldCall {
                        callee,
                        head,
                        tail,
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

    /// Adds one native constraint unless the same relation is already present.
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
            let argument_values = self.pack_values(*args);
            self.dependencies
                .entry(argument_values)
                .or_default()
                .insert(variable);
            let return_projections: Vec<_> =
                self.packs[*returns].projections.values().copied().collect();
            for projection in return_projections {
                self.dependencies
                    .entry(projection)
                    .or_default()
                    .insert(variable);
            }
            let call_id = self.callsites.len();
            self.callsites.push(CallSite {
                callee: variable,
                args: *args,
                returns: *returns,
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
            SolverConstraint::SetIndexPack { values } => {
                self.pack_dependents
                    .entry(*values)
                    .or_default()
                    .insert(primary);
            }
            SolverConstraint::SetField { value, .. }
            | SolverConstraint::GetField { value, .. }
            | SolverConstraint::Unary { result: value, .. } => depend_on(*value),
            SolverConstraint::Binary { rhs, result, .. } => {
                depend_on(*rhs);
                depend_on(*result);
            }
            SolverConstraint::Call { args, returns } => {
                self.pack_dependents
                    .entry(*args)
                    .or_default()
                    .insert(primary);
                self.pack_dependents
                    .entry(*returns)
                    .or_default()
                    .insert(primary);
            }
            SolverConstraint::FieldCall {
                head,
                tail,
                returns,
                ..
            } => {
                for argument in head {
                    if let SolverCallArgument::Value(variable) = argument {
                        depend_on(*variable);
                    }
                }
                if let Some(tail) = tail {
                    self.pack_dependents
                        .entry(*tail)
                        .or_default()
                        .insert(primary);
                }
                self.pack_dependents
                    .entry(*returns)
                    .or_default()
                    .insert(primary);
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
    pub(super) fn solve(&mut self) {
        loop {
            self.drain_queue();
            if self.activate_deferred_builtin_effects() {
                continue;
            }
            if self.activate_deferred_operators() {
                continue;
            }
            if self.activate_deferred_callable_requirements() {
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
            SolverConstraint::SetIndexPack { values } => {
                let index = self.fresh_variable();
                self.add_constraint(
                    index,
                    SolverConstraint::Observe(self.types.primitives().number),
                );
                let value = self.pack_values(values);
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
                self.deferred_callable_requirements.insert(
                    record.id,
                    CallSite {
                        callee: variable,
                        args,
                        returns,
                    },
                );
                self.apply_callable_signature(record.id, variable, args, returns);
                self.connect_call_metamethod(variable, args, returns);
                self.activate_calls(variable);
            }
            SolverConstraint::FieldCall {
                callee,
                head,
                tail,
                returns,
            } => self.apply_field_call(record.id, variable, callee, &head, tail, returns),
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
    fn observe(&mut self, variable: InferenceVarId, ty: TypeId) -> bool {
        let old = self.variables[variable].lower;
        let next = self.types.join(old, ty);
        if old == next {
            return false;
        }
        self.variables[variable].lower = next;
        self.variable_changed(variable);
        true
    }

    /// Adds a consumer requirement to a variable's upper bound.
    fn require(&mut self, variable: InferenceVarId, ty: TypeId) -> bool {
        let old = self.variables[variable].upper;
        let next = self.types.meet(old, ty);
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

    /// Adds a builtin scheme identity for callsite activation.
    fn include_builtin(&mut self, variable: InferenceVarId, path: BuiltinPath) -> bool {
        if !self.variables[variable].builtins.insert(path.clone()) {
            return false;
        }
        // The call domain imports and instantiates the scheme when a callsite
        // activates; this identity record must not copy foreign graph IDs.
        let _ = self.builtins.get_path(&path);
        self.variable_changed(variable);
        true
    }

    /// Returns a consistent produced type, excluding consumer-only inference.
    fn produced_type(&self, variable: InferenceVarId) -> Option<TypeId> {
        let facts = &self.variables[variable];
        if facts.lower == self.types.primitives().never
            || !self.types.is_subtype(facts.lower, facts.upper)
        {
            return None;
        }
        Some(facts.lower)
    }

    /// Returns the best consistent candidate from lower and upper bounds.
    fn candidate_type(&self, variable: InferenceVarId) -> Option<TypeId> {
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

    /// Returns whether unresolved evidence can conservatively default to `primitive`.
    fn can_default_to(&self, variable: InferenceVarId, primitive: TypeId) -> bool {
        let facts = &self.variables[variable];
        if !facts.tables.is_empty() || !facts.closures.is_empty() || !facts.builtins.is_empty() {
            return false;
        }
        self.lower_defaults_to(facts.lower, primitive)
    }

    /// Returns whether `lower` differs from `primitive` only by nil or dynamic evidence.
    fn lower_defaults_to(&self, lower: TypeId, primitive: TypeId) -> bool {
        match self.types.get(lower) {
            Type::Never | Type::Nil | Type::Unknown | Type::Any => true,
            Type::Union(members) => members
                .iter()
                .all(|member| self.lower_defaults_to(*member, primitive)),
            _ => self.types.is_subtype(lower, primitive),
        }
    }

    /// Returns runtime evidence, adding broad markers for identity-only domains.
    fn evidence_type(&mut self, variable: InferenceVarId) -> Option<TypeId> {
        let facts = self.variables[variable].clone();
        let never = self.types.primitives().never;
        let table = self.types.primitives().table;
        let function = self.types.primitives().function;
        let mut evidence = facts.lower;
        if !facts.tables.is_empty() {
            evidence = self.types.join(evidence, table);
        }
        if !facts.closures.is_empty() || !facts.builtins.is_empty() {
            evidence = self.types.join(evidence, function);
        }
        (evidence != never).then_some(evidence)
    }
}
