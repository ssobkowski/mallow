//! Closure calls, builtin schemes, and generic instantiation.

use std::collections::HashMap;

use smol_str::SmolStr;

use crate::{
    hil::ty2::{
        builtins::{BuiltinCallEffect, BuiltinIndex, BuiltinPath},
        canonical::{GenericBinder, Metamethod, Type, TypeId, TypePackTail, TypeScheme},
        inference::{program::TypeSlot, solver::model::Activation},
    },
    il::ProtoId,
};

use super::model::{
    CallSite, InferenceVarId, PackAlternative, PackVarId, SolverConstraint, TypeSolver,
};

impl TypeSolver<'_> {
    /// Activates newly discovered closure and builtin targets for `callee`.
    pub(super) fn activate_calls(&mut self, callee: InferenceVarId) {
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
                if self
                    .activations
                    .insert(call_id, Activation::Closure(*proto))
                {
                    self.connect_call_to_proto(&call, *proto);
                }
            }
            for path in &builtins {
                let (minimum, maximum) = self.pack_arity(call.args);
                let argument_types = self.call_argument_types(call.args, minimum, maximum);
                if self.activations.insert(
                    call_id,
                    Activation::Builtin {
                        path: path.clone(),
                        minimum,
                        maximum,
                        argument_types,
                    },
                ) {
                    self.instantiate_builtin(&call, path);
                }
                if !self
                    .activations
                    .contains(call_id, &Activation::BuiltinEffect(path.clone()))
                {
                    self.deferred_builtin_effects
                        .insert((call_id, path.clone()));
                }
            }
        }
    }

    /// Returns the current producer type at every arity-relevant argument position.
    fn call_argument_types(
        &mut self,
        args: PackVarId,
        minimum: usize,
        maximum: Option<usize>,
    ) -> Vec<Option<TypeId>> {
        let count = maximum.unwrap_or(minimum);
        (0..count)
            .map(|index| {
                let argument = self.project_pack(args, index);
                self.produced_type(argument)
            })
            .collect()
    }

    /// Activates builtin heap effects after ordinary pack propagation is quiescent.
    pub(super) fn activate_deferred_builtin_effects(&mut self) -> bool {
        let mut deferred: Vec<_> = std::mem::take(&mut self.deferred_builtin_effects)
            .into_iter()
            .collect();
        deferred.sort();
        let mut activated = false;
        for (call_id, path) in deferred {
            if !self
                .activations
                .insert(call_id, Activation::BuiltinEffect(path.clone()))
            {
                continue;
            }
            let Some(call) = self.callsites.get(call_id).cloned() else {
                continue;
            };
            let (minimum, maximum) = self.pack_arity(call.args);
            for effect in path.call_effects(minimum, maximum) {
                self.apply_builtin_effect(&call, effect);
                activated = true;
            }
        }
        activated
    }

    /// Connects one callsite to one concrete lifted closure.
    fn connect_call_to_proto(&mut self, call: &CallSite, proto: ProtoId) {
        let Some(function) = self.functions.get(proto.0 as usize) else {
            return;
        };
        let params = function.symbols.params.clone();
        let is_vararg = function.is_vararg;
        self.closure_argument_packs
            .entry(proto)
            .or_default()
            .insert(call.args);
        for (parameter_index, parameter) in params.iter().copied().enumerate() {
            let formal = self.variable_for_slot(TypeSlot::Symbol(proto, parameter));
            let argument = self.project_pack(call.args, parameter_index);
            self.add_constraint(formal, SolverConstraint::FlowFrom(argument));
        }
        if is_vararg {
            let varargs = self.pack_for_slot(super::super::program::PackSlot::VarArgs(proto));
            self.add_pack_suffix(varargs, call.args, params.len());
        }

        let returned = self.pack_for_slot(super::super::program::PackSlot::Returns(proto));
        let relations = self
            .body_value_relations
            .get(&proto)
            .cloned()
            .unwrap_or_default();
        let prefix_len = relations
            .iter()
            .map(|relation| relation.return_index + 1)
            .max()
            .unwrap_or(0);
        if prefix_len == 0 {
            self.add_pack_flow(call.returns, returned);
        } else {
            let mut head = Vec::with_capacity(prefix_len);
            for return_index in 0..prefix_len {
                let value = if let Some(relation) = relations
                    .iter()
                    .find(|relation| relation.return_index == return_index)
                {
                    self.project_pack(call.args, relation.parameter_index)
                } else {
                    self.project_pack(returned, return_index)
                };
                head.push(value);
            }
            let tail = self.pack_suffix(returned, prefix_len);
            self.include_pack_alternative(
                call.returns,
                PackAlternative {
                    head,
                    tail: Some(tail),
                },
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
                let table = self.project_pack(call.args, table_argument);
                let value = self.project_pack(call.args, value_argument);
                let index = match index {
                    BuiltinIndex::Argument(argument) => self.project_pack(call.args, argument),
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
                let table = self.project_pack(call.args, table_argument);
                let metatable = self.project_pack(call.args, metatable_argument);
                let result = self.project_pack(call.returns, 0);
                self.add_constraint(
                    table,
                    SolverConstraint::SetMetatable {
                        metatable,
                        result: Some(result),
                    },
                );
            }
        }
    }

    /// Instantiates one builtin scheme at one callsite.
    pub(super) fn instantiate_builtin(&mut self, call: &CallSite, path: &BuiltinPath) {
        let Some(scheme) = self.builtins.get_path(path).cloned() else {
            return;
        };
        let alternatives = match self.types.get(scheme.body()) {
            Type::Intersection(types) => types.clone(),
            _ => vec![scheme.body()],
        };
        let mut viable: Vec<_> = alternatives
            .into_iter()
            .filter(|alternative| self.function_accepts_pack(*alternative, call.args))
            .collect();

        if viable.len() > 1 {
            viable.retain(|alternative| self.signature_may_accept(*alternative, call.args));
        }
        if viable.len() == 1 {
            self.instantiate_function_scheme(call, &scheme, viable[0]);
        } else {
            self.observe_common_overload_returns(call, &viable);
        }
    }

    /// Returns whether a function scheme accepts at least one possible pack arity.
    fn function_accepts_pack(&self, scheme: TypeId, args: PackVarId) -> bool {
        let Type::FunctionSignature { params, .. } = self.types.get(scheme) else {
            return false;
        };
        let params = self.types.get_pack(*params);
        let fixed = params.head.len();
        let optional = params
            .head
            .iter()
            .rev()
            .take_while(|ty| self.types.accepts_nil(**ty))
            .count();
        let accepted_minimum = fixed - optional;
        let accepted_maximum = params.tail.is_none().then_some(fixed);
        let (actual_minimum, actual_maximum) = self.pack_arity(args);
        actual_maximum.is_none_or(|maximum| maximum >= accepted_minimum)
            && accepted_maximum.is_none_or(|maximum| actual_minimum <= maximum)
    }

    /// Returns whether current producer facts do not contradict a structural signature.
    fn signature_may_accept(&mut self, scheme: TypeId, args: PackVarId) -> bool {
        let Type::FunctionSignature { params, .. } = self.types.get(scheme) else {
            return false;
        };
        let params = self.types.get_pack(*params).clone();
        let guaranteed = self.pack_arity(args).0;
        for index in 0..guaranteed {
            let argument = self.project_pack(args, index);
            let Some(parameter) = params.head.get(index).copied().or_else(|| {
                params
                    .tail
                    .as_ref()
                    .and_then(TypePackTail::homogeneous_type)
            }) else {
                continue;
            };
            if self.types.contains_generic(parameter) {
                continue;
            }
            let Some(argument) = self.produced_type(argument) else {
                continue;
            };
            if !self.types.is_subtype(argument, parameter) {
                return false;
            }
        }
        true
    }

    /// Instantiates one selected function scheme with fresh generic variables and packs.
    fn instantiate_function_scheme(&mut self, call: &CallSite, scheme: &TypeScheme, body: TypeId) {
        let (params_id, returns_id) = match self.types.get(body) {
            Type::FunctionSignature { params, returns } => (*params, *returns),
            _ => return,
        };
        let binders = scheme.binders().to_vec();
        let generic_variables: HashMap<_, _> = binders
            .iter()
            .filter_map(|binder| match binder {
                GenericBinder::Type(name) => Some((name.clone(), self.fresh_variable())),
                GenericBinder::Pack(_) => None,
            })
            .collect();
        let params = self.types.get_pack(params_id).clone();
        let returns = self.types.get_pack(returns_id).clone();

        let mut fixed_index = 0usize;
        for pattern in params.head {
            let argument = self.project_pack(call.args, fixed_index);
            self.bind_argument_pattern(argument, pattern, &generic_variables);
            fixed_index += 1;
        }
        let mut generic_packs = HashMap::new();
        if let Some(tail) = params.tail {
            let arguments = self.pack_suffix(call.args, fixed_index);
            match tail {
                TypePackTail::Homogeneous(pattern) => {
                    let argument = self.pack_values(arguments);
                    self.bind_argument_pattern(argument, pattern, &generic_variables);
                }
                TypePackTail::Generic(name) => {
                    generic_packs.insert(name, arguments);
                }
            }
        }

        let mut head = Vec::with_capacity(returns.head.len());
        for pattern in returns.head {
            let target = self.fresh_variable();
            self.emit_return_pattern(target, pattern, &generic_variables);
            head.push(target);
        }
        let tail = match returns.tail {
            Some(TypePackTail::Homogeneous(pattern)) => {
                let value = self.fresh_variable();
                self.emit_return_pattern(value, pattern, &generic_variables);
                let tail = self.fresh_pack();
                self.include_homogeneous_pack(tail, value);
                Some(tail)
            }
            Some(TypePackTail::Generic(name)) => Some(
                generic_packs
                    .get(&name)
                    .copied()
                    .unwrap_or_else(|| self.fresh_pack()),
            ),
            None => None,
        };
        self.include_pack_alternative(call.returns, PackAlternative { head, tail });
    }

    /// Applies one parameter pattern to an actual argument.
    fn bind_argument_pattern(
        &mut self,
        argument: InferenceVarId,
        pattern: TypeId,
        generics: &HashMap<SmolStr, InferenceVarId>,
    ) {
        let node = self.types.get(pattern).clone();
        match node {
            Type::Generic(name) => {
                if let Some(generic) = generics.get(&name) {
                    self.add_constraint(*generic, SolverConstraint::FlowFrom(argument));
                }
            }
            Type::TableShape { fields, indexer } => {
                let tables: Vec<_> = self.variables[argument].tables.iter().copied().collect();
                for table in tables {
                    if let Some((key_pattern, value_pattern)) = indexer {
                        let keys = self.tables[table].keys;
                        let values = self.tables[table].values;
                        self.bind_argument_pattern(keys, key_pattern, generics);
                        self.bind_argument_pattern(values, value_pattern, generics);
                    }
                    for (name, pattern) in &fields {
                        let value = self.table_field_variable(table, name.clone(), false);
                        self.bind_argument_pattern(value, *pattern, generics);
                    }
                }
            }
            Type::Union(members) => {
                let generic_members: Vec<_> = members
                    .iter()
                    .filter_map(|member| match self.types.get(*member) {
                        Type::Generic(name) => generics.get(name).copied(),
                        _ => None,
                    })
                    .collect();
                let concrete: Vec<_> = members
                    .iter()
                    .copied()
                    .filter(|member| !matches!(self.types.get(*member), Type::Generic(_)))
                    .collect();
                if generic_members.is_empty() {
                    self.add_constraint(argument, SolverConstraint::Require(pattern));
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
            _ if !self.types.contains_generic(pattern) => {
                self.add_constraint(argument, SolverConstraint::Require(pattern));
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
        pattern: TypeId,
        generics: &HashMap<SmolStr, InferenceVarId>,
    ) {
        match self.types.get(pattern).clone() {
            Type::Generic(name) => {
                if let Some(generic) = generics.get(&name) {
                    self.add_constraint(target, SolverConstraint::FlowFrom(*generic));
                }
            }
            Type::Union(members) => {
                for member in members {
                    self.emit_return_pattern(target, member, generics);
                }
            }
            _ if !self.types.contains_generic(pattern) => {
                self.add_constraint(target, SolverConstraint::Observe(pattern));
            }
            _ => {}
        }
    }

    /// Observes only return types shared safely across unresolved overloads.
    fn observe_common_overload_returns(&mut self, call: &CallSite, alternatives: &[TypeId]) {
        let packs: Vec<_> = alternatives
            .iter()
            .filter_map(|alternative| match self.types.get(*alternative) {
                Type::FunctionSignature { returns, .. } => {
                    Some(self.types.get_pack(*returns).clone())
                }
                _ => None,
            })
            .collect();
        let head_len = packs.iter().map(|pack| pack.head.len()).max().unwrap_or(0);
        let mut head = Vec::with_capacity(head_len);
        for index in 0..head_len {
            let mut returned = Vec::new();
            for pack in &packs {
                let ty = pack
                    .head
                    .get(index)
                    .copied()
                    .or_else(|| pack.tail.as_ref().and_then(TypePackTail::homogeneous_type));
                let Some(ty) = ty else {
                    returned.push(self.types.primitives().nil);
                    continue;
                };
                if self.types.contains_generic(ty) {
                    returned.clear();
                    break;
                }
                returned.push(ty);
            }
            let target = self.fresh_variable();
            if !returned.is_empty() {
                let returned = self.types.join_all(returned);
                self.observe(target, returned);
            }
            head.push(target);
        }
        let has_generic_tail = packs
            .iter()
            .any(|pack| matches!(pack.tail, Some(TypePackTail::Generic(_))));
        let tail_types: Vec<_> = packs
            .iter()
            .filter_map(|pack| pack.tail.as_ref()?.homogeneous_type())
            .filter(|ty| !self.types.contains_generic(*ty))
            .collect();
        let tail = if has_generic_tail {
            Some(self.fresh_pack())
        } else if tail_types.is_empty() {
            None
        } else {
            let value = self.fresh_variable();
            let returned = self.types.join_all(tail_types);
            self.observe(value, returned);
            let tail = self.fresh_pack();
            self.include_homogeneous_pack(tail, value);
            Some(tail)
        };
        if !head.is_empty() || tail.is_some() {
            self.include_pack_alternative(call.returns, PackAlternative { head, tail });
        }
    }

    /// Applies producer-free callable requirements after concrete identities settle.
    pub(super) fn activate_deferred_callable_requirements(&mut self) -> bool {
        let mut deferred: Vec<_> = std::mem::take(&mut self.deferred_callable_requirements)
            .into_iter()
            .collect();
        deferred.sort_by_key(|(constraint_id, _)| *constraint_id);
        let mut changed = false;
        for (_, call) in deferred {
            changed |= self.infer_callable_requirement(call.callee, call.args, call.returns);
        }
        changed
    }

    /// Infers a callable upper bound from one otherwise dynamic fixed-shape callsite.
    fn infer_callable_requirement(
        &mut self,
        callee: InferenceVarId,
        args: PackVarId,
        returns: PackVarId,
    ) -> bool {
        let facts = &self.variables[callee];
        if !facts.tables.is_empty() || !facts.closures.is_empty() || !facts.builtins.is_empty() {
            return false;
        }
        if !matches!(
            self.types.get(facts.lower),
            Type::Never | Type::Unknown | Type::Any
        ) {
            return false;
        }
        let (minimum, maximum) = self.pack_arity(args);
        let Some(exact_arity) = maximum.filter(|maximum| *maximum == minimum) else {
            return false;
        };
        let projections_ready =
            (0..exact_arity).all(|index| self.packs[args].projections.contains_key(&index));
        let Some(args) = self.exact_pack_values(args) else {
            return false;
        };
        let Some(returns) = self.requested_pack_values(returns) else {
            return !projections_ready;
        };
        let Some(params) = args
            .iter()
            .map(|argument| self.callsite_bound_type(*argument))
            .collect::<Option<Vec<_>>>()
        else {
            return !projections_ready;
        };
        let Some(returns) = returns
            .iter()
            .map(|returned| self.callsite_bound_type(*returned))
            .collect::<Option<Vec<_>>>()
        else {
            return !projections_ready;
        };
        let params = self.types.pack(params, None);
        let returns = self.types.pack(
            returns,
            Some(TypePackTail::Homogeneous(self.types.primitives().unknown)),
        );
        let signature = self.types.function_signature(params, returns);
        self.require(callee, signature) || !projections_ready
    }

    /// Returns the precise produced or required type available at one call slot.
    fn callsite_bound_type(&self, variable: InferenceVarId) -> Option<TypeId> {
        if let Some(candidate) = self.candidate_type(variable) {
            return Some(candidate);
        }
        let upper = self.variables[variable].upper;
        (self.types.is_emittable_upper_bound(upper) && self.can_default_to(variable, upper))
            .then_some(upper)
    }

    /// Applies one unique structural function signature found in the callee's lower bound.
    pub(super) fn apply_callable_signature(
        &mut self,
        constraint_id: usize,
        callee: InferenceVarId,
        args: PackVarId,
        returns: PackVarId,
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
        if !self
            .activations
            .insert(constraint_id, Activation::CallSignature(*signature))
        {
            return;
        }
        let Type::FunctionSignature {
            params,
            returns: result_pack,
        } = self.types.get(*signature)
        else {
            return;
        };
        let params = self.types.get_pack(*params).clone();
        let result_pack = self.types.get_pack(*result_pack).clone();

        let fixed_params = params.head.len();
        for (index, accepted) in params.head.into_iter().enumerate() {
            let argument = self.project_pack(args, index);
            self.require(argument, accepted);
        }
        if let Some(TypePackTail::Homogeneous(accepted)) = params.tail {
            let suffix = self.pack_suffix(args, fixed_params);
            let arguments = self.pack_values(suffix);
            self.require(arguments, accepted);
        }

        let mut head = Vec::with_capacity(result_pack.head.len());
        for returned in result_pack.head {
            let target = self.fresh_variable();
            self.observe(target, returned);
            head.push(target);
        }
        let tail = match result_pack.tail {
            Some(TypePackTail::Homogeneous(returned)) => {
                let value = self.fresh_variable();
                self.observe(value, returned);
                let tail = self.fresh_pack();
                self.include_homogeneous_pack(tail, value);
                Some(tail)
            }
            Some(TypePackTail::Generic(_)) => Some(self.fresh_pack()),
            None => None,
        };
        self.include_pack_alternative(returns, PackAlternative { head, tail });
    }

    /// Collects concrete function signatures nested inside one graph node.
    fn collect_function_signatures(&self, ty: TypeId, output: &mut Vec<TypeId>) {
        match self.types.get(ty) {
            Type::FunctionSignature { .. } => output.push(ty),
            Type::Union(members) | Type::Intersection(members) => {
                for member in members {
                    self.collect_function_signatures(*member, output);
                }
            }
            Type::WithMetatable { methods, .. } => {
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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use smol_str::SmolStr;

    use super::{CallSite, GenericBinder, SolverConstraint, TypePackTail, TypeSolver};
    use crate::hil::ty2::{
        builtins::BuiltinEnvironment, inference::program::CollectedProgram, store::TypeStore,
    };

    /// Generic parameter packs flow each argument to the corresponding returned slot.
    #[test]
    fn generic_pack_returns_preserve_positional_types() {
        let mut store = TypeStore::new();
        let builtins = BuiltinEnvironment::new(&mut store);
        let mut solver = TypeSolver::new(
            CollectedProgram::default(),
            &[],
            &builtins,
            &mut store,
            HashMap::new(),
        );
        let first_argument = solver.fresh_variable();
        let second_argument = solver.fresh_variable();
        let callee = solver.fresh_variable();
        let string = solver.types.primitives().string;
        let number = solver.types.primitives().number;
        solver.add_constraint(first_argument, SolverConstraint::Observe(string));
        solver.add_constraint(second_argument, SolverConstraint::Observe(number));

        let name = SmolStr::new("T");
        let params = solver
            .types
            .pack(Vec::new(), Some(TypePackTail::Generic(name.clone())));
        let returns = solver
            .types
            .pack(Vec::new(), Some(TypePackTail::Generic(name.clone())));
        let body = solver.types.function_signature(params, returns);
        let scheme = solver
            .types
            .type_scheme(body, vec![GenericBinder::Pack(name)]);
        let args = solver.fixed_pack(vec![first_argument, second_argument]);
        let returns = solver.fresh_pack();
        let call = CallSite {
            callee,
            args,
            returns,
        };

        solver.instantiate_function_scheme(&call, &scheme, body);
        let first_return = solver.project_pack(returns, 0);
        let second_return = solver.project_pack(returns, 1);
        let excess_return = solver.project_pack(returns, 2);
        solver.solve();

        assert_eq!(solver.produced_type(first_return), Some(string));
        assert_eq!(solver.produced_type(second_return), Some(number));
        assert_eq!(
            solver.produced_type(excess_return),
            Some(solver.types.primitives().nil)
        );
    }
}
