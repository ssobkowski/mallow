//! Solved-type materialization and source generic recovery.

use std::collections::{HashMap, HashSet};

use smol_str::{SmolStr, format_smolstr};

use crate::{
    hil::{
        lifter::ssa::SymbolId,
        ty2::canonical::{
            GenericBinder, Metamethod, MetamethodType, Type, TypeId, TypePackTail, TypeScheme,
        },
    },
    il::ProtoId,
};

use super::model::{InferenceVarId, PackVarId, TableField, TableObjectId, TypeSolver};
use crate::hil::ty2::inference::program::{PackSlot, TypeSlot};

/// Deterministic source-level generic shared by one formal and its related returns.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GenericValuePlan {
    /// Formal parameter whose graph type is generalized.
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

impl TypeSolver<'_> {
    /// Creates every lazy pack and parameter view needed during output, then stabilizes them.
    pub(in crate::hil::ty2::inference) fn prepare_output(&mut self) {
        let functions: Vec<_> = self
            .functions
            .iter()
            .map(|function| (function.proto, function.symbols.params.clone()))
            .collect();
        for (proto, params) in functions {
            for parameter in params {
                self.variable_for_slot(TypeSlot::Symbol(proto, parameter));
            }
            let returns = self.pack_for_slot(PackSlot::Returns(proto));
            self.prepare_pack_output_view(returns);
        }
        self.solve();
    }

    /// Creates stable positional and tail-aggregate views for one output pack.
    fn prepare_pack_output_view(&mut self, pack: PackVarId) {
        if self.output_pack_views.contains_key(&pack) {
            return;
        }
        let (minimum, maximum) = self.pack_arity(pack);
        let head_len = maximum.unwrap_or(minimum);
        let projections = (0..head_len)
            .map(|index| self.project_pack(pack, index))
            .collect();
        let tail = if maximum.is_none() {
            let tail = self.pack_suffix(pack, head_len);
            Some(self.pack_values(tail))
        } else {
            None
        };
        self.output_pack_views.insert(pack, (projections, tail));
    }

    /// Resolves one inference variable into a canonical printable graph type.
    fn resolved_type(
        &mut self,
        variable: InferenceVarId,
        visiting: &mut HashSet<InferenceVarId>,
    ) -> Option<TypeId> {
        if !visiting.insert(variable) {
            return Some(self.types.primitives().unknown);
        }

        let facts = self.variables[variable].clone();
        let never = self.types.primitives().never;
        let mut components = Vec::new();
        if facts.lower != never {
            components.push(facts.lower);
        }
        if !facts.tables.is_empty() {
            let table_types = facts
                .tables
                .into_iter()
                .map(|table| self.materialize_table(table, visiting));
            components.extend(table_types);
        }
        if !facts.closures.is_empty() {
            let function_types = facts
                .closures
                .into_iter()
                .map(|proto| self.materialize_function(proto, visiting));
            components.extend(function_types);
        }

        let resolved = if components.is_empty() {
            self.candidate_type(variable)?
        } else {
            let resolved = self.types.join_all(components);
            if !self.types.is_subtype(resolved, facts.upper) {
                visiting.remove(&variable);
                return None;
            }
            resolved
        };
        visiting.remove(&variable);
        (resolved != never).then_some(resolved)
    }

    /// Materializes one mutable table allocation as an immutable structural type.
    fn materialize_table(
        &mut self,
        table: TableObjectId,
        visiting: &mut HashSet<InferenceVarId>,
    ) -> TypeId {
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

        let nil = self.types.primitives().nil;
        let unknown = self.types.primitives().unknown;
        let mut materialized_fields = Vec::new();
        for (name, field) in fields {
            let mut value = self.resolved_type(field.value, visiting).unwrap_or(unknown);
            if !field.definite {
                value = self.types.join(value, nil);
            }
            materialized_fields.push((name, value));
        }
        materialized_fields.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

        let indexer = match (
            self.resolved_type(keys, visiting),
            self.resolved_type(values, visiting),
        ) {
            (Some(key), Some(value)) => Some((key, self.types.join(value, nil))),
            _ => None,
        };
        let base = self.types.table_shape(materialized_fields, indexer);

        let mut methods_by_kind: HashMap<Metamethod, Vec<TypeId>> = HashMap::new();
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
                methods_by_kind.entry(method).or_default().push(ty);
            }
        }
        let mut methods: Vec<_> = methods_by_kind
            .into_iter()
            .map(|(method, types)| MetamethodType {
                method,
                ty: self.types.join_all(types),
            })
            .collect();
        methods.sort_by_key(|entry| entry.method as u8);
        if methods.is_empty() {
            base
        } else {
            self.types.with_metatable(base, methods)
        }
    }

    /// Materializes a lifted proto's parameter and return pack.
    fn materialize_function(
        &mut self,
        proto: ProtoId,
        visiting: &mut HashSet<InferenceVarId>,
    ) -> TypeId {
        let Some(function) = self.functions.get(proto.0 as usize) else {
            return self.types.primitives().function;
        };
        let params = function.symbols.params.clone();
        let is_vararg = function.is_vararg;
        let unknown = self.types.primitives().unknown;
        let param_types = params
            .into_iter()
            .map(|parameter| {
                let slot = TypeSlot::Symbol(proto, parameter);
                let variable = self.variable_for_slot(slot);
                self.parameter_upper_bound(slot, variable)
                    .or_else(|| self.resolved_type(variable, visiting))
                    .unwrap_or(unknown)
            })
            .collect();
        let params = self.types.pack(
            param_types,
            is_vararg.then_some(TypePackTail::Homogeneous(unknown)),
        );

        let returns = self.pack_for_slot(PackSlot::Returns(proto));
        let returns = self.materialize_pack(returns, visiting);
        self.types.function_signature(params, returns)
    }

    /// Materializes one solved inference pack as a canonical function type pack.
    fn materialize_pack(
        &mut self,
        pack: PackVarId,
        visiting: &mut HashSet<InferenceVarId>,
    ) -> crate::hil::ty2::canonical::TypePackId {
        let (projections, tail_value) = self
            .output_pack_views
            .get(&pack)
            .cloned()
            .expect("output pack views must be prepared before materialization");
        let unknown = self.types.primitives().unknown;
        let head = projections
            .into_iter()
            .map(|variable| {
                self.compatible_upper_bound(variable)
                    .or_else(|| self.resolved_type(variable, visiting))
                    .unwrap_or(unknown)
            })
            .collect();
        let tail = tail_value.map(|variable| {
            let value = self
                .compatible_upper_bound(variable)
                .or_else(|| self.resolved_type(variable, visiting))
                .unwrap_or(unknown);
            TypePackTail::Homogeneous(value)
        });
        self.types.pack(head, tail)
    }

    /// Returns a precise consumer bound when producer mismatch is only nil or dynamic.
    fn compatible_upper_bound(&self, variable: InferenceVarId) -> Option<TypeId> {
        let facts = &self.variables[variable];
        (self.types.is_emittable_upper_bound(facts.upper)
            && self.can_default_to(variable, facts.upper))
        .then_some(facts.upper)
    }

    /// Returns a body's precise parameter requirement when call evidence is only dynamic.
    fn parameter_upper_bound(&self, slot: TypeSlot, variable: InferenceVarId) -> Option<TypeId> {
        let TypeSlot::Symbol(proto, symbol) = slot else {
            return None;
        };
        let function = self.functions.get(proto.0 as usize)?;
        if !function.symbols.params.contains(&symbol) {
            return None;
        }
        self.compatible_upper_bound(variable)
    }

    /// Resolves one durable symbol into a validated graph type scheme.
    pub(in crate::hil::ty2::inference) fn resolved_symbol_type(
        &mut self,
        slot: TypeSlot,
    ) -> Option<TypeScheme> {
        let variable = *self.variables_by_slot.get(&slot)?;
        let closure_proto = {
            let closures = &self.variables[variable].closures;
            (closures.len() == 1).then(|| *closures.iter().next().expect("one closure exists"))
        };
        let ty = self
            .parameter_upper_bound(slot, variable)
            .or_else(|| self.resolved_type(variable, &mut HashSet::new()))?;
        if self.types.contains_metatable(ty) {
            // Structural metatable annotations are not representable at this
            // boundary without losing operator behavior, so leave the symbol
            // unannotated until the emitter has a dedicated representation.
            return None;
        }
        let ty = self.types.widen_literals(ty);
        if let TypeSlot::Symbol(proto, symbol) = slot
            && let Some(parameter) = self.generic_parameter_type(proto, symbol, ty)
        {
            return Some(parameter);
        }
        if let Some(proto) = closure_proto {
            return Some(self.generic_function_type(proto, ty));
        }
        Some(self.types.type_scheme(ty, Vec::new()))
    }

    /// Rewrites a recovered function signature with every proven source generic.
    fn generic_function_type(&mut self, proto: ProtoId, ty: TypeId) -> TypeScheme {
        let Type::FunctionSignature { params, returns } = self.types.get(ty).clone() else {
            return self.types.type_scheme(ty, Vec::new());
        };
        let Some(function) = self.functions.get(proto.0 as usize) else {
            return self.types.type_scheme(ty, Vec::new());
        };
        let function_params = function.symbols.params.clone();
        let mut params = self.types.get_pack(params).clone();
        let mut returns = self.types.get_pack(returns).clone();
        let mut binders = Vec::new();

        for (index, symbol) in function_params.into_iter().enumerate() {
            let Some(base) = params.head.get(index).copied() else {
                continue;
            };
            let name_offset = binders.len();
            let Some((names, table)) =
                self.generic_parameter_shape(proto, symbol, base, name_offset)
            else {
                continue;
            };
            binders.extend(names.into_iter().map(GenericBinder::Type));
            params.head[index] = table;
        }

        for mut plan in self.generic_value_plans(proto) {
            plan.name = Self::conventional_generic_name(binders.len());
            binders.push(GenericBinder::Type(plan.name.clone()));
            let pattern = self.generic_value_pattern(&plan);
            if let Some(parameter) = params.head.get_mut(plan.parameter_index) {
                *parameter = pattern;
            }
            for return_index in plan.return_indices {
                if let Some(returned) = returns.head.get_mut(return_index) {
                    *returned = pattern;
                }
            }
        }

        let params = self.types.pack(params.head, params.tail);
        let returns = self.types.pack(returns.head, returns.tail);
        let body = self.types.function_signature(params, returns);
        self.types.type_scheme(body, binders)
    }

    /// Returns a generic parameter annotation for a directly emitted parameter.
    fn generic_parameter_type(
        &mut self,
        proto: ProtoId,
        symbol: SymbolId,
        base: TypeId,
    ) -> Option<TypeScheme> {
        if let Some(plan) = self
            .generic_value_plans(proto)
            .into_iter()
            .find(|plan| plan.parameter == symbol)
        {
            let generic = self.types.generic(plan.name.clone());
            let body = if plan.optional {
                self.types.union(generic, self.types.primitives().nil)
            } else {
                generic
            };
            return Some(
                self.types
                    .type_scheme(body, vec![GenericBinder::Type(plan.name)]),
            );
        }
        let (names, table) = self.generic_parameter_shape(proto, symbol, base, 0)?;
        Some(
            self.types
                .type_scheme(table, names.into_iter().map(GenericBinder::Type).collect()),
        )
    }

    /// Plans collision-free direct-value generics whose formal upper bound stayed unknown.
    pub(super) fn generic_value_plans(&self, proto: ProtoId) -> Vec<GenericValuePlan> {
        let Some(relations) = self.body_value_relations.get(&proto) else {
            return Vec::new();
        };
        let Some(function) = self.functions.get(proto.0 as usize) else {
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
            let parameter_index = relation.parameter_index;
            let return_index = relation.return_index;
            let Some(parameter) = function.symbols.params.get(parameter_index).copied() else {
                continue;
            };
            let slot = TypeSlot::Symbol(proto, parameter);
            let Some(variable) = self.variables_by_slot.get(&slot) else {
                continue;
            };
            if self.variables[*variable].upper != unknown
                || !self.parameter_allows_generic(*variable)
            {
                continue;
            }
            if let Some(existing) = plans
                .iter_mut()
                .find(|plan| plan.parameter_index == parameter_index)
            {
                existing.return_indices.push(return_index);
                continue;
            }
            let name_index = reserved_count + plans.len();
            plans.push(GenericValuePlan {
                parameter,
                parameter_index,
                return_indices: vec![return_index],
                name: Self::conventional_generic_name(name_index),
                optional: self
                    .closure_argument_packs
                    .get(&proto)
                    .is_some_and(|packs| {
                        packs.iter().any(|pack| {
                            let (minimum, _) = self.pack_arity(*pack);
                            minimum <= parameter_index
                        })
                    }),
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
    pub(super) fn generic_value_pattern(&mut self, plan: &GenericValuePlan) -> TypeId {
        let generic = self.types.generic(plan.name.clone());
        if plan.optional {
            self.types.union(generic, self.types.primitives().nil)
        } else {
            generic
        }
    }

    /// Builds one structural table parameter from same-object field relations.
    fn generic_parameter_shape(
        &mut self,
        proto: ProtoId,
        symbol: SymbolId,
        base: TypeId,
        name_offset: usize,
    ) -> Option<(Vec<SmolStr>, TypeId)> {
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
        self.collect_graph_field_names(base, &mut fields);
        let mut generic_by_field: HashMap<SmolStr, usize> = HashMap::new();
        for call in &calls {
            for (_, field) in &call.field_arguments {
                let next_index = generic_by_field.len();
                generic_by_field.entry(field.clone()).or_insert(next_index);
            }
        }

        let names: Vec<_> = (0..generic_by_field.len())
            .map(|index| Self::conventional_generic_name(name_offset + index))
            .collect();
        for (field, index) in &generic_by_field {
            fields.insert(field.clone(), self.types.generic(names[*index].clone()));
        }
        for call in calls {
            let param_count = call
                .field_arguments
                .iter()
                .map(|(index, _)| index + 1)
                .max()
                .unwrap_or(0);
            let mut callback_params = vec![self.types.primitives().unknown; param_count];
            for (index, field) in call.field_arguments {
                let generic_index = generic_by_field
                    .get(&field)
                    .copied()
                    .expect("generic field was indexed before callback construction");
                callback_params[index] = self.types.generic(names[generic_index].clone());
            }
            let (callback_returns, callback_tail) = match call.return_count {
                Some(return_count) => (vec![self.types.primitives().unknown; return_count], None),
                None => (
                    Vec::new(),
                    Some(TypePackTail::Homogeneous(self.types.primitives().unknown)),
                ),
            };
            let callback_params = self.types.pack(callback_params, None);
            let callback_returns = self.types.pack(callback_returns, callback_tail);
            let callback = self
                .types
                .function_signature(callback_params, callback_returns);
            fields.insert(call.callee, callback);
        }

        Some((
            names,
            self.types.table_shape(fields.into_iter().collect(), None),
        ))
    }

    /// Collects field names that occur in any structural table alternative.
    fn collect_graph_field_names(&self, ty: TypeId, fields: &mut HashMap<SmolStr, TypeId>) {
        match self.types.get(ty) {
            Type::TableShape {
                fields: table_fields,
                ..
            } => {
                for (name, ty) in table_fields {
                    fields.entry(name.clone()).or_insert(*ty);
                }
            }
            Type::Union(members) | Type::Intersection(members) => {
                for member in members {
                    self.collect_graph_field_names(*member, fields);
                }
            }
            Type::WithMetatable { base, .. } => self.collect_graph_field_names(*base, fields),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use id_arena::Arena;
    use smol_str::{SmolStr, format_smolstr};

    use super::super::model::SolverConstraint;
    use super::{GenericValuePlan, TypePackTail, TypeSolver};
    use crate::hil::{
        lifter::ssa::Symbol,
        ty2::{
            builtins::BuiltinEnvironment,
            canonical::Type,
            inference::program::{CollectedProgram, GenericFieldCall},
            store::TypeStore,
        },
    };
    use crate::il::ProtoId;

    /// Materializing an open pack keeps fixed-head types out of its tail.
    #[test]
    fn materialized_open_pack_uses_only_suffix_values_for_tail() {
        let mut store = TypeStore::new();
        let builtins = BuiltinEnvironment::new(&mut store);
        let mut solver = TypeSolver::new(
            CollectedProgram::default(),
            &[],
            &builtins,
            &mut store,
            HashMap::new(),
        );
        let head = solver.fresh_variable();
        let tail_value = solver.fresh_variable();
        let boolean = solver.types.primitives().boolean;
        let string = solver.types.primitives().string;
        solver.add_constraint(head, SolverConstraint::Observe(boolean));
        solver.add_constraint(tail_value, SolverConstraint::Observe(string));
        let tail = solver.fresh_pack();
        solver.include_homogeneous_pack(tail, tail_value);
        let pack = solver.prefixed_pack(vec![head], tail);
        solver.prepare_pack_output_view(pack);
        solver.solve();

        let materialized = solver.materialize_pack(pack, &mut HashSet::new());
        let materialized = solver.types.get_pack(materialized);
        assert_eq!(materialized.head, vec![boolean]);
        assert_eq!(materialized.tail, Some(TypePackTail::Homogeneous(string)));
    }

    /// Independent table generics and a direct generic receive one global name allocator.
    #[test]
    fn function_generic_binders_use_one_global_allocator() {
        let mut store = TypeStore::new();
        let builtins = BuiltinEnvironment::new(&mut store);
        let mut solver = TypeSolver::new(
            CollectedProgram::default(),
            &[],
            &builtins,
            &mut store,
            HashMap::new(),
        );
        let mut symbols: Arena<Symbol> = Arena::new();
        let first = symbols.alloc(Symbol::param(0));
        let second = symbols.alloc(Symbol::param(1));
        solver.generic_field_calls.insert(
            ProtoId(0),
            vec![
                GenericFieldCall {
                    parameter: first,
                    callee: "visit".into(),
                    field_arguments: (0..11)
                        .map(|index| (index, format_smolstr!("field{index}")))
                        .collect(),
                    return_count: Some(1),
                },
                GenericFieldCall {
                    parameter: second,
                    callee: "visit".into(),
                    field_arguments: vec![(0, "value".into())],
                    return_count: Some(1),
                },
            ],
        );
        let table = solver.types.table_shape(Vec::new(), None);
        let (first_names, first_shape) = solver
            .generic_parameter_shape(ProtoId(0), first, table, 0)
            .expect("first table shape");
        let (second_names, second_shape) = solver
            .generic_parameter_shape(ProtoId(0), second, table, first_names.len())
            .expect("second table shape");
        assert_eq!(first_names.len(), 11);
        assert_eq!(first_names[9], SmolStr::new("T9"));
        assert_eq!(first_names[10], SmolStr::new("T10"));
        assert_eq!(second_names, vec![SmolStr::new("T11")]);
        let Type::TableShape { fields, .. } = solver.types.get(first_shape) else {
            panic!("first generic shape is not a table")
        };
        let field9 = fields
            .iter()
            .find(|(name, _)| name == "field9")
            .expect("field9 generic");
        assert!(matches!(solver.types.get(field9.1), Type::Generic(name) if name == "T9"));
        let Type::TableShape { fields, .. } = solver.types.get(second_shape) else {
            panic!("second generic shape is not a table")
        };
        assert!(matches!(solver.types.get(fields[0].1), Type::Generic(name) if name == "T11"));

        let direct = GenericValuePlan {
            parameter: first,
            parameter_index: 0,
            return_indices: vec![0],
            name: "T12".into(),
            optional: false,
        };
        assert_eq!(
            TypeSolver::conventional_generic_name(12),
            SmolStr::new("T12")
        );
        let direct_type = solver.generic_value_pattern(&direct);
        assert!(matches!(solver.types.get(direct_type), Type::Generic(name) if name == "T12"));
    }
}
