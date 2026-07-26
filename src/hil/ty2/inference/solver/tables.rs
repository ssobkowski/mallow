//! Table constraints, structural access, and metatable attachment.

use smol_str::SmolStr;

use crate::hil::ty2::canonical::{Type, TypeId, TypeLiteral};
use crate::hil::ty2::inference::solver::model::Activation;

use super::model::{
    InferenceVarId, PackVarId, SolverCallArgument, SolverConstraint, TableObjectId, TypeSolver,
};

impl TypeSolver<'_> {
    /// Connects one indexed write to every table identity carried by `object`.
    pub(super) fn apply_set_index(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        index: InferenceVarId,
        value: InferenceVarId,
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if !self
                .activations
                .insert(constraint_id, Activation::TableConstraint(table))
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
    pub(super) fn apply_get_index(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        index: InferenceVarId,
        value: InferenceVarId,
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if !self
                .activations
                .insert(constraint_id, Activation::TableConstraint(table))
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
                    .activations
                    .insert(constraint_id, Activation::DynamicField(table, field))
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
    pub(super) fn apply_set_field(
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
                .activations
                .insert(constraint_id, Activation::TableConstraint(table))
            {
                continue;
            }
            let field_value = self.table_field_variable(table, field.clone(), definite);
            self.add_constraint(field_value, SolverConstraint::FlowFrom(value));
            self.table_changed(table);
        }
    }

    /// Connects one named read to concrete tables and sealed structural types.
    pub(super) fn apply_get_field(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        field: SmolStr,
        value: InferenceVarId,
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if !self
                .activations
                .insert(constraint_id, Activation::TableConstraint(table))
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
    pub(super) fn apply_field_call(
        &mut self,
        constraint_id: usize,
        object: InferenceVarId,
        callee_field: SmolStr,
        head: &[SolverCallArgument],
        tail: Option<PackVarId>,
        returns: PackVarId,
    ) {
        let tables: Vec<_> = self.variables[object].tables.iter().copied().collect();
        for table in tables {
            if !self
                .activations
                .insert(constraint_id, Activation::TableConstraint(table))
            {
                continue;
            }

            let callee = self.table_field_variable(table, callee_field.clone(), false);
            let head = head
                .iter()
                .map(|argument| match argument {
                    SolverCallArgument::Value(variable) => *variable,
                    SolverCallArgument::Field(field) => {
                        self.table_field_variable(table, field.clone(), false)
                    }
                })
                .collect();
            let args = if let Some(tail) = tail {
                self.prefixed_pack(head, tail)
            } else {
                self.fixed_pack(head)
            };
            self.add_constraint(callee, SolverConstraint::Call { args, returns });
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
                .activations
                .insert(constraint_id, Activation::IndexDispatch(metatable))
            {
                continue;
            }
            let handler = self.table_field_variable(metatable, "__index".into(), false);
            let key = self.fresh_variable();
            let key_ty = self.types.literal(TypeLiteral::String(field.to_string()));
            self.add_constraint(key, SolverConstraint::Observe(key_ty));
            let args = self.fixed_pack(vec![object, key]);
            let returns = self.result_pack(&[value]);
            self.add_constraint(handler, SolverConstraint::Call { args, returns });
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
                .activations
                .insert(constraint_id, Activation::IndexDispatch(metatable))
            {
                continue;
            }
            let handler = self.table_field_variable(metatable, "__index".into(), false);
            let args = self.fixed_pack(vec![object, key]);
            let returns = self.result_pack(&[value]);
            self.add_constraint(handler, SolverConstraint::Call { args, returns });
            self.add_constraint(handler, SolverConstraint::GetIndex { index: key, value });
        }
    }

    /// Extracts an indexer value from a sealed structural type.
    fn structural_index_value(&mut self, ty: TypeId) -> Option<TypeId> {
        match self.types.get(ty).clone() {
            Type::TableShape {
                indexer: Some((_, value)),
                ..
            } => Some(value),
            Type::Union(members) | Type::Intersection(members) => {
                let values: Vec<_> = members
                    .into_iter()
                    .filter_map(|member| self.structural_index_value(member))
                    .collect();
                (!values.is_empty()).then(|| self.types.union_all(values))
            }
            Type::WithMetatable { base, .. } => self.structural_index_value(base),
            _ => None,
        }
    }

    /// Extracts and unions all matching named fields from a structural type.
    fn structural_field_type(&mut self, ty: TypeId, field: &SmolStr) -> Option<TypeId> {
        match self.types.get(ty).clone() {
            Type::TableShape { fields, .. } => fields
                .into_iter()
                .find(|(name, _)| name == field)
                .map(|(_, ty)| ty),
            Type::Union(members) | Type::Intersection(members) => {
                let values: Vec<_> = members
                    .into_iter()
                    .filter_map(|member| self.structural_field_type(member, field))
                    .collect();
                (!values.is_empty()).then(|| self.types.union_all(values))
            }
            Type::WithMetatable { base, .. } => self.structural_field_type(base, field),
            _ => None,
        }
    }

    /// Links every base table allocation to every metatable allocation.
    pub(super) fn apply_set_metatable(
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
}
