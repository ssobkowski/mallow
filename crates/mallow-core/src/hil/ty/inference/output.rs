//! Materialization of solved inference facts into canonical types.

use std::collections::HashSet;

use super::engine::Engine;
use super::keys::{PackKey, ValueKey};
use super::world::{ObjectId, PackId, ValueId};
use crate::hil::ty::canonical::{MetamethodType, TypeId, TypePackTail};
use crate::il::ProtoId;

impl Engine<'_> {
    /// Creates output views needed by function signatures, then stabilizes them.
    pub fn prepare_output(&mut self) {
        let functions: Vec<_> = self
            .functions
            .iter()
            .map(|function| {
                (
                    function.proto,
                    function.symbols.params().to_vec(),
                    function.is_vararg,
                )
            })
            .collect();
        for (proto, params, is_vararg) in functions {
            for parameter in params {
                self.value_for_key(ValueKey::Symbol(proto, parameter));
            }
            if is_vararg {
                self.pack_for_key(PackKey::VarArgs(proto));
            }
            let returns = self.pack_for_key(PackKey::Returns(proto));
            self.prepare_pack_view(returns);
        }
        self.solve();
    }

    /// Resolves one stable value key into a canonical type.
    pub fn resolved_value_type(&mut self, key: ValueKey) -> Option<TypeId> {
        let value = self.get_value_key(key)?;
        let ty = self.resolved_value(value, &mut HashSet::new())?;
        if self.types.contains_metatable(ty) {
            return None;
        }
        let ty = self.types.widen_literals(ty);
        Some(ty)
    }

    /// Creates currently useful projections for one output pack.
    fn prepare_pack_view(&mut self, pack: PackId) {
        let existing = self.world.packs[pack]
            .projections
            .keys()
            .copied()
            .max()
            .map(|index| index + 1)
            .unwrap_or(1);
        for index in 0..existing {
            self.ensure_projection(pack, index);
        }
    }

    /// Resolves one value into a canonical type.
    fn resolved_value(
        &mut self,
        value: ValueId,
        visiting: &mut HashSet<ValueId>,
    ) -> Option<TypeId> {
        if !visiting.insert(value) {
            return Some(self.types.primitives().unknown);
        }

        let state = self.world.values[value].clone();
        let never = self.types.primitives().never;
        let mut parts = Vec::new();
        if state.lower != never {
            parts.push(state.lower);
        }
        for object in state.identities.objects {
            parts.push(self.materialize_object(object, visiting));
        }
        for proto in state.identities.closures {
            parts.push(self.materialize_function(proto, visiting));
        }

        let resolved = if parts.is_empty() {
            self.candidate_type(value)?
        } else {
            let resolved = self.types.join_all(parts);
            if !self.types.is_subtype(resolved, state.upper) {
                visiting.remove(&value);
                return None;
            }
            resolved
        };
        visiting.remove(&value);
        (resolved != never).then_some(resolved)
    }

    /// Materializes one mutable object as an immutable table shape.
    fn materialize_object(&mut self, object: ObjectId, visiting: &mut HashSet<ValueId>) -> TypeId {
        let object_state = &self.world.objects[object];
        let keys = object_state.keys;
        let values = object_state.values;
        let fields: Vec<_> = object_state
            .fields
            .iter()
            .map(|(name, field)| (name.clone(), *field))
            .collect();
        let metatables: Vec<_> = object_state.metatables.iter().copied().collect();

        let nil = self.types.primitives().nil;
        let unknown = self.types.primitives().unknown;
        let mut materialized_fields = Vec::new();
        for (name, field) in fields {
            let mut value = self
                .resolved_value(field.value, visiting)
                .unwrap_or(unknown);
            if !field.definite {
                value = self.types.join(value, nil);
            }
            materialized_fields.push((name, value));
        }
        materialized_fields.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

        let indexer = match (
            self.resolved_value(keys, visiting),
            self.resolved_value(values, visiting),
        ) {
            (Some(key), Some(value)) => Some((key, self.types.join(value, nil))),
            _ => None,
        };
        let base = self.types.table_shape(materialized_fields, indexer);

        let mut methods = Vec::<MetamethodType>::new();
        for metatable in metatables {
            let fields: Vec<_> = self.world.objects[metatable]
                .fields
                .iter()
                .map(|(name, field)| (name.clone(), field.value))
                .collect();
            for (name, value) in fields {
                let Ok(method) = crate::hil::ty::canonical::Metamethod::try_from(name.as_str())
                else {
                    continue;
                };
                let Some(ty) = self.resolved_value(value, visiting) else {
                    continue;
                };
                methods.push(MetamethodType { method, ty });
            }
        }
        methods.sort_by_key(|method| method.method as u8);
        if methods.is_empty() {
            base
        } else {
            self.types.with_metatable(base, methods)
        }
    }

    /// Materializes one closure proto as a function signature.
    fn materialize_function(&mut self, proto: ProtoId, visiting: &mut HashSet<ValueId>) -> TypeId {
        let Some(function) = self.functions.get(proto.0 as usize) else {
            return self.types.primitives().function;
        };
        let params = function.symbols.params().to_vec();
        let is_vararg = function.is_vararg;
        let unknown = self.types.primitives().unknown;
        let param_types = params
            .into_iter()
            .map(|parameter| {
                let value = self.value_for_key(ValueKey::Symbol(proto, parameter));
                self.resolved_value(value, visiting).unwrap_or(unknown)
            })
            .collect();
        let params = self.types.pack(
            param_types,
            is_vararg.then_some(TypePackTail::Homogeneous(unknown)),
        );

        let returns = self.pack_for_key(PackKey::Returns(proto));
        let returns = self.materialize_pack(returns, visiting);
        self.types.function_signature(params, returns)
    }

    /// Materializes one solved pack as a canonical type pack.
    fn materialize_pack(
        &mut self,
        pack: PackId,
        visiting: &mut HashSet<ValueId>,
    ) -> crate::hil::ty::canonical::TypePackId {
        let mut projections: Vec<_> = self.world.packs[pack]
            .projections
            .iter()
            .map(|(index, value)| (*index, *value))
            .collect();
        projections.sort_by_key(|(index, _)| *index);
        let unknown = self.types.primitives().unknown;
        let head = projections
            .into_iter()
            .map(|(_, value)| self.resolved_value(value, visiting).unwrap_or(unknown))
            .collect();
        self.types.pack(head, None)
    }
}
