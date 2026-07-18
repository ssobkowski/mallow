//! Primitive operator constraints and metamethod dispatch.

use crate::{
    hil::ty2::canonical::{Metamethod, Type, TypeId},
    operator::{BinOp, UnOp},
};
use smol_str::SmolStr;

use super::model::{DeferredOperator, InferenceVarId, PackVarId, SolverConstraint, TypeSolver};

impl TypeSolver<'_> {
    /// Activates primitive operator defaults after table and closure identities settle.
    pub(super) fn activate_deferred_operators(&mut self) -> bool {
        let mut deferred: Vec<_> = std::mem::take(&mut self.deferred_operators)
            .into_iter()
            .collect();
        deferred.sort_by_key(|(constraint_id, _)| *constraint_id);
        let mut activated = false;
        for (constraint_id, operator) in deferred {
            if !self.activated_operator_fallbacks.insert(constraint_id) {
                continue;
            }
            let number = self.types.primitives().number;
            let string = self.types.primitives().string;
            match operator {
                DeferredOperator::Arithmetic { lhs, rhs, result }
                    if self.can_default_to(lhs, number) && self.can_default_to(rhs, number) =>
                {
                    self.require(lhs, number);
                    self.require(rhs, number);
                    self.observe(result, number);
                    activated = true;
                }
                DeferredOperator::Comparison { lhs, rhs } => {
                    let narrowed = if self.produced_is_subtype(lhs, number)
                        && self.can_default_to(rhs, number)
                        || self.produced_is_subtype(rhs, number) && self.can_default_to(lhs, number)
                    {
                        Some(number)
                    } else if self.produced_is_subtype(lhs, string)
                        && self.can_default_to(rhs, string)
                        || self.produced_is_subtype(rhs, string) && self.can_default_to(lhs, string)
                    {
                        Some(string)
                    } else {
                        None
                    };
                    if let Some(ty) = narrowed {
                        self.require(lhs, ty);
                        self.require(rhs, ty);
                        activated = true;
                    }
                }
                DeferredOperator::UnaryMinus { operand, result }
                    if self.can_default_to(operand, number) =>
                {
                    self.require(operand, number);
                    self.observe(result, number);
                    activated = true;
                }
                _ => {}
            }
        }
        activated
    }

    /// Returns whether a variable produces only values inside `primitive`.
    fn produced_is_subtype(&self, variable: InferenceVarId, primitive: TypeId) -> bool {
        self.produced_type(variable)
            .is_some_and(|produced| self.types.is_subtype(produced, primitive))
    }

    /// Records one operator fallback unless its final decision already ran.
    fn defer_operator(&mut self, constraint_id: usize, operator: DeferredOperator) {
        if !self.activated_operator_fallbacks.contains(&constraint_id) {
            self.deferred_operators
                .entry(constraint_id)
                .or_insert(operator);
        }
    }
    /// Applies conservative builtin overloads and then known metamethods.
    pub(super) fn apply_binary(
        &mut self,
        constraint_id: usize,
        lhs: InferenceVarId,
        op: BinOp,
        rhs: InferenceVarId,
        result: InferenceVarId,
    ) {
        let number = self.types.primitives().number;
        let string = self.types.primitives().string;
        let boolean = self.types.primitives().boolean;
        let table = self.types.primitives().table;
        let vector = self.types.primitives().vector;
        match op {
            BinOp::Eq | BinOp::Ne => {
                self.observe(result, boolean);
            }
            BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => {
                self.observe(result, boolean);
                let accepted = self.operator_domain(&[number, string, table]);
                self.require(lhs, accepted);
                self.require(rhs, accepted);
                self.defer_operator(constraint_id, DeferredOperator::Comparison { lhs, rhs });
            }
            BinOp::And => {
                if let Some(lhs_ty) = self.evidence_type(lhs) {
                    let falsy = self.types.falsy_part(lhs_ty);
                    self.observe(result, falsy);
                }
                if let Some(rhs_ty) = self.evidence_type(rhs) {
                    self.observe(result, rhs_ty);
                }
            }
            BinOp::Or => {
                if let Some(lhs_ty) = self.evidence_type(lhs) {
                    let truthy = self.types.truthy_part(lhs_ty);
                    self.observe(result, truthy);
                }
                if let Some(rhs_ty) = self.evidence_type(rhs) {
                    self.observe(result, rhs_ty);
                }
            }
            BinOp::Concat => {
                let accepted = self.operator_domain(&[string, number, table]);
                self.require(lhs, accepted);
                self.require(rhs, accepted);
                if self.operands_are_concat_primitives(lhs, rhs) {
                    self.observe(result, string);
                }
                self.connect_binary_metamethod(lhs, rhs, result, Metamethod::Concat);
            }
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::IDiv
            | BinOp::Mod
            | BinOp::Pow => {
                let accepted = self.operator_domain(&[number, vector, table]);
                self.require(lhs, accepted);
                self.require(rhs, accepted);
                if let Some(ty) = self.arithmetic_result(lhs, op, rhs) {
                    self.observe(result, ty);
                }
                self.defer_operator(
                    constraint_id,
                    DeferredOperator::Arithmetic { lhs, rhs, result },
                );
                if let Ok(method) = Metamethod::try_from(op) {
                    self.connect_binary_metamethod(lhs, rhs, result, method);
                }
            }
        }
    }

    /// Applies conservative builtin unary operations and known metamethods.
    pub(super) fn apply_unary(
        &mut self,
        constraint_id: usize,
        operand: InferenceVarId,
        op: UnOp,
        result: InferenceVarId,
    ) {
        let number = self.types.primitives().number;
        let string = self.types.primitives().string;
        let boolean = self.types.primitives().boolean;
        let vector = self.types.primitives().vector;
        let table = self.types.primitives().table;
        match op {
            UnOp::Not => {
                self.observe(result, boolean);
            }
            UnOp::Minus => {
                let accepted = self.operator_domain(&[number, vector, table]);
                self.require(operand, accepted);
                if let Some(operand_ty) = self.evidence_type(operand) {
                    if self.has_concrete_overlap(operand_ty, number) {
                        self.observe(result, number);
                    }
                    if self.has_concrete_overlap(operand_ty, vector) {
                        self.observe(result, vector);
                    }
                }
                self.defer_operator(
                    constraint_id,
                    DeferredOperator::UnaryMinus { operand, result },
                );
                self.connect_unary_metamethod(operand, result, Metamethod::Unm);
            }
            UnOp::Length => {
                let accepted = self.operator_domain(&[string, table]);
                self.require(operand, accepted);
                if let Some(operand_ty) = self.evidence_type(operand)
                    && self.has_concrete_overlap(operand_ty, string)
                {
                    self.observe(result, number);
                }
                self.connect_unary_metamethod(operand, result, Metamethod::Len);
            }
        }
    }

    /// Builds an operator domain including userdata metamethod receivers.
    fn operator_domain(&mut self, builtins: &[TypeId]) -> TypeId {
        let userdata = self.types.primitives().userdata;
        let members: Vec<_> = builtins.iter().copied().chain([userdata]).collect();
        self.types.union_all(members)
    }

    /// Returns every builtin arithmetic result supported by current evidence.
    fn arithmetic_result(
        &mut self,
        lhs: InferenceVarId,
        op: BinOp,
        rhs: InferenceVarId,
    ) -> Option<TypeId> {
        let lhs = self.evidence_type(lhs)?;
        let rhs = self.evidence_type(rhs)?;
        let number = self.types.primitives().number;
        let vector = self.types.primitives().vector;
        let mut results = Vec::new();
        if self.has_concrete_overlap(lhs, number) && self.has_concrete_overlap(rhs, number) {
            results.push(number);
        }

        let vector_lhs = self.has_concrete_overlap(lhs, vector);
        let vector_rhs = self.has_concrete_overlap(rhs, vector);
        let number_rhs = self.has_concrete_overlap(rhs, number);
        let supported = match op {
            BinOp::Add | BinOp::Sub => vector_lhs && vector_rhs,
            BinOp::Mul | BinOp::Div | BinOp::IDiv => vector_lhs && (vector_rhs || number_rhs),
            BinOp::Mod | BinOp::Pow => false,
            _ => false,
        };
        if supported {
            results.push(vector);
        }
        (!results.is_empty()).then(|| self.types.union_all(results))
    }

    /// Returns whether both operands prove a primitive concatenation overload.
    fn operands_are_concat_primitives(&mut self, lhs: InferenceVarId, rhs: InferenceVarId) -> bool {
        let Some(lhs) = self.evidence_type(lhs) else {
            return false;
        };
        let Some(rhs) = self.evidence_type(rhs) else {
            return false;
        };
        let string = self.types.primitives().string;
        let number = self.types.primitives().number;
        let lhs_accepted =
            self.has_concrete_overlap(lhs, string) || self.has_concrete_overlap(lhs, number);
        let rhs_accepted =
            self.has_concrete_overlap(rhs, string) || self.has_concrete_overlap(rhs, number);
        lhs_accepted && rhs_accepted
    }

    /// Returns whether `evidence` contains a concrete member of `accepted`.
    fn has_concrete_overlap(&mut self, evidence: TypeId, accepted: TypeId) -> bool {
        if matches!(self.types.get(evidence), Type::Unknown | Type::Any) {
            return false;
        }
        self.types.meet(evidence, accepted) != self.types.primitives().never
    }

    /// Connects a binary operation to every known operand metatable method.
    fn connect_binary_metamethod(
        &mut self,
        lhs: InferenceVarId,
        rhs: InferenceVarId,
        result: InferenceVarId,
        method: Metamethod,
    ) {
        let mut tables: Vec<_> = self.variables[lhs].tables.iter().copied().collect();
        tables.extend(self.variables[rhs].tables.iter().copied());
        tables.sort_unstable();
        tables.dedup();
        for table in tables {
            let metatables: Vec<_> = self.tables[table].metatables.iter().copied().collect();
            for metatable in metatables {
                let method = self.table_field_variable(
                    metatable,
                    SmolStr::new_static(method.field()),
                    false,
                );
                let args = self.fixed_pack(vec![lhs, rhs]);
                let returns = self.result_pack(&[result]);
                self.add_constraint(method, SolverConstraint::Call { args, returns });
            }
        }
    }

    /// Connects a unary operation to every known operand metatable method.
    fn connect_unary_metamethod(
        &mut self,
        operand: InferenceVarId,
        result: InferenceVarId,
        method: Metamethod,
    ) {
        let tables: Vec<_> = self.variables[operand].tables.iter().copied().collect();
        for table in tables {
            let metatables: Vec<_> = self.tables[table].metatables.iter().copied().collect();
            for metatable in metatables {
                let method = self.table_field_variable(
                    metatable,
                    SmolStr::new_static(method.field()),
                    false,
                );
                let args = self.fixed_pack(vec![operand]);
                let returns = self.result_pack(&[result]);
                self.add_constraint(method, SolverConstraint::Call { args, returns });
            }
        }
    }

    /// Connects a table call to every statically known `__call` method.
    pub(super) fn connect_call_metamethod(
        &mut self,
        callee: InferenceVarId,
        args: PackVarId,
        returns: PackVarId,
    ) {
        let tables: Vec<_> = self.variables[callee].tables.iter().copied().collect();
        for table in tables {
            let metatables: Vec<_> = self.tables[table].metatables.iter().copied().collect();
            for metatable in metatables {
                let method = self.table_field_variable(metatable, "__call".into(), false);
                let args = self.prefixed_pack(vec![callee], args);
                self.add_constraint(method, SolverConstraint::Call { args, returns });
            }
        }
    }
}
