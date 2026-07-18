//! Inference-time value-pack construction, projection, and flow.

use std::collections::HashSet;

use super::model::{
    InferenceVarId, PackAlternative, PackUse, PackVarId, PackVariable, SolverConstraint, TypeSolver,
};
use crate::hil::ty2::inference::program::PackSlot;

/// Reachability facts needed to distinguish finite recursive packs from open packs.
#[derive(Debug, Default)]
struct PackGraphState {
    /// Whether a reachable pack has an explicit or unresolved open source.
    open: bool,
    /// Whether a reachable alternative has a closed end.
    terminal: bool,
    /// Whether a reachable cycle adds at least one value on every traversal.
    positive_cycle: bool,
}

impl TypeSolver<'_> {
    /// Allocates one empty inference-time value pack.
    pub(super) fn fresh_pack(&mut self) -> PackVarId {
        self.packs.alloc(PackVariable::default())
    }

    /// Returns the inference pack corresponding to a durable collected slot.
    pub(super) fn pack_for_slot(&mut self, slot: PackSlot) -> PackVarId {
        if let Some(pack) = self.packs_by_slot.get(&slot) {
            return *pack;
        }
        let pack = self.fresh_pack();
        self.packs_by_slot.insert(slot, pack);
        pack
    }

    /// Creates one closed pack from fixed scalar variables.
    pub(super) fn fixed_pack(&mut self, head: Vec<InferenceVarId>) -> PackVarId {
        let pack = self.fresh_pack();
        self.include_pack_alternative(pack, PackAlternative { head, tail: None });
        pack
    }

    /// Creates one result pack whose requested projections flow into destinations.
    pub(super) fn result_pack(&mut self, destinations: &[InferenceVarId]) -> PackVarId {
        let pack = self.fresh_pack();
        for (index, destination) in destinations.iter().copied().enumerate() {
            let projection = self.project_pack(pack, index);
            self.add_constraint(destination, SolverConstraint::FlowFrom(projection));
        }
        pack
    }

    /// Creates one pack with a fixed prefix followed by `tail`.
    pub(super) fn prefixed_pack(
        &mut self,
        head: Vec<InferenceVarId>,
        tail: PackVarId,
    ) -> PackVarId {
        let pack = self.fresh_pack();
        self.include_pack_alternative(
            pack,
            PackAlternative {
                head,
                tail: Some(tail),
            },
        );
        pack
    }

    /// Adds one concrete sequence alternative and updates every existing pack view.
    pub(super) fn include_pack_alternative(
        &mut self,
        pack: PackVarId,
        alternative: PackAlternative,
    ) -> bool {
        if self.packs[pack].alternatives.contains(&alternative) {
            return false;
        }
        self.packs[pack].alternatives.push(alternative.clone());
        if let Some(tail) = alternative.tail {
            self.pack_uses
                .entry(tail)
                .or_default()
                .insert(PackUse::ShapeTo(pack));
        }
        self.connect_pack_alternative(pack, &alternative);
        self.propagate_pack_alternative(pack, alternative);
        self.pack_changed(pack);
        true
    }

    /// Adds one homogeneous open source to a pack.
    pub(super) fn include_homogeneous_pack(
        &mut self,
        pack: PackVarId,
        value: InferenceVarId,
    ) -> bool {
        if self.packs[pack].homogeneous.contains(&value) {
            return false;
        }
        self.packs[pack].homogeneous.push(value);
        let projections: Vec<_> = self.packs[pack].projections.values().copied().collect();
        for projection in projections {
            self.add_constraint(projection, SolverConstraint::FlowFrom(value));
            self.add_constraint(
                projection,
                SolverConstraint::Observe(self.types.primitives().nil),
            );
        }
        if let Some(values) = self.packs[pack].values {
            self.add_constraint(values, SolverConstraint::FlowFrom(value));
        }
        let uses: Vec<_> = self
            .pack_uses
            .get(&pack)
            .map(|uses| uses.iter().copied().collect())
            .unwrap_or_default();
        for use_ in uses {
            match use_ {
                PackUse::SuffixTo { target, .. } => {
                    self.include_homogeneous_pack(target, value);
                }
                PackUse::FlowTo(_) | PackUse::ShapeTo(_) => {}
            }
        }
        self.pack_changed(pack);
        true
    }

    /// Links `target` to the complete current and future sequence in `source`.
    pub(super) fn add_pack_flow(&mut self, target: PackVarId, source: PackVarId) {
        if target == source {
            return;
        }
        let use_ = PackUse::FlowTo(target);
        if !self.pack_uses.entry(source).or_default().insert(use_) {
            return;
        }
        self.include_pack_alternative(
            target,
            PackAlternative {
                head: Vec::new(),
                tail: Some(source),
            },
        );
    }

    /// Copies all current and future values after `skip` into `target`.
    pub(super) fn add_pack_suffix(&mut self, target: PackVarId, source: PackVarId, skip: usize) {
        if skip == 0 {
            self.add_pack_flow(target, source);
            return;
        }
        let use_ = PackUse::SuffixTo { target, skip };
        if !self.pack_uses.entry(source).or_default().insert(use_) {
            return;
        }
        let alternatives = self.packs[source].alternatives.clone();
        let homogeneous = self.packs[source].homogeneous.clone();
        for alternative in alternatives {
            self.propagate_pack_suffix(target, alternative, skip);
        }
        for value in homogeneous {
            self.include_homogeneous_pack(target, value);
        }
    }

    /// Creates a live suffix view of `source`.
    pub(super) fn pack_suffix(&mut self, source: PackVarId, skip: usize) -> PackVarId {
        let suffix = self.fresh_pack();
        self.add_pack_suffix(suffix, source, skip);
        suffix
    }

    /// Returns a stable scalar variable for one pack position.
    pub(super) fn project_pack(&mut self, pack: PackVarId, index: usize) -> InferenceVarId {
        if let Some(variable) = self.packs[pack].projections.get(&index) {
            return *variable;
        }
        let variable = self.fresh_variable();
        self.packs[pack].projections.insert(index, variable);
        let dependents = self.pack_dependents.get(&pack).cloned().unwrap_or_default();
        self.dependencies
            .entry(variable)
            .or_default()
            .extend(dependents);
        let alternatives = self.packs[pack].alternatives.clone();
        let homogeneous = self.packs[pack].homogeneous.clone();
        for alternative in alternatives {
            self.connect_pack_projection(variable, index, &alternative);
        }
        for source in homogeneous {
            self.add_constraint(variable, SolverConstraint::FlowFrom(source));
            self.add_constraint(
                variable,
                SolverConstraint::Observe(self.types.primitives().nil),
            );
        }
        variable
    }

    /// Returns a stable aggregate variable for values the pack can actually produce.
    pub(super) fn pack_values(&mut self, pack: PackVarId) -> InferenceVarId {
        if let Some(variable) = self.packs[pack].values {
            return variable;
        }
        let variable = self.fresh_variable();
        self.packs[pack].values = Some(variable);
        let alternatives = self.packs[pack].alternatives.clone();
        let homogeneous = self.packs[pack].homogeneous.clone();
        for alternative in alternatives {
            self.connect_pack_values(variable, &alternative);
        }
        for source in homogeneous {
            self.add_constraint(variable, SolverConstraint::FlowFrom(source));
        }
        variable
    }

    /// Returns every contiguous result projection requested by pack consumers.
    pub(super) fn requested_pack_values(&self, pack: PackVarId) -> Option<Vec<InferenceVarId>> {
        if self.packs[pack].values.is_some() {
            return None;
        }
        let Some(maximum) = self.packs[pack].projections.keys().copied().max() else {
            return Some(Vec::new());
        };
        (0..=maximum)
            .map(|index| self.packs[pack].projections.get(&index).copied())
            .collect()
    }

    /// Returns exact positional variables when every alternative has one fixed arity.
    pub(super) fn exact_pack_values(&mut self, pack: PackVarId) -> Option<Vec<InferenceVarId>> {
        let (minimum, maximum) = self.pack_arity(pack);
        let maximum = maximum?;
        if minimum != maximum {
            return None;
        }
        Some(
            (0..maximum)
                .map(|index| self.project_pack(pack, index))
                .collect(),
        )
    }

    /// Returns the minimum arity and optional finite maximum arity of a pack.
    pub(super) fn pack_arity(&self, pack: PackVarId) -> (usize, Option<usize>) {
        let mut state = PackGraphState::default();
        self.inspect_pack_graph(pack, &mut HashSet::new(), &mut state);
        let minimum = self
            .minimum_pack_arity(pack, &mut HashSet::new())
            .unwrap_or(0);
        let maximum = if state.open || state.positive_cycle || !state.terminal {
            None
        } else {
            self.maximum_finite_pack_arity(pack, &mut HashSet::new())
        };
        (minimum, maximum)
    }

    /// Inspects reachable pack cycles and terminal sources.
    fn inspect_pack_graph(
        &self,
        pack: PackVarId,
        visited: &mut HashSet<PackVarId>,
        state: &mut PackGraphState,
    ) {
        if !visited.insert(pack) {
            return;
        }
        let facts = &self.packs[pack];
        if facts.alternatives.is_empty() || !facts.homogeneous.is_empty() {
            state.open = true;
        }
        for alternative in &facts.alternatives {
            if let Some(tail) = alternative.tail {
                if !alternative.head.is_empty()
                    && self.pack_reaches(tail, pack, &mut HashSet::new())
                {
                    state.positive_cycle = true;
                }
                self.inspect_pack_graph(tail, visited, state);
            } else {
                state.terminal = true;
            }
        }
    }

    /// Returns whether following pack-tail edges can reach `target`.
    fn pack_reaches(
        &self,
        pack: PackVarId,
        target: PackVarId,
        visited: &mut HashSet<PackVarId>,
    ) -> bool {
        if pack == target {
            return true;
        }
        if !visited.insert(pack) {
            return false;
        }
        self.packs[pack].alternatives.iter().any(|alternative| {
            alternative
                .tail
                .is_some_and(|tail| self.pack_reaches(tail, target, visited))
        })
    }

    /// Returns the shortest reachable closed or open sequence length.
    fn minimum_pack_arity(
        &self,
        pack: PackVarId,
        visiting: &mut HashSet<PackVarId>,
    ) -> Option<usize> {
        if !visiting.insert(pack) {
            return None;
        }
        let facts = &self.packs[pack];
        let mut minimum =
            (facts.alternatives.is_empty() || !facts.homogeneous.is_empty()).then_some(0usize);
        for alternative in &facts.alternatives {
            let tail = if let Some(tail) = alternative.tail {
                self.minimum_pack_arity(tail, visiting)
            } else {
                Some(0)
            };
            if let Some(tail) = tail {
                let candidate = alternative.head.len().saturating_add(tail);
                minimum = Some(minimum.map_or(candidate, |minimum| minimum.min(candidate)));
            }
        }
        visiting.remove(&pack);
        minimum
    }

    /// Returns the longest finite path after open and productive cycles are excluded.
    fn maximum_finite_pack_arity(
        &self,
        pack: PackVarId,
        visiting: &mut HashSet<PackVarId>,
    ) -> Option<usize> {
        if !visiting.insert(pack) {
            return None;
        }
        let mut maximum = None;
        for alternative in &self.packs[pack].alternatives {
            let tail = if let Some(tail) = alternative.tail {
                self.maximum_finite_pack_arity(tail, visiting)
            } else {
                Some(0)
            };
            if let Some(tail) = tail {
                let candidate = alternative.head.len().saturating_add(tail);
                maximum = Some(maximum.map_or(candidate, |maximum: usize| maximum.max(candidate)));
            }
        }
        visiting.remove(&pack);
        maximum
    }

    /// Wires one newly discovered alternative to existing projections and aggregates.
    fn connect_pack_alternative(&mut self, pack: PackVarId, alternative: &PackAlternative) {
        let projections: Vec<_> = self.packs[pack]
            .projections
            .iter()
            .map(|(index, variable)| (*index, *variable))
            .collect();
        for (index, variable) in projections {
            self.connect_pack_projection(variable, index, alternative);
        }
        if let Some(values) = self.packs[pack].values {
            self.connect_pack_values(values, alternative);
        }
    }

    /// Wires one alternative into one positional projection.
    fn connect_pack_projection(
        &mut self,
        target: InferenceVarId,
        index: usize,
        alternative: &PackAlternative,
    ) {
        if let Some(source) = alternative.head.get(index) {
            self.add_constraint(target, SolverConstraint::FlowFrom(*source));
        } else if let Some(tail) = alternative.tail {
            let source = self.project_pack(tail, index - alternative.head.len());
            self.add_constraint(target, SolverConstraint::FlowFrom(source));
        } else {
            self.add_constraint(
                target,
                SolverConstraint::Observe(self.types.primitives().nil),
            );
        }
    }

    /// Wires one alternative into the aggregate of actually produced values.
    fn connect_pack_values(&mut self, target: InferenceVarId, alternative: &PackAlternative) {
        for source in &alternative.head {
            self.add_constraint(target, SolverConstraint::FlowFrom(*source));
        }
        if let Some(tail) = alternative.tail {
            let source = self.pack_values(tail);
            self.add_constraint(target, SolverConstraint::FlowFrom(source));
        }
    }

    /// Propagates one new alternative to every registered downstream pack relation.
    fn propagate_pack_alternative(&mut self, source: PackVarId, alternative: PackAlternative) {
        let uses: Vec<_> = self
            .pack_uses
            .get(&source)
            .map(|uses| uses.iter().copied().collect())
            .unwrap_or_default();
        for use_ in uses {
            match use_ {
                PackUse::FlowTo(_) | PackUse::ShapeTo(_) => {}
                PackUse::SuffixTo { target, skip } => {
                    self.propagate_pack_suffix(target, alternative.clone(), skip);
                }
            }
        }
    }

    /// Applies one suffix relation to one concrete source alternative.
    fn propagate_pack_suffix(
        &mut self,
        target: PackVarId,
        alternative: PackAlternative,
        skip: usize,
    ) {
        if skip < alternative.head.len() {
            self.include_pack_alternative(
                target,
                PackAlternative {
                    head: alternative.head[skip..].to_vec(),
                    tail: alternative.tail,
                },
            );
        } else if skip == alternative.head.len() {
            if let Some(tail) = alternative.tail {
                self.add_pack_flow(target, tail);
            } else {
                self.include_pack_alternative(
                    target,
                    PackAlternative {
                        head: Vec::new(),
                        tail: None,
                    },
                );
            }
        } else if let Some(tail) = alternative.tail {
            self.add_pack_suffix(target, tail, skip - alternative.head.len());
        } else {
            self.include_pack_alternative(
                target,
                PackAlternative {
                    head: Vec::new(),
                    tail: None,
                },
            );
        }
    }

    /// Re-enqueues constraints that depend directly or indirectly on `pack` shape.
    fn pack_changed(&mut self, pack: PackVarId) {
        self.pack_changed_inner(pack, &mut HashSet::new());
    }

    /// Propagates one shape change without looping through recursive pack flows.
    fn pack_changed_inner(&mut self, pack: PackVarId, visited: &mut HashSet<PackVarId>) {
        if !visited.insert(pack) {
            return;
        }
        let dependents = self.pack_dependents.get(&pack).cloned().unwrap_or_default();
        for dependent in dependents {
            self.queue.push(dependent);
        }
        let targets: Vec<_> = self
            .pack_uses
            .get(&pack)
            .into_iter()
            .flatten()
            .filter_map(|use_| match use_ {
                PackUse::FlowTo(target) | PackUse::ShapeTo(target) => Some(*target),
                PackUse::SuffixTo { .. } => None,
            })
            .collect();
        for target in targets {
            self.pack_changed_inner(target, visited);
        }
    }
}
