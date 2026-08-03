//! Type-specific ownership and canonical graph operations.

use std::collections::{HashMap, HashSet};
use std::hash::{DefaultHasher, Hash, Hasher as _};

use id_arena::{Arena, Id};
use smol_str::SmolStr;

use super::canonical::{
    MetamethodType, PrimitiveIds, RuntimeKind, Type, TypeId, TypeLiteral, TypePack, TypePackId,
    TypePackTail,
};

/// Computes the stable per-run bucket fingerprint for one value.
fn fingerprint<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// A collision-safe hash-consing arena for graph nodes.
///
/// Hashes only select a bucket. Every candidate in that bucket is compared by
/// full structural equality, so a deliberately colliding hash can never merge
/// unequal values.
#[derive(Debug)]
pub struct HashConsArena<T: Hash + Eq> {
    /// Owned values. Allocation is private to [`Self::intern`].
    arena: Arena<T>,
    /// Fingerprint buckets containing candidate IDs.
    buckets: HashMap<u64, Vec<Id<T>>>,
}

impl<T: Hash + Eq> Default for HashConsArena<T> {
    /// Creates an empty hash-consing arena.
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Hash + Eq> HashConsArena<T> {
    /// Creates an empty hash-consing arena.
    #[must_use]
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            buckets: HashMap::new(),
        }
    }

    /// Interns `value`, returning the existing ID when an equal value exists.
    #[must_use]
    pub fn intern(&mut self, value: T) -> Id<T> {
        let fp = fingerprint(&value);
        if let Some(candidates) = self.buckets.get(&fp)
            && let Some(id) = candidates
                .iter()
                .find(|id| self.arena.get(**id) == Some(&value))
        {
            return *id;
        }

        let id = self.arena.alloc(value);
        self.buckets.entry(fp).or_default().push(id);
        id
    }

    /// Returns the value addressed by `id`, or `None` for a foreign ID.
    #[must_use]
    pub fn get(&self, id: Id<T>) -> Option<&T> {
        self.arena.get(id)
    }

    /// Returns the number of owned values.
    #[cfg(test)]
    #[must_use]
    pub fn len(&self) -> usize {
        self.arena.len()
    }
}

/// Owns canonical type nodes and type packs for one inference run.
#[derive(Debug)]
pub struct TypeStore {
    /// Collision-safe storage for recursive type nodes.
    types: HashConsArena<Type>,
    /// Collision-safe storage for function argument and return packs.
    packs: HashConsArena<TypePack>,
    /// IDs of nodes allocated during initialization.
    primitives: PrimitiveIds,
}

impl TypeStore {
    /// Creates a type store and allocates its primitive graph nodes.
    #[must_use]
    pub fn new() -> Self {
        let mut types = HashConsArena::new();
        let primitives = PrimitiveIds {
            never: types.intern(Type::Never),
            unknown: types.intern(Type::Unknown),
            any: types.intern(Type::Any),
            nil: types.intern(Type::Nil),
            string: types.intern(Type::String),
            number: types.intern(Type::Number),
            integer: types.intern(Type::Integer),
            boolean: types.intern(Type::Boolean),
            true_literal: types.intern(Type::Literal(TypeLiteral::Boolean(true))),
            false_literal: types.intern(Type::Literal(TypeLiteral::Boolean(false))),
            table: types.intern(Type::Table),
            function: types.intern(Type::Function),
            thread: types.intern(Type::Thread),
            userdata: types.intern(Type::Userdata),
            vector: types.intern(Type::Vector),
            buffer: types.intern(Type::Buffer),
        };
        Self {
            types,
            packs: HashConsArena::new(),
            primitives,
        }
    }

    /// Borrows primitive IDs without copying the complete primitive set.
    #[must_use]
    pub const fn primitives(&self) -> &PrimitiveIds {
        &self.primitives
    }

    /// Returns the node for `id`, panicking if it came from another store.
    #[must_use]
    pub fn get(&self, id: TypeId) -> &Type {
        self.types
            .get(id)
            .expect("type ID must belong to this TypeStore")
    }

    /// Returns the pack for `id`, panicking if it came from another store.
    #[must_use]
    pub fn get_pack(&self, id: TypePackId) -> &TypePack {
        self.packs
            .get(id)
            .expect("type-pack ID must belong to this TypeStore")
    }

    /// Interns a node after its child IDs have been validated by a constructor.
    fn intern_node(&mut self, node: Type) -> TypeId {
        self.types.intern(node)
    }

    /// Creates a named host type.
    #[must_use]
    pub fn named(&mut self, name: impl Into<SmolStr>) -> TypeId {
        self.intern_node(Type::Named(name.into()))
    }

    /// Creates one literal node and reuses the canonical boolean primitives.
    #[must_use]
    pub fn literal(&mut self, literal: TypeLiteral) -> TypeId {
        match literal {
            TypeLiteral::Boolean(true) => self.primitives.true_literal,
            TypeLiteral::Boolean(false) => self.primitives.false_literal,
            literal => self.intern_node(Type::Literal(literal)),
        }
    }

    /// Creates a type pack after validating every referenced type ID.
    #[must_use]
    pub fn pack(&mut self, head: Vec<TypeId>, tail: Option<TypePackTail>) -> TypePackId {
        for id in &head {
            self.assert_type(*id);
        }
        if let Some(TypePackTail::Homogeneous(id)) = &tail {
            self.assert_type(*id);
        }

        self.packs.intern(TypePack { head, tail })
    }

    /// Creates a structural table shape with ordered, unique field names.
    #[must_use]
    pub fn table_shape(
        &mut self,
        mut fields: Vec<(SmolStr, TypeId)>,
        indexer: Option<(TypeId, TypeId)>,
    ) -> TypeId {
        for (_, id) in &fields {
            self.assert_type(*id);
        }
        if let Some((key, value)) = indexer {
            self.assert_type(key);
            self.assert_type(value);
        }

        fields.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0));
        assert!(
            fields.windows(2).all(|pair| pair[0].0 != pair[1].0),
            "table fields must be unique"
        );

        self.intern_node(Type::TableShape { fields, indexer })
    }

    /// Creates a function signature from canonical argument and return packs.
    #[must_use]
    pub fn function_signature(&mut self, params: TypePackId, returns: TypePackId) -> TypeId {
        self.assert_pack(params);
        self.assert_pack(returns);
        self.intern_node(Type::FunctionSignature { params, returns })
    }

    /// Imports one graph node from another store through canonical constructors.
    ///
    /// IDs are arena-owned, so copying an ID directly would create a foreign
    /// reference. This operation recursively copies child nodes and packs,
    /// while memoizing each source ID and reusing existing target nodes.
    #[must_use]
    pub fn import(&mut self, source: &TypeStore, id: TypeId) -> TypeId {
        source.assert_type(id);
        if self.types.get(id).is_some() {
            return id;
        }
        let mut type_memo = HashMap::new();
        let mut pack_memo = HashMap::new();
        self.import_node(source, id, &mut type_memo, &mut pack_memo)
    }

    /// Recursively imports one node with per-operation memoization.
    fn import_node(
        &mut self,
        source: &TypeStore,
        id: TypeId,
        type_memo: &mut HashMap<TypeId, TypeId>,
        pack_memo: &mut HashMap<TypePackId, TypePackId>,
    ) -> TypeId {
        if let Some(target) = type_memo.get(&id) {
            return *target;
        }
        let node = source.get(id).clone();
        let target = match node {
            Type::Never => self.primitives().never,
            Type::Unknown => self.primitives().unknown,
            Type::Any => self.primitives().any,
            Type::Nil => self.primitives().nil,
            Type::String => self.primitives().string,
            Type::Number => self.primitives().number,
            Type::Boolean => self.primitives().boolean,
            Type::Thread => self.primitives().thread,
            Type::Userdata => self.primitives().userdata,
            Type::Vector => self.primitives().vector,
            Type::Integer => self.primitives().integer,
            Type::Buffer => self.primitives().buffer,
            Type::Named(name) => self.named(name),
            Type::Literal(literal) => self.literal(literal),
            Type::Table => self.primitives().table,
            Type::TableShape { fields, indexer } => {
                let mut imported_fields = Vec::with_capacity(fields.len());
                for (name, child) in fields {
                    imported_fields
                        .push((name, self.import_node(source, child, type_memo, pack_memo)));
                }
                let indexer = if let Some((key, value)) = indexer {
                    Some((
                        self.import_node(source, key, type_memo, pack_memo),
                        self.import_node(source, value, type_memo, pack_memo),
                    ))
                } else {
                    None
                };
                self.table_shape(imported_fields, indexer)
            }
            Type::Function => self.primitives().function,
            Type::FunctionSignature { params, returns } => {
                let params = self.import_pack(source, params, type_memo, pack_memo);
                let returns = self.import_pack(source, returns, type_memo, pack_memo);
                self.function_signature(params, returns)
            }
            Type::Union(parts) => {
                let mut imported = Vec::with_capacity(parts.len());
                for child in parts {
                    imported.push(self.import_node(source, child, type_memo, pack_memo));
                }
                self.union_all(imported)
            }
            Type::Intersection(parts) => {
                let mut imported = Vec::with_capacity(parts.len());
                for child in parts {
                    imported.push(self.import_node(source, child, type_memo, pack_memo));
                }
                self.intersection_all(imported)
            }
            Type::WithMetatable { base, methods } => {
                let base = self.import_node(source, base, type_memo, pack_memo);
                let mut imported_methods = Vec::with_capacity(methods.len());
                for method in methods {
                    imported_methods.push(MetamethodType {
                        method: method.method,
                        ty: self.import_node(source, method.ty, type_memo, pack_memo),
                    });
                }
                self.with_metatable(base, imported_methods)
            }
        };
        type_memo.insert(id, target);
        target
    }

    /// Recursively imports one type pack with per-operation memoization.
    fn import_pack(
        &mut self,
        source: &TypeStore,
        id: TypePackId,
        type_memo: &mut HashMap<TypeId, TypeId>,
        pack_memo: &mut HashMap<TypePackId, TypePackId>,
    ) -> TypePackId {
        if let Some(target) = pack_memo.get(&id) {
            return *target;
        }
        let pack = source.get_pack(id);

        let mut head = Vec::with_capacity(pack.head.len());
        for child in &pack.head {
            head.push(self.import_node(source, *child, type_memo, pack_memo));
        }

        let tail = pack.tail.as_ref().map(|tail| match tail {
            TypePackTail::Homogeneous(id) => {
                TypePackTail::Homogeneous(self.import_node(source, *id, type_memo, pack_memo))
            }
        });

        let target = self.pack(head, tail);
        pack_memo.insert(id, target);
        target
    }

    /// Creates a metatabled type with ordered, unique method entries.
    #[must_use]
    pub fn with_metatable(&mut self, base: TypeId, mut methods: Vec<MetamethodType>) -> TypeId {
        self.assert_type(base);
        for entry in &methods {
            self.assert_type(entry.ty);
        }
        methods.sort_by_key(|entry| entry.method as u8);
        assert!(
            methods
                .windows(2)
                .all(|pair| pair[0].method != pair[1].method),
            "metatable methods must be unique"
        );
        self.intern_node(Type::WithMetatable { base, methods })
    }

    /// Builds a structural union of two members.
    #[must_use]
    pub fn union(&mut self, lhs: TypeId, rhs: TypeId) -> TypeId {
        self.union_all([lhs, rhs])
    }

    /// Builds a structural union by flattening only nested unions and removing exact duplicates.
    #[must_use]
    pub fn union_all<I>(&mut self, members: I) -> TypeId
    where
        I: IntoIterator<Item = TypeId>,
    {
        self.structural_combine(members, CombineMethod::Union)
    }

    /// Builds a structural intersection of two members.
    #[must_use]
    pub fn intersection(&mut self, lhs: TypeId, rhs: TypeId) -> TypeId {
        self.intersection_all([lhs, rhs])
    }

    /// Builds a structural intersection by flattening only nested intersections and removing exact duplicates.
    #[must_use]
    pub fn intersection_all<I>(&mut self, members: I) -> TypeId
    where
        I: IntoIterator<Item = TypeId>,
    {
        self.structural_combine(members, CombineMethod::Intersection)
    }

    /// Computes the semantic lattice join, including subtype absorption and top rules.
    #[must_use]
    pub fn join(&mut self, lhs: TypeId, rhs: TypeId) -> TypeId {
        self.assert_type(lhs);
        self.assert_type(rhs);
        if lhs == rhs {
            return lhs;
        }

        let any = self.primitives.any;
        let never = self.primitives.never;
        let unknown = self.primitives.unknown;

        if lhs == any || rhs == any {
            return any;
        }
        if lhs == never {
            return rhs;
        }
        if rhs == never {
            return lhs;
        }
        if lhs == unknown || rhs == unknown {
            return unknown;
        }
        if self.is_subtype(lhs, rhs) {
            return rhs;
        }
        if self.is_subtype(rhs, lhs) {
            return lhs;
        }
        self.union(lhs, rhs)
    }

    /// Computes the semantic lattice meet, including subtype absorption and bottom rules.
    #[must_use]
    pub fn meet(&mut self, lhs: TypeId, rhs: TypeId) -> TypeId {
        self.assert_type(lhs);
        self.assert_type(rhs);
        if lhs == rhs {
            return lhs;
        }

        let any = self.primitives.any;
        let never = self.primitives.never;
        let unknown = self.primitives.unknown;

        if lhs == never || rhs == never {
            return never;
        }
        if lhs == any {
            return rhs;
        }
        if rhs == any {
            return lhs;
        }
        if lhs == unknown {
            return rhs;
        }
        if rhs == unknown {
            return lhs;
        }
        if self.is_subtype(lhs, rhs) {
            return lhs;
        }
        if self.is_subtype(rhs, lhs) {
            return rhs;
        }
        let left = self.get(lhs).clone();
        let right = self.get(rhs).clone();
        if let Type::Union(parts) = left {
            let mut result = never;
            for part in parts {
                let overlap = self.meet(part, rhs);
                result = self.join(result, overlap);
            }
            return result;
        }
        if let Type::Union(parts) = right {
            let mut result = never;
            for part in parts {
                let overlap = self.meet(lhs, part);
                result = self.join(result, overlap);
            }
            return result;
        }
        if self.are_disjoint(lhs, rhs) {
            return never;
        }
        self.intersection(lhs, rhs)
    }

    /// Computes a left fold of [`Self::join`].
    #[must_use]
    pub fn join_all<I>(&mut self, members: I) -> TypeId
    where
        I: IntoIterator<Item = TypeId>,
    {
        let mut iter = members.into_iter();
        let Some(first) = iter.next() else {
            return self.primitives().never;
        };
        iter.fold(first, |current, next| self.join(current, next))
    }

    /// Returns whether all values represented by `sub` are accepted by `sup`.
    #[must_use]
    pub fn is_subtype(&self, sub: TypeId, sup: TypeId) -> bool {
        let sub_node = self.get(sub);
        let sup_node = self.get(sup);
        if sub == sup {
            return true;
        }
        if matches!(sub_node, Type::Never) || matches!(sup_node, Type::Unknown | Type::Any) {
            return true;
        }
        if matches!(sub_node, Type::Any) {
            return true;
        }
        match (sub_node, sup_node) {
            (Type::Literal(TypeLiteral::String(_)), Type::String)
            | (Type::Literal(TypeLiteral::Boolean(_)), Type::Boolean)
            | (Type::TableShape { .. }, Type::Table)
            | (Type::FunctionSignature { .. }, Type::Function) => true,
            (Type::Union(parts), _) => parts.iter().all(|part| self.is_subtype(*part, sup)),
            (_, Type::Union(parts)) => parts.iter().any(|part| self.is_subtype(sub, *part)),
            (Type::Intersection(parts), _) => parts.iter().any(|part| self.is_subtype(*part, sup)),
            (_, Type::Intersection(parts)) => parts.iter().all(|part| self.is_subtype(sub, *part)),
            (
                Type::TableShape {
                    fields: left,
                    indexer: left_index,
                },
                Type::TableShape {
                    fields: right,
                    indexer: right_index,
                },
            ) => {
                let fields = right.iter().all(|(name, expected)| {
                    left.iter()
                        .find(|(candidate, _)| candidate == name)
                        .is_some_and(|(_, found)| self.is_subtype(*found, *expected))
                });
                let indexer = match (left_index, right_index) {
                    (_, None) => true,
                    (Some((left_key, left_value)), Some((right_key, right_value))) => {
                        self.is_subtype(*right_key, *left_key)
                            && self.is_subtype(*left_value, *right_value)
                    }
                    (None, Some(_)) => false,
                };
                fields && indexer
            }
            (Type::WithMetatable { base, .. }, _) => self.is_subtype(*base, sup),
            _ => false,
        }
    }

    /// Returns whether `evidence` contains any value accepted by `expected`.
    pub fn overlaps(&mut self, evidence: TypeId, expected: TypeId) -> bool {
        self.meet(evidence, expected) != self.primitives.never
    }

    /// Returns the broad runtime category of a type, following metatable bases.
    #[must_use]
    pub fn runtime_kind(&self, id: TypeId) -> Option<RuntimeKind> {
        match self.get(id) {
            Type::Nil => Some(RuntimeKind::Nil),
            Type::String | Type::Literal(TypeLiteral::String(_)) => Some(RuntimeKind::String),
            Type::Number => Some(RuntimeKind::Number),
            Type::Integer => Some(RuntimeKind::Integer),
            Type::Boolean | Type::Literal(TypeLiteral::Boolean(_)) => Some(RuntimeKind::Boolean),
            Type::Thread => Some(RuntimeKind::Thread),
            Type::Userdata | Type::Named(_) => Some(RuntimeKind::Userdata),
            Type::Vector => Some(RuntimeKind::Vector),
            Type::Buffer => Some(RuntimeKind::Buffer),
            Type::Table | Type::TableShape { .. } => Some(RuntimeKind::Table),
            Type::Function | Type::FunctionSignature { .. } => Some(RuntimeKind::Function),
            Type::WithMetatable { base, .. } => self.runtime_kind(*base),
            Type::Union(_) | Type::Intersection(_) | Type::Never | Type::Unknown | Type::Any => {
                None
            }
        }
    }

    /// Returns whether `lhs` and `rhs` have no common runtime values.
    fn are_disjoint(&self, lhs: TypeId, rhs: TypeId) -> bool {
        match (self.get(lhs), self.get(rhs)) {
            (Type::Literal(TypeLiteral::String(lhs)), Type::Literal(TypeLiteral::String(rhs))) => {
                lhs != rhs
            }
            (
                Type::Literal(TypeLiteral::Boolean(lhs)),
                Type::Literal(TypeLiteral::Boolean(rhs)),
            ) => lhs != rhs,
            _ => {
                matches!((self.runtime_kind(lhs), self.runtime_kind(rhs)), (Some(lhs), Some(rhs)) if lhs != rhs)
            }
        }
    }

    /// Flattens matching structural nodes and removes exact duplicate IDs.
    fn structural_combine<I>(&mut self, members: I, method: CombineMethod) -> TypeId
    where
        I: IntoIterator<Item = TypeId>,
    {
        let mut flat = Vec::new();
        for id in members {
            self.assert_type(id);
            match (method, self.get(id)) {
                (CombineMethod::Union, Type::Union(parts))
                | (CombineMethod::Intersection, Type::Intersection(parts)) => {
                    flat.extend(parts.iter().copied())
                }
                _ => flat.push(id),
            }
        }
        flat.sort_unstable();
        flat.dedup();
        match flat.as_slice() {
            [] => match method {
                CombineMethod::Union => self.primitives().never,
                CombineMethod::Intersection => self.primitives().unknown,
            },
            [single] => *single,
            _ => match method {
                CombineMethod::Union => self.intern_node(Type::Union(flat)),
                CombineMethod::Intersection => self.intern_node(Type::Intersection(flat)),
            },
        }
    }

    /// Checks a child type ID and panics on a foreign ID.
    fn assert_type(&self, id: TypeId) {
        let _ = self.get(id);
    }

    /// Checks a child pack ID and panics on a foreign ID.
    fn assert_pack(&self, id: TypePackId) {
        let _ = self.get_pack(id);
    }

    /// Widens singleton literals recursively before source emission.
    #[must_use]
    pub fn widen_literals(&mut self, id: TypeId) -> TypeId {
        match self.get(id).clone() {
            Type::Literal(TypeLiteral::String(_)) => self.primitives().string,
            Type::Literal(TypeLiteral::Boolean(_)) => self.primitives().boolean,
            Type::Union(parts) => {
                let mut result = self.primitives().never;
                for part in parts {
                    let widened = self.widen_literals(part);
                    result = self.join(result, widened);
                }
                result
            }
            Type::Intersection(parts) => {
                let mut widened = Vec::with_capacity(parts.len());
                for part in parts {
                    widened.push(self.widen_literals(part));
                }
                self.intersection_all(widened)
            }
            Type::TableShape { fields, indexer } => {
                let fields = fields
                    .into_iter()
                    .map(|(name, ty)| (name, self.widen_literals(ty)))
                    .collect();
                let indexer = indexer
                    .map(|(key, value)| (self.widen_literals(key), self.widen_literals(value)));
                self.table_shape(fields, indexer)
            }
            Type::FunctionSignature { params, returns } => {
                let params = self.widen_literal_pack(params);
                let returns = self.widen_literal_pack(returns);
                self.function_signature(params, returns)
            }
            Type::WithMetatable { base, methods } => {
                let base = self.widen_literals(base);
                let methods = methods
                    .into_iter()
                    .map(|entry| MetamethodType {
                        method: entry.method,
                        ty: self.widen_literals(entry.ty),
                    })
                    .collect();
                self.with_metatable(base, methods)
            }
            _ => id,
        }
    }

    /// Widens every fixed and variadic type in one function pack.
    #[must_use]
    fn widen_literal_pack(&mut self, id: TypePackId) -> TypePackId {
        let pack = self.get_pack(id).clone();
        let mut head = Vec::with_capacity(pack.head.len());
        for ty in pack.head {
            head.push(self.widen_literals(ty));
        }
        let tail = pack.tail.map(|tail| match tail {
            TypePackTail::Homogeneous(ty) => TypePackTail::Homogeneous(self.widen_literals(ty)),
        });
        self.pack(head, tail)
    }

    /// Returns the truthy restriction used by conditional inference.
    #[must_use]
    pub fn truthy_part(&mut self, id: TypeId) -> TypeId {
        match self.get(id).clone() {
            Type::Never | Type::Nil | Type::Literal(TypeLiteral::Boolean(false)) => {
                self.primitives().never
            }
            Type::Boolean => self.primitives().true_literal,
            Type::Union(parts) => {
                let mut result = self.primitives().never;
                for part in parts {
                    let truthy = self.truthy_part(part);
                    result = self.join(result, truthy);
                }
                result
            }
            Type::Unknown | Type::Any => id,
            _ => id,
        }
    }

    /// Returns the falsy restriction used by conditional inference.
    #[must_use]
    pub fn falsy_part(&mut self, id: TypeId) -> TypeId {
        match self.get(id).clone() {
            Type::Never => self.primitives().never,
            Type::Nil | Type::Literal(TypeLiteral::Boolean(false)) => id,
            Type::Boolean => self.primitives().false_literal,
            Type::Union(parts) => {
                let mut result = self.primitives().never;
                for part in parts {
                    let falsy = self.falsy_part(part);
                    result = self.join(result, falsy);
                }
                result
            }
            Type::Unknown => self.join(self.primitives().nil, self.primitives().false_literal),
            Type::Any => self.primitives().any,
            _ => self.primitives().never,
        }
    }

    /// Removes alternatives covered by `excluded` from a union.
    #[must_use]
    pub fn exclude(&mut self, id: TypeId, excluded: &[TypeId]) -> TypeId {
        for excluded_id in excluded {
            self.assert_type(*excluded_id);
        }
        match self.get(id).clone() {
            Type::Union(parts) => {
                let mut retained = Vec::new();
                for part in parts {
                    if !excluded
                        .iter()
                        .any(|excluded_id| self.is_subtype(part, *excluded_id))
                    {
                        retained.push(part);
                    }
                }
                self.join_all(retained)
            }
            _ if excluded
                .iter()
                .any(|excluded_id| self.is_subtype(id, *excluded_id)) =>
            {
                self.primitives().never
            }
            _ => id,
        }
    }

    /// Returns whether a type is precise enough to emit as an upper bound.
    #[must_use]
    pub fn is_emittable_upper_bound(&self, id: TypeId) -> bool {
        match self.get(id) {
            Type::Never | Type::Unknown | Type::Any | Type::Table | Type::Function => false,
            Type::Union(parts) | Type::Intersection(parts) => parts
                .iter()
                .all(|part| self.is_emittable_upper_bound(*part)),
            _ => true,
        }
    }

    /// Returns whether a graph node contains an unresolved `unknown` child.
    #[must_use]
    pub fn contains_unknown(&self, id: TypeId) -> bool {
        let mut visited = HashSet::new();
        self.contains_unknown_inner(id, &mut visited)
    }

    /// Traverses one node for [`Self::contains_unknown`].
    fn contains_unknown_inner(&self, id: TypeId, visited: &mut HashSet<TypeId>) -> bool {
        if !visited.insert(id) {
            return false;
        }
        match self.get(id) {
            Type::Unknown => true,
            Type::TableShape { fields, indexer } => {
                fields
                    .iter()
                    .any(|(_, ty)| self.contains_unknown_inner(*ty, visited))
                    || indexer.is_some_and(|(key, value)| {
                        self.contains_unknown_inner(key, visited)
                            || self.contains_unknown_inner(value, visited)
                    })
            }
            Type::FunctionSignature { params, returns } => {
                self.pack_contains_unknown(*params, visited)
                    || self.pack_contains_unknown(*returns, visited)
            }
            Type::Union(parts) | Type::Intersection(parts) => parts
                .iter()
                .any(|ty| self.contains_unknown_inner(*ty, visited)),
            Type::WithMetatable { base, methods } => {
                self.contains_unknown_inner(*base, visited)
                    || methods
                        .iter()
                        .any(|method| self.contains_unknown_inner(method.ty, visited))
            }
            _ => false,
        }
    }

    /// Returns whether a pack contains an unresolved `unknown` child.
    #[must_use]
    fn pack_contains_unknown(&self, id: TypePackId, visited: &mut HashSet<TypeId>) -> bool {
        let pack = self.get_pack(id);
        pack.head
            .iter()
            .any(|ty| self.contains_unknown_inner(*ty, visited))
            || pack.tail.as_ref().is_some_and(|tail| match tail {
                TypePackTail::Homogeneous(ty) => self.contains_unknown_inner(*ty, visited),
            })
    }

    /// Returns whether a node or any child carries metatable behavior.
    #[must_use]
    pub fn contains_metatable(&self, id: TypeId) -> bool {
        match self.get(id) {
            Type::WithMetatable { .. } => true,
            Type::TableShape { fields, indexer } => {
                fields.iter().any(|(_, ty)| self.contains_metatable(*ty))
                    || indexer.is_some_and(|(key, value)| {
                        self.contains_metatable(key) || self.contains_metatable(value)
                    })
            }
            Type::FunctionSignature { params, returns } => {
                self.pack_contains_metatable(*params) || self.pack_contains_metatable(*returns)
            }
            Type::Union(parts) | Type::Intersection(parts) => {
                parts.iter().any(|ty| self.contains_metatable(*ty))
            }
            _ => false,
        }
    }

    /// Returns whether a type is useful enough to emit as a source annotation.
    #[must_use]
    pub fn is_meaningful(&self, id: TypeId) -> bool {
        match self.get(id) {
            Type::Unknown | Type::Any | Type::Table | Type::Function => false,
            Type::TableShape { fields, indexer }
                if fields.is_empty()
                    && indexer.is_some_and(|(key, value)| {
                        key == self.primitives.unknown && value == self.primitives.unknown
                    }) =>
            {
                false
            }
            Type::FunctionSignature { params, returns }
                if self.is_unknown_variadic_pack(*params)
                    && self.is_unknown_variadic_pack(*returns) =>
            {
                false
            }
            Type::Union(parts) => parts.iter().any(|ty| self.is_meaningful(*ty)),
            _ => true,
        }
    }

    /// Returns whether one graph type can be emitted as a useful source annotation.
    #[must_use]
    pub fn is_emittable_annotation(&self, id: TypeId) -> bool {
        self.is_meaningful(id) && !self.contains_unknown(id)
    }

    /// Returns whether every element of a return pack can be emitted faithfully.
    ///
    /// An empty pack is meaningful because `: ()` distinguishes a function that
    /// returns no values from one whose return behavior was left unannotated.
    #[must_use]
    pub fn is_emittable_return_pack(&self, id: TypePackId) -> bool {
        let pack = self.get_pack(id);
        pack.head.iter().all(|ty| self.is_emittable_annotation(*ty))
            && pack.tail.as_ref().is_none_or(|tail| match tail {
                TypePackTail::Homogeneous(ty) => self.is_emittable_annotation(*ty),
            })
    }

    /// Returns whether a pack is exactly one unknown variadic tail.
    fn is_unknown_variadic_pack(&self, id: TypePackId) -> bool {
        let pack = self.get_pack(id);
        pack.head.is_empty()
            && pack.tail == Some(TypePackTail::Homogeneous(self.primitives.unknown))
    }

    /// Returns whether any type in a pack has metatable behavior.
    fn pack_contains_metatable(&self, id: TypePackId) -> bool {
        let pack = self.get_pack(id);
        pack.head.iter().any(|ty| self.contains_metatable(*ty))
            || pack.tail.as_ref().is_some_and(|tail| match tail {
                TypePackTail::Homogeneous(ty) => self.contains_metatable(*ty),
            })
    }
}

/// How to combine types.
#[derive(Debug, Clone, Copy)]
enum CombineMethod {
    Union,
    Intersection,
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};

    use super::{HashConsArena, MetamethodType, RuntimeKind, Type, TypeLiteral, TypeStore};
    use crate::hil::ty::canonical::{Metamethod, TypePackTail};

    /// A test value whose every fingerprint collides.
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Colliding(u8);

    impl Hash for Colliding {
        /// Deliberately hashes every value into one bucket.
        fn hash<H: Hasher>(&self, state: &mut H) {
            0_u8.hash(state);
        }
    }

    /// Hash collisions must not merge unequal values.
    #[test]
    fn hash_cons_arena_checks_structural_equality_after_collision() {
        let mut arena = HashConsArena::new();
        let first = arena.intern(Colliding(1));
        let second = arena.intern(Colliding(2));
        assert_ne!(first, second);
        assert_eq!(arena.intern(Colliding(1)), first);
        assert_eq!(arena.len(), 2);
    }

    /// Foreign child IDs are rejected instead of silently indexing another graph.
    #[test]
    #[should_panic(expected = "type ID must belong to this TypeStore")]
    fn foreign_type_ids_fail_loudly() {
        let mut first = TypeStore::new();
        let second = TypeStore::new();
        let _ = first.table_shape(vec![("field".into(), second.primitives().string)], None);
    }

    /// Canonical table shapes reject duplicate field names.
    #[test]
    #[should_panic(expected = "table fields must be unique")]
    fn duplicate_table_fields_fail_loudly() {
        let mut store = TypeStore::new();
        let string = store.primitives().string;
        let _ = store.table_shape(
            vec![("field".into(), string), ("field".into(), string)],
            None,
        );
    }

    /// Canonical metatables reject duplicate method entries.
    #[test]
    #[should_panic(expected = "metatable methods must be unique")]
    fn duplicate_metatable_methods_fail_loudly() {
        let mut store = TypeStore::new();
        let function = store.primitives().function;
        let table = store.primitives().table;
        let methods = vec![
            MetamethodType {
                method: Metamethod::Call,
                ty: function,
            },
            MetamethodType {
                method: Metamethod::Call,
                ty: function,
            },
        ];
        let _ = store.with_metatable(table, methods);
    }

    /// Structural operators retain lattice markers while lattice operators absorb them.
    #[test]
    fn structural_and_lattice_operators_have_distinct_absorption_semantics() {
        let mut store = TypeStore::new();
        let never = store.primitives().never;
        let unknown = store.primitives().unknown;
        let string = store.primitives().string;
        let structural_union = store.union(never, string);
        let lattice_join = store.join(never, string);
        let structural_intersection = store.intersection(unknown, string);
        let lattice_meet = store.meet(unknown, string);
        assert!(
            matches!(store.get(structural_union), Type::Union(parts) if parts.contains(&never) && parts.contains(&string))
        );
        assert!(
            matches!(store.get(structural_intersection), Type::Intersection(parts) if parts.contains(&unknown) && parts.contains(&string))
        );
        assert_eq!(lattice_join, string);
        assert_eq!(lattice_meet, string);
        assert_ne!(structural_union, lattice_join);
        assert_ne!(structural_intersection, lattice_meet);
    }

    /// Integer and number are disjoint, while distinct string singletons are disjoint.
    #[test]
    fn runtime_kinds_preserve_integer_and_singleton_disjointness() {
        let mut store = TypeStore::new();
        let integer = store.primitives().integer;
        let number = store.primitives().number;
        let left = store.literal(TypeLiteral::String("left".into()));
        let right = store.literal(TypeLiteral::String("right".into()));
        assert_eq!(store.meet(integer, number), store.primitives().never);
        assert_eq!(store.meet(left, right), store.primitives().never);
    }

    /// Metatables preserve the runtime category and subtyping of their base value.
    #[test]
    fn metatable_runtime_kind_and_subtyping_follow_the_base() {
        let mut store = TypeStore::new();
        let number = store.primitives().number;
        let table = store.primitives().table;
        let metatabled_number = store.with_metatable(number, Vec::new());

        assert_eq!(
            store.runtime_kind(metatabled_number),
            Some(RuntimeKind::Number)
        );
        assert!(!store.is_subtype(metatabled_number, table));
        assert!(store.is_subtype(metatabled_number, number));
    }

    /// Nested graph and pack imports copy every child and reuse target nodes.
    #[test]
    fn imports_nested_function_graphs_without_foreign_ids() {
        let mut source = TypeStore::new();
        let field = source.literal(TypeLiteral::String("field".into()));
        let shape = source.table_shape(vec![("value".into(), field)], None);
        let number = source.primitives().number;
        let params = source.pack(vec![shape], Some(TypePackTail::Homogeneous(number)));
        let returns = source.pack(Vec::new(), None);
        let function = source.function_signature(params, returns);

        let mut target = TypeStore::new();
        let imported = target.import(&source, function);
        let reused = target.import(&source, function);
        assert_eq!(imported, reused);
        let Type::FunctionSignature { params, returns } = target.get(imported) else {
            panic!("imported node must remain a function signature")
        };
        assert_eq!(target.get_pack(*returns).head.len(), 0);
        assert_eq!(target.get_pack(*params).head.len(), 1);
        assert_eq!(
            target.get_pack(*params).tail,
            Some(TypePackTail::Homogeneous(target.primitives().number))
        );
        let Type::TableShape { fields, .. } = target.get(target.get_pack(*params).head[0]) else {
            panic!("nested table shape must be imported")
        };
        assert_eq!(fields.len(), 1);
    }

    /// Broad table/function nodes remain distinct from empty structural nodes.
    #[test]
    fn broad_and_structural_callable_container_types_are_distinct() {
        let mut store = TypeStore::new();
        let broad_table = store.primitives().table;
        let empty_shape = store.table_shape(Vec::new(), None);
        let broad_function = store.primitives().function;
        let empty_pack = store.pack(Vec::new(), None);
        let empty_signature = store.function_signature(empty_pack, empty_pack);
        assert!(matches!(store.get(broad_table), Type::Table));
        assert!(
            matches!(store.get(empty_shape), Type::TableShape { fields, indexer } if fields.is_empty() && indexer.is_none())
        );
        assert!(matches!(store.get(broad_function), Type::Function));
        assert!(
            matches!(store.get(empty_signature), Type::FunctionSignature { params, returns } if *params == empty_pack && *returns == empty_pack)
        );
        assert_ne!(broad_table, empty_shape);
        assert_ne!(broad_function, empty_signature);
    }

    /// Literal widening traverses every fixed and variadic function pack slot.
    #[test]
    fn widens_literals_nested_in_function_signature_packs() {
        let mut store = TypeStore::new();
        let string_literal = store.literal(TypeLiteral::String("value".into()));
        let false_literal = store.literal(TypeLiteral::Boolean(false));
        let true_literal = store.literal(TypeLiteral::Boolean(true));
        let params = store.pack(
            vec![string_literal],
            Some(TypePackTail::Homogeneous(false_literal)),
        );
        let returns = store.pack(
            vec![true_literal],
            Some(TypePackTail::Homogeneous(string_literal)),
        );
        let signature = store.function_signature(params, returns);

        let widened = store.widen_literals(signature);
        let Type::FunctionSignature { params, returns } = store.get(widened) else {
            panic!("widened function must remain a structural signature")
        };
        let params = store.get_pack(*params).clone();
        let returns = store.get_pack(*returns).clone();
        assert_eq!(params.head, vec![store.primitives().string]);
        assert_eq!(
            params.tail,
            Some(TypePackTail::Homogeneous(store.primitives().boolean))
        );
        assert_eq!(returns.head, vec![store.primitives().boolean]);
        assert_eq!(
            returns.tail,
            Some(TypePackTail::Homogeneous(store.primitives().string))
        );
    }
}
