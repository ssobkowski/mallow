//! Canonical monotypes used by the inference engine.
//!
//! Printable [`Type`] values are deliberately kept outside the solver. The
//! solver needs canonical identity, cheap sharing, and algebraic operations,
//! whereas the printer needs an owned syntax tree. This module is the boundary
//! between those two representations.

use std::collections::{HashMap, HashSet};

use id_arena::{Arena, Id};
use smol_str::SmolStr;

use crate::hil::ty::{FunctionTypeParam, FunctionTypeReturn, Metamethod, Type, TypeLiteral};

/// Stable handle for a canonical monotype.
pub type MonoTypeId = Id<MonoType>;

/// Stable handle for a canonical Luau type pack.
pub type TypePackId = Id<TypePack>;

/// One canonical Luau type pack.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypePack {
    /// Fixed positional elements before an optional variadic tail.
    pub head: Vec<MonoTypeId>,
    /// Homogeneous variadic tail, when the pack is open.
    pub tail: Option<MonoTypeId>,
}

/// A canonical metatable method entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetamethodType {
    /// Metamethod selected by the runtime operation.
    pub method: Metamethod,
    /// Callable type stored in the metatable field.
    pub ty: MonoTypeId,
}

/// One immutable canonical type node.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MonoType {
    /// The empty type and bottom of the subtype lattice.
    Never,
    /// The safe top type.
    Unknown,
    /// The dynamically checked escape type.
    Any,
    /// The `nil` type.
    Nil,
    /// The `string` type.
    String,
    /// The `number` type.
    Number,
    /// The `boolean` type.
    Boolean,
    /// The `thread` type.
    Thread,
    /// The `userdata` type.
    Userdata,
    /// The `vector` type.
    Vector,
    /// The native `integer` subtype.
    Integer,
    /// The `buffer` type.
    Buffer,
    /// The empty return value `()`.
    Unit,
    /// A named host-provided type.
    Named(SmolStr),
    /// A string singleton type.
    StringLiteral(SmolStr),
    /// A boolean singleton type.
    BooleanLiteral(bool),
    /// The supertype of table values when no shape is known.
    Table,
    /// A structural table type with sorted named fields and an optional indexer.
    TableShape {
        /// Named fields sorted lexicographically for canonical identity.
        fields: Vec<(SmolStr, MonoTypeId)>,
        /// Homogeneous key/value indexer.
        indexer: Option<(MonoTypeId, MonoTypeId)>,
    },
    /// The supertype of callable function values when no signature is known.
    Function,
    /// A canonical function signature.
    FunctionSignature {
        /// Parameter pack accepted by the function.
        params: TypePackId,
        /// Return pack produced by the function.
        returns: TypePackId,
    },
    /// A normalized disjunction containing at least two alternatives.
    Union(Vec<MonoTypeId>),
    /// A normalized conjunction containing at least two components.
    Intersection(Vec<MonoTypeId>),
    /// A base value paired with a statically known metatable.
    WithMetatable {
        /// Underlying value type.
        base: MonoTypeId,
        /// Sorted metatable method entries.
        methods: Vec<MetamethodType>,
    },
}

/// Handles for primitive types allocated once per inference session.
#[derive(Debug, Clone, Copy)]
pub struct PrimitiveTypes {
    /// Canonical `never`.
    pub never: MonoTypeId,
    /// Canonical `unknown`.
    pub unknown: MonoTypeId,
    /// Canonical `any`.
    pub any: MonoTypeId,
    /// Canonical `nil`.
    pub nil: MonoTypeId,
    /// Canonical `string`.
    pub string: MonoTypeId,
    /// Canonical `number`.
    pub number: MonoTypeId,
    /// Canonical `boolean`.
    pub boolean: MonoTypeId,
    /// Canonical singleton `true`.
    pub true_literal: MonoTypeId,
    /// Canonical singleton `false`.
    pub false_literal: MonoTypeId,
    /// Canonical table supertype.
    pub table: MonoTypeId,
    /// Canonical function supertype.
    pub function: MonoTypeId,
    /// Canonical `vector`.
    pub vector: MonoTypeId,
}

/// Owns and interns all monotypes and type packs for one inference run.
#[derive(Debug)]
pub struct TypeArena {
    /// Canonical monotype storage.
    types: Arena<MonoType>,
    /// Hash-consing index for monotypes.
    type_interner: HashMap<MonoType, MonoTypeId>,
    /// Canonical type-pack storage.
    packs: Arena<TypePack>,
    /// Hash-consing index for type packs.
    pack_interner: HashMap<TypePack, TypePackId>,
    /// Primitive nodes shared by every constraint.
    primitives: PrimitiveTypes,
}

impl Default for TypeArena {
    /// Creates an empty arena and allocates its primitive environment.
    fn default() -> Self {
        Self::new()
    }
}

impl TypeArena {
    /// Creates a canonical type arena with all primitive nodes preallocated.
    #[must_use]
    pub fn new() -> Self {
        // Primitive handles are installed only after the interner exists. Keeping
        // this bootstrapping local prevents partially initialized arenas from
        // escaping through the public API.
        let mut types = Arena::new();
        let mut type_interner = HashMap::new();
        let mut intern_primitive = |node: MonoType| {
            let id = types.alloc(node.clone());
            type_interner.insert(node, id);
            id
        };

        let never = intern_primitive(MonoType::Never);
        let unknown = intern_primitive(MonoType::Unknown);
        let any = intern_primitive(MonoType::Any);
        let nil = intern_primitive(MonoType::Nil);
        let string = intern_primitive(MonoType::String);
        let number = intern_primitive(MonoType::Number);
        let boolean = intern_primitive(MonoType::Boolean);
        let true_literal = intern_primitive(MonoType::BooleanLiteral(true));
        let false_literal = intern_primitive(MonoType::BooleanLiteral(false));
        let table = intern_primitive(MonoType::Table);
        let function = intern_primitive(MonoType::Function);
        let vector = intern_primitive(MonoType::Vector);

        Self {
            types,
            type_interner,
            packs: Arena::new(),
            pack_interner: HashMap::new(),
            primitives: PrimitiveTypes {
                never,
                unknown,
                any,
                nil,
                string,
                number,
                boolean,
                true_literal,
                false_literal,
                table,
                function,
                vector,
            },
        }
    }

    /// Returns the primitive handles owned by this arena.
    #[inline]
    #[must_use]
    pub const fn primitives(&self) -> PrimitiveTypes {
        self.primitives
    }

    /// Returns the canonical node for `id`.
    #[inline]
    #[must_use]
    pub fn get(&self, id: MonoTypeId) -> &MonoType {
        self.types
            .get(id)
            .expect("monotype ID must belong to this inference arena")
    }

    /// Returns the canonical pack for `id`.
    #[inline]
    #[must_use]
    pub fn get_pack(&self, id: TypePackId) -> &TypePack {
        self.packs
            .get(id)
            .expect("type-pack ID must belong to this inference arena")
    }

    /// Interns one monotype node and returns its stable identity.
    #[must_use]
    pub fn intern(&mut self, node: MonoType) -> MonoTypeId {
        if let Some(id) = self.type_interner.get(&node) {
            return *id;
        }

        let id = self.types.alloc(node.clone());
        self.type_interner.insert(node, id);
        id
    }

    /// Interns one type pack and returns its stable identity.
    #[must_use]
    pub fn intern_pack(&mut self, pack: TypePack) -> TypePackId {
        if let Some(id) = self.pack_interner.get(&pack) {
            return *id;
        }

        let id = self.packs.alloc(pack.clone());
        self.pack_interner.insert(pack, id);
        id
    }

    /// Lowers a printable type into the canonical monotype arena.
    ///
    /// Generic variables are type-scheme syntax rather than monotypes, so this
    /// method returns `None` when one occurs anywhere inside `ty`.
    pub fn lower_surface(&mut self, ty: &Type) -> Option<MonoTypeId> {
        let node = match ty {
            Type::Never => return Some(self.primitives.never),
            Type::Unknown => return Some(self.primitives.unknown),
            Type::Any => return Some(self.primitives.any),
            Type::Nil => return Some(self.primitives.nil),
            Type::String => return Some(self.primitives.string),
            Type::Number => return Some(self.primitives.number),
            Type::Boolean => return Some(self.primitives.boolean),
            Type::Vector => return Some(self.primitives.vector),
            Type::Thread => MonoType::Thread,
            Type::Userdata => MonoType::Userdata,
            Type::Integer => MonoType::Integer,
            Type::Buffer => MonoType::Buffer,
            Type::Unit => MonoType::Unit,
            Type::Named(name) => MonoType::Named(name.clone()),
            Type::Literal(TypeLiteral::String(value)) => {
                MonoType::StringLiteral(value.as_str().into())
            }
            Type::Literal(TypeLiteral::Boolean(value)) => {
                return Some(if *value {
                    self.primitives.true_literal
                } else {
                    self.primitives.false_literal
                });
            }
            Type::Generic(_) => return None,
            Type::Union(types) => {
                let members = types
                    .iter()
                    .map(|ty| self.lower_surface(ty))
                    .collect::<Option<Vec<_>>>()?;
                return Some(self.union_all(members));
            }
            Type::Intersection(types) => {
                let members = types
                    .iter()
                    .map(|ty| self.lower_surface(ty))
                    .collect::<Option<Vec<_>>>()?;
                return Some(self.intersection_all(members));
            }
            Type::Table { fields, array } => {
                let mut lowered_fields = fields
                    .iter()
                    .map(|(name, ty)| Some((name.clone(), self.lower_surface(ty)?)))
                    .collect::<Option<Vec<_>>>()?;
                lowered_fields.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
                let indexer = match array {
                    Some(array) => {
                        let (key, value) = array.as_ref();
                        Some((self.lower_surface(key)?, self.lower_surface(value)?))
                    }
                    None => None,
                };
                MonoType::TableShape {
                    fields: lowered_fields,
                    indexer,
                }
            }
            Type::Function {
                params,
                return_type,
                ..
            } => {
                let params = self.lower_params(params)?;
                let returns = self.lower_returns(return_type)?;
                MonoType::FunctionSignature { params, returns }
            }
            Type::WithMetatable { base, metatable } => {
                let base = self.lower_surface(base)?;
                let mut methods = Vec::new();
                for (method, ty) in metatable.iter() {
                    methods.push(MetamethodType {
                        method,
                        ty: self.lower_surface(ty)?,
                    });
                }
                methods.sort_by_key(|entry: &MetamethodType| entry.method as u8);
                MonoType::WithMetatable { base, methods }
            }
        };

        Some(self.intern(node))
    }

    /// Lowers a function parameter list into a canonical type pack.
    fn lower_params(&mut self, params: &[FunctionTypeParam]) -> Option<TypePackId> {
        let mut head = Vec::new();
        let mut tail = None;
        for param in params {
            match param {
                FunctionTypeParam::Type(ty) => head.push(self.lower_surface(ty)?),
                FunctionTypeParam::Vararg(ty) => {
                    tail = Some(self.lower_surface(ty)?);
                    break;
                }
            }
        }
        Some(self.intern_pack(TypePack { head, tail }))
    }

    /// Lowers a function return list into a canonical type pack.
    fn lower_returns(&mut self, returns: &[FunctionTypeReturn]) -> Option<TypePackId> {
        let mut head = Vec::new();
        let mut tail = None;
        for ret in returns {
            match ret {
                FunctionTypeReturn::Type(ty) => head.push(self.lower_surface(ty)?),
                FunctionTypeReturn::Vararg(ty) => {
                    tail = Some(self.lower_surface(ty)?);
                    break;
                }
            }
        }
        Some(self.intern_pack(TypePack { head, tail }))
    }

    /// Returns the normalized union of all `members`.
    ///
    /// `any` deterministically takes precedence over `unknown`, regardless of
    /// operand order, because Luau's `any` must retain its escape semantics.
    #[must_use]
    pub fn union_all(&mut self, members: impl IntoIterator<Item = MonoTypeId>) -> MonoTypeId {
        let mut flat = Vec::new();
        let mut has_unknown = false;
        for member in members {
            match self.get(member).clone() {
                MonoType::Never => {}
                MonoType::Unknown => has_unknown = true,
                MonoType::Any => return self.primitives.any,
                MonoType::Union(inner) => flat.extend(inner),
                _ => flat.push(member),
            }
        }

        if has_unknown {
            return self.primitives.unknown;
        }

        flat.sort_unstable();
        flat.dedup();
        let snapshot = flat.clone();
        flat.retain(|candidate| {
            !snapshot
                .iter()
                .any(|other| candidate != other && self.is_subtype(*candidate, *other))
        });

        match flat.as_slice() {
            [] => self.primitives.never,
            [only] => *only,
            _ => self.intern(MonoType::Union(flat)),
        }
    }

    /// Returns the normalized union of `lhs` and `rhs`.
    #[inline]
    #[must_use]
    pub fn union(&mut self, lhs: MonoTypeId, rhs: MonoTypeId) -> MonoTypeId {
        self.union_all([lhs, rhs])
    }

    /// Returns the normalized intersection of all `members`.
    #[must_use]
    pub fn intersection_all(
        &mut self,
        members: impl IntoIterator<Item = MonoTypeId>,
    ) -> MonoTypeId {
        let mut current = self.primitives.unknown;
        for member in members {
            current = self.intersection(current, member);
            if current == self.primitives.never {
                break;
            }
        }
        current
    }

    /// Returns the semantic intersection of `lhs` and `rhs`.
    #[must_use]
    pub fn intersection(&mut self, lhs: MonoTypeId, rhs: MonoTypeId) -> MonoTypeId {
        if lhs == self.primitives.never || rhs == self.primitives.never {
            return self.primitives.never;
        }
        if lhs == self.primitives.any {
            return rhs;
        }
        if rhs == self.primitives.any {
            return lhs;
        }
        if lhs == rhs || self.is_subtype(lhs, rhs) {
            return lhs;
        }
        if self.is_subtype(rhs, lhs) {
            return rhs;
        }

        let lhs_node = self.get(lhs).clone();
        let rhs_node = self.get(rhs).clone();

        if let MonoType::Union(members) = lhs_node {
            let intersections = members
                .into_iter()
                .map(|member| self.intersection(member, rhs))
                .collect::<Vec<_>>();
            return self.union_all(intersections);
        }
        if let MonoType::Union(members) = rhs_node {
            let intersections = members
                .into_iter()
                .map(|member| self.intersection(lhs, member))
                .collect::<Vec<_>>();
            return self.union_all(intersections);
        }

        if self.are_disjoint(lhs, rhs) {
            return self.primitives.never;
        }

        let mut members = Vec::new();
        match self.get(lhs) {
            MonoType::Intersection(inner) => members.extend(inner.iter().copied()),
            _ => members.push(lhs),
        }
        match self.get(rhs) {
            MonoType::Intersection(inner) => members.extend(inner.iter().copied()),
            _ => members.push(rhs),
        }
        members.sort_unstable();
        members.dedup();
        self.intern(MonoType::Intersection(members))
    }

    /// Returns whether every value of `sub` is accepted by `sup`.
    #[must_use]
    pub fn is_subtype(&self, sub: MonoTypeId, sup: MonoTypeId) -> bool {
        if sub == sup {
            return true;
        }

        match (self.get(sub), self.get(sup)) {
            (MonoType::Never, _) | (_, MonoType::Unknown | MonoType::Any) => true,
            (MonoType::Any, _) => true,
            (MonoType::Integer, MonoType::Number) => true,
            (MonoType::StringLiteral(_), MonoType::String) => true,
            (MonoType::BooleanLiteral(_), MonoType::Boolean) => true,
            (MonoType::TableShape { .. } | MonoType::WithMetatable { .. }, MonoType::Table) => true,
            (MonoType::FunctionSignature { .. }, MonoType::Function) => true,
            (MonoType::Union(members), _) => {
                members.iter().all(|member| self.is_subtype(*member, sup))
            }
            (_, MonoType::Union(members)) => {
                members.iter().any(|member| self.is_subtype(sub, *member))
            }
            (MonoType::Intersection(members), _) => {
                members.iter().any(|member| self.is_subtype(*member, sup))
            }
            (_, MonoType::Intersection(members)) => {
                members.iter().all(|member| self.is_subtype(sub, *member))
            }
            (
                MonoType::TableShape {
                    fields: sub_fields,
                    indexer: sub_indexer,
                },
                MonoType::TableShape {
                    fields: sup_fields,
                    indexer: sup_indexer,
                },
            ) => {
                let fields_match = sup_fields.iter().all(|(name, sup_ty)| {
                    sub_fields
                        .iter()
                        .find(|(candidate, _)| candidate == name)
                        .is_some_and(|(_, sub_ty)| self.is_subtype(*sub_ty, *sup_ty))
                });
                let indexer_matches = match (sub_indexer, sup_indexer) {
                    (_, None) => true,
                    (Some((sub_key, sub_value)), Some((sup_key, sup_value))) => {
                        self.is_subtype(*sup_key, *sub_key)
                            && self.is_subtype(*sub_value, *sup_value)
                    }
                    (None, Some(_)) => false,
                };
                fields_match && indexer_matches
            }
            _ => false,
        }
    }

    /// Returns whether an upper bound is precise enough to emit without producer evidence.
    ///
    /// Broad table and function markers stand for values whose structural or
    /// metatable behavior is unknown. They are useful compatibility bounds but
    /// are not valid source annotations for operations requiring that behavior.
    #[must_use]
    pub fn is_emittable_upper_bound(&self, ty: MonoTypeId) -> bool {
        match self.get(ty) {
            MonoType::Never | MonoType::Unknown | MonoType::Any => false,
            MonoType::Table | MonoType::Function => false,
            MonoType::Union(types) | MonoType::Intersection(types) => {
                types.iter().all(|ty| self.is_emittable_upper_bound(*ty))
            }
            _ => true,
        }
    }

    /// Returns whether `lhs` and `rhs` have no common runtime values.
    fn are_disjoint(&self, lhs: MonoTypeId, rhs: MonoTypeId) -> bool {
        let primitive_family = |node: &MonoType| match node {
            MonoType::Nil => Some(0),
            MonoType::String | MonoType::StringLiteral(_) => Some(1),
            MonoType::Number | MonoType::Integer => Some(2),
            MonoType::Boolean | MonoType::BooleanLiteral(_) => Some(3),
            MonoType::Thread => Some(4),
            MonoType::Userdata | MonoType::Named(_) => Some(5),
            MonoType::Vector => Some(6),
            MonoType::Buffer => Some(7),
            MonoType::Unit => Some(8),
            MonoType::Table | MonoType::TableShape { .. } | MonoType::WithMetatable { .. } => {
                Some(9)
            }
            MonoType::Function | MonoType::FunctionSignature { .. } => Some(10),
            _ => None,
        };

        match (self.get(lhs), self.get(rhs)) {
            (MonoType::BooleanLiteral(lhs), MonoType::BooleanLiteral(rhs)) => lhs != rhs,
            (lhs, rhs) => match (primitive_family(lhs), primitive_family(rhs)) {
                (Some(lhs), Some(rhs)) => lhs != rhs,
                _ => false,
            },
        }
    }

    /// Restricts `ty` to values that take a truthy control-flow edge.
    #[must_use]
    pub fn truthy_part(&mut self, ty: MonoTypeId) -> MonoTypeId {
        match self.get(ty).clone() {
            MonoType::Never | MonoType::Nil | MonoType::BooleanLiteral(false) => {
                self.primitives.never
            }
            MonoType::Boolean => self.primitives.true_literal,
            MonoType::Union(members) => {
                let filtered = members
                    .into_iter()
                    .map(|member| self.truthy_part(member))
                    .collect::<Vec<_>>();
                self.union_all(filtered)
            }
            MonoType::Unknown | MonoType::Any => ty,
            _ => ty,
        }
    }

    /// Restricts `ty` to values that take a falsy control-flow edge.
    #[must_use]
    pub fn falsy_part(&mut self, ty: MonoTypeId) -> MonoTypeId {
        match self.get(ty).clone() {
            MonoType::Never => self.primitives.never,
            MonoType::Nil | MonoType::BooleanLiteral(false) => ty,
            MonoType::Boolean => self.primitives.false_literal,
            MonoType::Union(members) => {
                let filtered = members
                    .into_iter()
                    .map(|member| self.falsy_part(member))
                    .collect::<Vec<_>>();
                self.union_all(filtered)
            }
            MonoType::Unknown => self.union(self.primitives.nil, self.primitives.false_literal),
            MonoType::Any => self.primitives.any,
            _ => self.primitives.never,
        }
    }

    /// Removes every union alternative covered by one of `excluded`.
    ///
    /// This operation is used when a generic pattern such as `T | nil`
    /// observes an argument: the concrete `nil` arm must not become evidence
    /// for `T`.
    #[must_use]
    pub fn exclude(&mut self, ty: MonoTypeId, excluded: &[MonoTypeId]) -> MonoTypeId {
        match self.get(ty).clone() {
            MonoType::Union(members) => {
                let retained = members
                    .into_iter()
                    .filter(|member| {
                        !excluded
                            .iter()
                            .any(|excluded| self.is_subtype(*member, *excluded))
                    })
                    .collect::<Vec<_>>();
                self.union_all(retained)
            }
            _ if excluded
                .iter()
                .any(|excluded| self.is_subtype(ty, *excluded)) =>
            {
                self.primitives.never
            }
            _ => ty,
        }
    }

    /// Converts a canonical monotype into a printable owned type tree.
    #[must_use]
    pub fn to_surface(&self, id: MonoTypeId) -> Type {
        let mut visiting = HashSet::new();
        self.to_surface_inner(id, &mut visiting)
    }

    /// Recursively converts one monotype while guarding malformed cycles.
    fn to_surface_inner(&self, id: MonoTypeId, visiting: &mut HashSet<MonoTypeId>) -> Type {
        if !visiting.insert(id) {
            return Type::Unknown;
        }

        let ty = match self.get(id) {
            MonoType::Never => Type::Never,
            MonoType::Unknown => Type::Unknown,
            MonoType::Any => Type::Any,
            MonoType::Nil => Type::Nil,
            MonoType::String => Type::String,
            MonoType::Number => Type::Number,
            MonoType::Boolean => Type::Boolean,
            MonoType::Thread => Type::Thread,
            MonoType::Userdata => Type::Userdata,
            MonoType::Vector => Type::Vector,
            MonoType::Integer => Type::Integer,
            MonoType::Buffer => Type::Buffer,
            MonoType::Unit => Type::Unit,
            MonoType::Named(name) => Type::Named(name.clone()),
            MonoType::StringLiteral(value) => Type::Literal(TypeLiteral::String(value.to_string())),
            MonoType::BooleanLiteral(value) => Type::Literal(TypeLiteral::Boolean(*value)),
            MonoType::Table => Type::Table {
                fields: HashMap::new(),
                array: Some(Box::new((Type::Unknown, Type::Unknown))),
            },
            MonoType::TableShape { fields, indexer } => Type::Table {
                fields: fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.to_surface_inner(*ty, visiting)))
                    .collect(),
                array: indexer.map(|(key, value)| {
                    Box::new((
                        self.to_surface_inner(key, visiting),
                        self.to_surface_inner(value, visiting),
                    ))
                }),
            },
            MonoType::Function => Type::Function {
                generics: Vec::new(),
                params: vec![FunctionTypeParam::Vararg(Type::Unknown)],
                return_type: vec![FunctionTypeReturn::Vararg(Type::Unknown)],
            },
            MonoType::FunctionSignature { params, returns } => {
                let params = self.get_pack(*params);
                let returns = self.get_pack(*returns);
                let mut surface_params = params
                    .head
                    .iter()
                    .map(|ty| FunctionTypeParam::Type(self.to_surface_inner(*ty, visiting)))
                    .collect::<Vec<_>>();
                if let Some(tail) = params.tail {
                    surface_params.push(FunctionTypeParam::Vararg(
                        self.to_surface_inner(tail, visiting),
                    ));
                }
                let mut surface_returns = returns
                    .head
                    .iter()
                    .map(|ty| FunctionTypeReturn::Type(self.to_surface_inner(*ty, visiting)))
                    .collect::<Vec<_>>();
                if let Some(tail) = returns.tail {
                    surface_returns.push(FunctionTypeReturn::Vararg(
                        self.to_surface_inner(tail, visiting),
                    ));
                } else if surface_returns.is_empty() {
                    surface_returns.push(FunctionTypeReturn::Type(Type::Unit));
                }
                Type::Function {
                    generics: Vec::new(),
                    params: surface_params,
                    return_type: surface_returns,
                }
            }
            MonoType::Union(members) => Type::Union(
                members
                    .iter()
                    .map(|member| self.to_surface_inner(*member, visiting))
                    .collect(),
            ),
            MonoType::Intersection(members) => Type::Intersection(
                members
                    .iter()
                    .map(|member| self.to_surface_inner(*member, visiting))
                    .collect(),
            ),
            MonoType::WithMetatable { base, methods } => {
                let mut metatable = crate::hil::ty::Metatable::new();
                for method in methods {
                    metatable.insert(method.method, self.to_surface_inner(method.ty, visiting));
                }
                Type::WithMetatable {
                    base: Box::new(self.to_surface_inner(*base, visiting)),
                    metatable,
                }
            }
        };

        visiting.remove(&id);
        ty
    }
}

#[cfg(test)]
mod tests {
    use super::{MonoType, TypeArena};

    /// Verifies that union construction is canonical and removes covered literals.
    #[test]
    fn union_is_canonical_and_removes_subtypes() {
        let mut arena = TypeArena::new();
        let primitives = arena.primitives();
        let literal = arena.intern(MonoType::StringLiteral("x".into()));

        let lhs = arena.union_all([literal, primitives.number, primitives.string]);
        let rhs = arena.union_all([primitives.string, primitives.number, literal]);

        assert_eq!(lhs, rhs);
        assert!(matches!(arena.get(lhs), MonoType::Union(members) if members.len() == 2));
    }

    /// Verifies that `any` wins over `unknown` independently of operand order.
    #[test]
    fn union_any_precedes_unknown_regardless_of_order() {
        let mut arena = TypeArena::new();
        let primitives = arena.primitives();

        let unknown_then_any = arena.union_all([primitives.unknown, primitives.any]);
        let any_then_unknown = arena.union_all([primitives.any, primitives.unknown]);

        assert_eq!(unknown_then_any, any_then_unknown);
        assert_eq!(unknown_then_any, primitives.any);
    }

    /// Verifies the identity and annihilator laws involving dynamic `any`.
    #[test]
    fn intersection_obeys_any_identity_and_never_annihilator() {
        let mut arena = TypeArena::new();
        let primitives = arena.primitives();

        assert_eq!(
            arena.intersection(primitives.any, primitives.string),
            primitives.string
        );
        assert_eq!(
            arena.intersection(primitives.string, primitives.any),
            primitives.string
        );
        assert_eq!(
            arena.intersection(primitives.never, primitives.any),
            primitives.never
        );
        assert_eq!(
            arena.intersection(primitives.any, primitives.never),
            primitives.never
        );
    }

    /// Verifies that truthiness partitions optional booleans without widening them.
    #[test]
    fn truthiness_partitions_nil_and_boolean_literals() {
        let mut arena = TypeArena::new();
        let primitives = arena.primitives();
        let input = arena.union_all([primitives.nil, primitives.false_literal, primitives.string]);

        assert_eq!(arena.truthy_part(input), primitives.string);
        let falsy = arena.falsy_part(input);
        assert!(matches!(arena.get(falsy), MonoType::Union(members) if members.len() == 2));
    }
}
