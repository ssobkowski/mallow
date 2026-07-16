use std::{
    collections::{HashMap, hash_map::DefaultHasher},
    hash::{Hash, Hasher},
};

use id_arena::{Arena, Id};
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::{
    disasm::Chunk,
    il::{BytecodeType, Proto, TypeTag},
    operator::BinOp,
};

pub type TypeId = Id<Type>;

/// A Luau type literal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeLiteral {
    String(String),
    Boolean(bool),
}

/// A Luau metamethod.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Metamethod {
    Index,
    NewIndex,
    Call,
    Concat,
    Unm,
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
    ToString,
    Eq,
    Lt,
    Le,
    Len,
    Iter,
}

impl Metamethod {
    /// Returns the field name used by Luau to store this metamethod.
    pub const fn field(self) -> &'static str {
        match self {
            Self::Index => "__index",
            Self::NewIndex => "__newindex",
            Self::Call => "__call",
            Self::Concat => "__concat",
            Self::Unm => "__unm",
            Self::Add => "__add",
            Self::Sub => "__sub",
            Self::Mul => "__mul",
            Self::Div => "__div",
            Self::IDiv => "__idiv",
            Self::Mod => "__mod",
            Self::Pow => "__pow",
            Self::ToString => "__tostring",
            Self::Eq => "__eq",
            Self::Lt => "__lt",
            Self::Le => "__le",
            Self::Len => "__len",
            Self::Iter => "__iter",
        }
    }
}

impl TryFrom<BinOp> for Metamethod {
    type Error = ();

    /// Converts an operator with a binary metamethod into that metamethod.
    fn try_from(op: BinOp) -> Result<Self, Self::Error> {
        match op {
            BinOp::Add => Ok(Self::Add),
            BinOp::Sub => Ok(Self::Sub),
            BinOp::Mul => Ok(Self::Mul),
            BinOp::Div => Ok(Self::Div),
            BinOp::IDiv => Ok(Self::IDiv),
            BinOp::Mod => Ok(Self::Mod),
            BinOp::Pow => Ok(Self::Pow),
            BinOp::Concat => Ok(Self::Concat),
            _ => Err(()),
        }
    }
}

impl TryFrom<&str> for Metamethod {
    type Error = ();

    /// Converts a Luau metamethod field name into its semantic identifier.
    fn try_from(field: &str) -> Result<Self, Self::Error> {
        match field {
            "__index" => Ok(Self::Index),
            "__newindex" => Ok(Self::NewIndex),
            "__call" => Ok(Self::Call),
            "__concat" => Ok(Self::Concat),
            "__unm" => Ok(Self::Unm),
            "__add" => Ok(Self::Add),
            "__sub" => Ok(Self::Sub),
            "__mul" => Ok(Self::Mul),
            "__div" => Ok(Self::Div),
            "__idiv" => Ok(Self::IDiv),
            "__mod" => Ok(Self::Mod),
            "__pow" => Ok(Self::Pow),
            "__tostring" => Ok(Self::ToString),
            "__eq" => Ok(Self::Eq),
            "__lt" => Ok(Self::Lt),
            "__le" => Ok(Self::Le),
            "__len" => Ok(Self::Len),
            "__iter" => Ok(Self::Iter),
            _ => Err(()),
        }
    }
}

/// Surface description of the metamethods attached to a Luau value.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Metatable {
    // Most metatables relevant to one inferred operation expose very few methods.
    // Sparse storage avoids reserving one recursive `Option<Type>` for every
    // possible metamethod while retaining deterministic linear lookup at this size.
    methods: Vec<(Metamethod, Type)>,
}

impl Metatable {
    /// Creates an empty metatable type descriptor.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds or replaces a metamethod type.
    pub fn insert(&mut self, method: Metamethod, ty: Type) {
        if let Some((_, existing)) = self.methods.iter_mut().find(|(m, _)| *m == method) {
            *existing = ty;
            return;
        }

        self.methods.push((method, ty));
        self.methods.sort_by_key(|(method, _)| *method as u8);
    }

    /// Creates a metatable descriptor with one method already defined.
    #[cfg(test)]
    pub fn with_method(mut self, method: Metamethod, ty: Type) -> Self {
        self.insert(method, ty);
        self
    }

    /// Returns every modeled metamethod and its owned surface type.
    pub fn iter(&self) -> impl Iterator<Item = (Metamethod, &Type)> {
        self.methods.iter().map(|(method, ty)| (*method, ty))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionTypeParam {
    /// Typed param, written as `T`
    Type(Type),
    /// Typed vararg, written as `...T`.
    Vararg(Type),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionTypeReturn {
    /// A normal return type.
    Type(Type),
    /// Vararg return type.
    Vararg(Type),
}

/// A Luau type.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum Type {
    /// The `nil` type.
    Nil,
    /// The `string` type.
    String,
    /// The `number` type.
    Number,
    /// The `boolean` type.
    Boolean,
    /// The `table` type, described as `{ [key]: value, foo: bar }`.
    Table {
        fields: HashMap<SmolStr, Type>,
        array: Option<Box<(Type, Type)>>,
    },
    /// The `function` type, described as `<generics>(params) -> return_type`.
    Function {
        /// The generics of the function, such as `<T, U>`.
        generics: Vec<SmolStr>,
        /// The parameters of the function, such as `(number, string)`.
        params: Vec<FunctionTypeParam>,
        /// The return type of the function, such as `string`.
        return_type: Vec<FunctionTypeReturn>,
    },
    /// The `thread` type.
    Thread,
    /// The `userdata` type.
    Userdata,
    /// The `vector` type.
    Vector,
    /// The `integer` type.
    Integer,
    /// The `buffer` type.
    Buffer,
    /// The `unknown` type.
    #[default]
    Unknown,
    /// The `never` type.
    Never,
    /// The `any` type.
    Any,
    /// A named type such as host userdata.
    Named(SmolStr),
    /// The unit type (`()`).
    Unit,
    /// A literal type, such as `"foo"`.
    Literal(TypeLiteral),
    /// A named generic type, such as `<T>`
    Generic(SmolStr),
    /// An union over types, such as `T | U`.
    Union(Vec<Type>),
    /// An intersection type, such as `T & U`.
    Intersection(Vec<Type>),
    /// A type that contains a metatable
    WithMetatable {
        base: Box<Type>,
        metatable: Metatable,
    },
}

impl Hash for Type {
    /// Hashes a surface type independently of `HashMap` field iteration order.
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Type::Table { fields, array } => {
                let mut fields = fields.iter().collect::<Vec<_>>();
                fields.sort_by_key(|(name, _)| (*name).clone());
                fields.len().hash(state);
                for (name, ty) in fields {
                    name.hash(state);
                    ty.hash(state);
                }
                array.hash(state);
            }
            Type::Function {
                generics,
                params,
                return_type,
            } => {
                generics.hash(state);
                params.hash(state);
                return_type.hash(state);
            }
            Type::Named(name) | Type::Generic(name) => name.hash(state),
            Type::Literal(literal) => literal.hash(state),
            Type::Union(types) | Type::Intersection(types) => types.hash(state),
            Type::WithMetatable { base, metatable } => {
                base.hash(state);
                metatable.hash(state);
            }
            Type::Nil
            | Type::String
            | Type::Number
            | Type::Boolean
            | Type::Thread
            | Type::Userdata
            | Type::Vector
            | Type::Integer
            | Type::Buffer
            | Type::Unknown
            | Type::Never
            | Type::Any
            | Type::Unit => {}
        }
    }
}

impl Type {
    /// Converts compact bytecode type information into a printable Luau type.
    ///
    /// Luau bytecode stores only a coarse tag, so this intentionally returns
    /// `None` for tags that should not be emitted as source annotations.
    pub fn from_bytecode_tag(tag: TypeTag, chunk: &Chunk) -> Option<Self> {
        let ty = match tag.ty {
            BytecodeType::Nil => Self::Nil,
            BytecodeType::Boolean => Self::Boolean,
            BytecodeType::Number => Self::Number,
            BytecodeType::String => Self::String,
            BytecodeType::Table => Self::Table {
                fields: HashMap::new(),
                array: None,
            },
            BytecodeType::Function => Self::Function {
                generics: Vec::new(),
                params: vec![FunctionTypeParam::Vararg(Self::Unknown)],
                return_type: vec![FunctionTypeReturn::Vararg(Self::Unknown)],
            },
            BytecodeType::Thread => Self::Thread,
            BytecodeType::Userdata => Self::Userdata,
            BytecodeType::Vector => Self::Vector,
            BytecodeType::Buffer => Self::Buffer,
            BytecodeType::Integer => Self::Integer,
            BytecodeType::Any => Self::Any,
            BytecodeType::Unknown(_) => Self::Unknown,
            BytecodeType::TaggedUserdata(index) => {
                let name = chunk.userdata_type_mappings.as_ref().and_then(|mappings| {
                    mappings
                        .iter()
                        .find(|mapping| mapping.index == index)
                        .and_then(|mapping| mapping.name)
                        .and_then(|name| chunk.get_string(name))
                        .map(|name| name.to_string())
                })?;

                Self::Named(name.into())
            }
        };

        Some(if tag.optional {
            ty.union(Self::Nil)
        } else {
            ty
        })
    }

    /// Returns the union of two types.
    #[must_use]
    pub fn union(self, other: Type) -> Type {
        if self == Self::Any || other == Self::Any {
            return Self::Any;
        }

        let mut variants = Vec::new();

        let mut add_type = |ty: Type| match ty {
            Type::Never => {}
            Type::Union(inner_variants) => {
                for inner in inner_variants {
                    if !variants.contains(&inner) {
                        variants.push(inner);
                    }
                }
            }
            _ => {
                if !variants.contains(&ty) {
                    variants.push(ty);
                }
            }
        };

        add_type(self);
        add_type(other);

        if variants.iter().any(|v| v == &Type::String) {
            variants.retain(|v| !matches!(v, Type::Literal(TypeLiteral::String(_))));
        }
        if variants.iter().any(|v| v == &Type::Boolean) {
            variants.retain(|v| !matches!(v, Type::Literal(TypeLiteral::Boolean(_))));
        }

        match variants.len() {
            0 => Type::Never,
            1 => variants.pop().expect("variants should not be empty"),
            _ => Type::Union(variants),
        }
    }

    /// Returns the binding strength used when emitting a type inside another type.
    pub const fn precedence(&self) -> TypePrecedence {
        match self {
            Type::Function { .. } => TypePrecedence::Function,
            Type::Union(_) => TypePrecedence::Union,
            Type::Intersection(_) => TypePrecedence::Intersection,
            Type::WithMetatable { base, .. } => base.precedence(),
            _ => TypePrecedence::Primary,
        }
    }

    /// Returns whether a bytecode-derived type is useful enough to print as a
    /// source annotation.
    pub fn is_meaningful(&self) -> bool {
        match self {
            Type::Unknown | Type::Any => false,
            Type::Table { fields, array }
                if fields.is_empty()
                    && array.as_ref().is_some_and(|part| {
                        matches!(part.as_ref(), (Type::Unknown, Type::Unknown))
                    }) =>
            {
                false
            }
            Type::Function {
                generics,
                params,
                return_type,
            } if generics.is_empty()
                && matches!(
                    params.as_slice(),
                    [FunctionTypeParam::Vararg(Type::Unknown)]
                )
                && matches!(
                    return_type.as_slice(),
                    [FunctionTypeReturn::Vararg(Type::Unknown)]
                ) =>
            {
                // (...unknown) -> (...unknown)
                false
            }
            Type::Union(types) => types.iter().any(Type::is_meaningful),
            _ => true,
        }
    }

    /// Returns whether this annotation depends on structural metatable semantics.
    pub fn contains_metatable(&self) -> bool {
        match self {
            Self::WithMetatable { .. } => true,
            Self::Table { fields, array } => {
                fields.values().any(Self::contains_metatable)
                    || array.as_ref().is_some_and(|array| {
                        let (key, value) = array.as_ref();
                        key.contains_metatable() || value.contains_metatable()
                    })
            }
            Self::Function {
                params,
                return_type,
                ..
            } => {
                params.iter().any(|param| match param {
                    FunctionTypeParam::Type(ty) | FunctionTypeParam::Vararg(ty) => {
                        ty.contains_metatable()
                    }
                }) || return_type.iter().any(|returned| match returned {
                    FunctionTypeReturn::Type(ty) | FunctionTypeReturn::Vararg(ty) => {
                        ty.contains_metatable()
                    }
                })
            }
            Self::Union(types) | Self::Intersection(types) => {
                types.iter().any(Self::contains_metatable)
            }
            _ => false,
        }
    }

    /// Widens singleton evidence before it becomes a source annotation.
    #[must_use]
    pub fn widen_literals(self) -> Self {
        match self {
            Self::Literal(TypeLiteral::String(_)) => Self::String,
            Self::Literal(TypeLiteral::Boolean(_)) => Self::Boolean,
            Self::Table { fields, array } => Self::Table {
                fields: fields
                    .into_iter()
                    .map(|(name, ty)| (name, ty.widen_literals()))
                    .collect(),
                array: array.map(|array| {
                    let (key, value) = *array;
                    Box::new((key.widen_literals(), value.widen_literals()))
                }),
            },
            Self::Function {
                generics,
                params,
                return_type,
            } => Self::Function {
                generics,
                params: params
                    .into_iter()
                    .map(|param| match param {
                        FunctionTypeParam::Type(ty) => FunctionTypeParam::Type(ty.widen_literals()),
                        FunctionTypeParam::Vararg(ty) => {
                            FunctionTypeParam::Vararg(ty.widen_literals())
                        }
                    })
                    .collect(),
                return_type: return_type
                    .into_iter()
                    .map(|returned| match returned {
                        FunctionTypeReturn::Type(ty) => {
                            FunctionTypeReturn::Type(ty.widen_literals())
                        }
                        FunctionTypeReturn::Vararg(ty) => {
                            FunctionTypeReturn::Vararg(ty.widen_literals())
                        }
                    })
                    .collect(),
            },
            Self::Union(types) => types
                .into_iter()
                .map(Self::widen_literals)
                .fold(Self::Never, Self::union),
            Self::Intersection(types) => {
                Self::Intersection(types.into_iter().map(Self::widen_literals).collect())
            }
            Self::WithMetatable { base, metatable } => Self::WithMetatable {
                base: Box::new(base.widen_literals()),
                metatable,
            },
            ty => ty,
        }
    }

    /// Returns whether this type explicitly includes `nil`.
    pub fn accepts_nil(&self) -> bool {
        match self {
            Self::Nil => true,
            Self::Union(types) => types.iter().any(Self::accepts_nil),
            _ => false,
        }
    }

    /// Returns whether any printable component is still the broad `unknown` type.
    pub fn contains_unknown(&self) -> bool {
        match self {
            Self::Unknown => true,
            Self::Table { fields, array } => {
                fields.values().any(Self::contains_unknown)
                    || array.as_ref().is_some_and(|array| {
                        let (key, value) = array.as_ref();
                        key.contains_unknown() || value.contains_unknown()
                    })
            }
            Self::Function {
                params,
                return_type,
                ..
            } => {
                params.iter().any(|param| match param {
                    FunctionTypeParam::Type(ty) | FunctionTypeParam::Vararg(ty) => {
                        ty.contains_unknown()
                    }
                }) || return_type.iter().any(|returned| match returned {
                    FunctionTypeReturn::Type(ty) | FunctionTypeReturn::Vararg(ty) => {
                        ty.contains_unknown()
                    }
                })
            }
            Self::Union(types) | Self::Intersection(types) => {
                types.iter().any(Self::contains_unknown)
            }
            Self::WithMetatable { base, metatable } => {
                base.contains_unknown()
                    || metatable
                        .iter()
                        .any(|(_, method)| method.contains_unknown())
            }
            _ => false,
        }
    }

    /// Returns whether this type contains type-scheme generic syntax.
    pub fn contains_generic(&self) -> bool {
        match self {
            Self::Generic(_) => true,
            Self::Table { fields, array } => {
                fields.values().any(Self::contains_generic)
                    || array.as_ref().is_some_and(|array| {
                        let (key, value) = array.as_ref();
                        key.contains_generic() || value.contains_generic()
                    })
            }
            Self::Function {
                params,
                return_type,
                ..
            } => {
                params.iter().any(|param| match param {
                    FunctionTypeParam::Type(ty) | FunctionTypeParam::Vararg(ty) => {
                        ty.contains_generic()
                    }
                }) || return_type.iter().any(|returned| match returned {
                    FunctionTypeReturn::Type(ty) | FunctionTypeReturn::Vararg(ty) => {
                        ty.contains_generic()
                    }
                })
            }
            Self::Union(types) | Self::Intersection(types) => {
                types.iter().any(Self::contains_generic)
            }
            Self::WithMetatable { base, .. } => base.contains_generic(),
            _ => false,
        }
    }
}

/// Owns Luau type nodes and exposes cheap handles for HIL metadata.
#[derive(Debug, Default, Clone)]
pub struct TypeStore {
    /// Stable storage for surface type nodes.
    arena: Arena<Type>,
    /// Fingerprint buckets used to avoid linear deep-equality scans.
    fingerprints: HashMap<u64, SmallVec<[TypeId; 1]>>,
}

impl TypeStore {
    /// Stores a type and returns its stable handle.
    #[inline]
    #[must_use]
    pub fn alloc(&mut self, ty: Type) -> TypeId {
        let fingerprint = Self::fingerprint(&ty);
        let id = self.arena.alloc(ty);
        self.fingerprints.entry(fingerprint).or_default().push(id);
        id
    }

    /// Stores `ty` unless an equivalent node is already present, in which
    /// case the existing handle is returned.
    #[inline]
    #[must_use]
    pub fn alloc_unique(&mut self, ty: Type) -> TypeId {
        let fingerprint = Self::fingerprint(&ty);
        if let Some(ids) = self.fingerprints.get(&fingerprint)
            && let Some(matching) = ids.iter().find(|id| self.arena.get(**id) == Some(&ty))
        {
            return *matching;
        }

        self.alloc(ty)
    }

    /// Returns a deterministic fingerprint for one surface type.
    fn fingerprint(ty: &Type) -> u64 {
        let mut hasher = DefaultHasher::new();
        ty.hash(&mut hasher);
        hasher.finish()
    }

    /// Returns the type node for `id`.
    #[inline]
    pub fn get(&self, id: TypeId) -> Option<&Type> {
        self.arena.get(id)
    }

    /// Converts compact bytecode type information into a stored Luau type,
    /// and inserts it into the arena.
    #[inline]
    #[must_use]
    pub fn alloc_bytecode_tag(&mut self, tag: TypeTag, chunk: &Chunk) -> Option<TypeId> {
        Type::from_bytecode_tag(tag, chunk).map(|ty| self.alloc(ty))
    }

    /// Stores and returns the union of two existing type nodes.
    #[inline]
    #[must_use]
    pub fn union(&mut self, lhs: TypeId, rhs: TypeId) -> TypeId {
        if lhs == rhs {
            return lhs;
        }

        let merged = match (self.get(lhs), self.get(rhs)) {
            (Some(lhs), Some(rhs)) => lhs.clone().union(rhs.clone()),
            _ => Type::Unknown,
        };
        if self.get(lhs) == Some(&merged) {
            return lhs;
        }
        if self.get(rhs) == Some(&merged) {
            return rhs;
        }

        self.alloc_unique(merged)
    }
}

/// A bytecode-provided local or temporary type tied to a physical register
/// lifetime.
#[derive(Debug, Clone, PartialEq)]
pub struct LocalTypeBinding {
    pub ty: TypeId,
    pub register: u8,
    pub start_pc: u32,
    pub end_pc: u32,
}

/// Type facts decoded from one proto's bytecode metadata.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ProtoTypeContext {
    params: Vec<Option<TypeId>>,
    upvalues: Vec<Option<TypeId>>,
    locals: Vec<LocalTypeBinding>,
}

impl ProtoTypeContext {
    /// Builds a type context from the compact type records attached to `proto`.
    pub fn from_proto(proto: &Proto, chunk: &Chunk, type_store: &mut TypeStore) -> Self {
        let params = proto
            .type_info
            .function
            .as_ref()
            .map(|function| {
                function
                    .params
                    .iter()
                    .map(|tag| type_store.alloc_bytecode_tag(*tag, chunk))
                    .collect()
            })
            .unwrap_or_default();

        let upvalues = proto
            .type_info
            .upvalues
            .iter()
            .map(|tag| type_store.alloc_bytecode_tag(*tag, chunk))
            .collect();

        let locals = proto
            .type_info
            .locals
            .iter()
            .filter_map(|local| {
                let ty = type_store.alloc_bytecode_tag(local.ty, chunk)?;
                Some(LocalTypeBinding {
                    ty,
                    register: local.register,
                    start_pc: local.start_pc,
                    end_pc: local.end_pc,
                })
            })
            .collect();

        Self {
            params,
            upvalues,
            locals,
        }
    }

    /// Returns the bytecode type for a function parameter, if one exists.
    #[inline]
    pub fn param(&self, index: u8) -> Option<TypeId> {
        self.params.get(index as usize).copied().flatten()
    }

    /// Returns the bytecode type for an upvalue, if one exists.
    #[inline]
    pub fn upvalue(&self, index: u8) -> Option<TypeId> {
        self.upvalues.get(index as usize).copied().flatten()
    }

    /// Returns the bytecode local/temporary type active for `register` at `pc`.
    #[inline]
    pub fn local_at(&self, register: u8, pc: u32) -> Option<TypeId> {
        self.locals
            .iter()
            .find(|local| local.register == register && local.start_pc <= pc && pc < local.end_pc)
            .map(|local| local.ty)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypePrecedence {
    Lowest = 0,
    Function = 1,
    Union = 2,
    Intersection = 3,
    Primary = 4,
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::operator::BinOp;

    use super::{Metamethod, Metatable, Type, TypeStore};

    /// Structurally equal tables share one arena node regardless of field insertion order.
    #[test]
    fn type_store_interns_tables_independent_of_hashmap_order() {
        let mut store = TypeStore::default();
        let lhs = Type::Table {
            fields: HashMap::from([
                ("first".into(), Type::Number),
                ("second".into(), Type::String),
            ]),
            array: None,
        };
        let rhs = Type::Table {
            fields: HashMap::from([
                ("second".into(), Type::String),
                ("first".into(), Type::Number),
            ]),
            array: None,
        };

        assert_eq!(store.alloc_unique(lhs), store.alloc_unique(rhs));
    }

    /// Metatable identity is canonical regardless of method discovery order.
    #[test]
    fn metatable_methods_are_kept_in_canonical_order() {
        let lhs = Metatable::new()
            .with_method(Metamethod::Mul, Type::Number)
            .with_method(Metamethod::Add, Type::String);
        let rhs = Metatable::new()
            .with_method(Metamethod::Add, Type::String)
            .with_method(Metamethod::Mul, Type::Number);

        assert_eq!(lhs, rhs);
    }

    /// Metamethod names and binary operators share one reversible semantic mapping.
    #[test]
    fn metamethod_conversions_are_canonical() {
        assert_eq!(Metamethod::try_from(BinOp::Add), Ok(Metamethod::Add));
        assert_eq!(Metamethod::try_from("__add"), Ok(Metamethod::Add));
        assert_eq!(Metamethod::Add.field(), "__add");
        assert!(Metamethod::try_from(BinOp::And).is_err());
        assert!(Metamethod::try_from("__missing").is_err());
    }
}
