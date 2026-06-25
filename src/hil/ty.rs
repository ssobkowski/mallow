use id_arena::{Arena, Id};
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::{
    disasm::Chunk,
    il::{BytecodeType, Proto, TypeTag},
};

pub type TypeId = Id<Type>;

/// A Luau type literal.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeLiteral {
    String(String),
    Boolean(bool),
}

/// A Luau metamethod.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq)]
pub struct Metatable {
    // The reason why this, and not storing each mmd individually, is it would come
    // to about 432 bytes of storing each one as `Option<TypeId>`. For 99% of applications,
    // this vector will never grow past 2 elements - searching for the mmd we need is
    // virtually free.
    methods: SmallVec<[(Metamethod, TypeId); 2]>,
}

impl Metatable {
    /// Returns the type ID for the given metamethod, if one is defined.
    #[inline]
    fn get(&self, method: Metamethod) -> Option<TypeId> {
        self.methods
            .iter()
            .find(|(m, _)| *m == method)
            .map(|(_, id)| *id)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum FunctionTypeParam {
    /// Typed param, written as `T`
    Type(Type),
    /// Typed vararg, written as `...T`.
    Vararg(Type),
}

/// A Luau type.
#[derive(Debug, Default, Clone, PartialEq)]
pub enum Type {
    /// The `nil` type.
    Nil,
    /// The `string` type.
    String,
    /// The `number` type.
    Number,
    /// The `boolean` type.
    Boolean,
    /// The `table` type, described as `{ [key]: value }`.
    Table { key: Box<Type>, value: Box<Type> },
    /// The `function` type, described as `<generics>(params) -> return_type`.
    Function {
        /// The generics of the function, such as `<T, U>`.
        generics: SmallVec<[SmolStr; 3]>,
        /// The parameters of the function, such as `(number, string)`.
        params: Vec<FunctionTypeParam>,
        /// The return type of the function, such as `string`.
        return_type: Option<Box<Type>>,
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
    /// An object type, such as `{ foo: string, bar: number }`.
    Object(Vec<(SmolStr, Type)>),
    /// A type that contains a metatable
    WithMetatable {
        base: Box<Type>,
        metatable: Metatable,
    },
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
                key: Box::new(Self::Unknown),
                value: Box::new(Self::Unknown),
            },
            BytecodeType::Function => Self::Function {
                generics: SmallVec::new(),
                params: vec![FunctionTypeParam::Vararg(Self::Unknown)],
                return_type: Some(Box::new(Self::Unknown)),
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

    /// Returns the intersection of two types.
    pub fn intersection(self, other: Type) -> Type {
        if self == Type::Never || other == Type::Never {
            return Type::Never;
        }

        if self == Type::Any {
            return other;
        }
        if other == Type::Any {
            return self;
        }

        let mut variants = Vec::new();

        let mut add_type = |t: Type| match t {
            Type::Any => {}
            Type::Intersection(inner_variants) => {
                for inner in inner_variants {
                    if !variants.contains(&inner) {
                        variants.push(inner);
                    }
                }
            }
            _ => {
                if !variants.contains(&t) {
                    variants.push(t);
                }
            }
        };

        add_type(self);
        add_type(other);

        match variants.len() {
            0 => Type::Any,
            1 => variants.pop().expect("variants should not be empty"),
            _ => Type::Intersection(variants),
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
            Type::Table { key, value }
                if matches!(key.as_ref(), Type::Unknown)
                    && matches!(value.as_ref(), Type::Unknown) =>
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
                && matches!(return_type.as_deref(), Some(Type::Unknown)) =>
            {
                false
            }
            Type::Union(types) => types
                .iter()
                .filter(|ty| !matches!(ty, Type::Nil))
                .any(Type::is_meaningful),
            _ => true,
        }
    }
}

/// Owns Luau type nodes and exposes cheap handles for HIL metadata.
#[derive(Debug, Clone, Default)]
pub struct TypeStore {
    arena: Arena<Type>,
}

impl TypeStore {
    /// Creates an empty type store.
    pub fn new() -> Self {
        Self::default()
    }

    /// Stores a type and returns its stable handle.
    pub fn alloc(&mut self, ty: Type) -> TypeId {
        self.arena.alloc(ty)
    }

    /// Returns the type node for `id`.
    pub fn get(&self, id: TypeId) -> &Type {
        &self.arena[id]
    }

    /// Converts compact bytecode type information into a stored Luau type,
    /// and inserts it into the arena.
    pub fn from_bytecode_tag(&mut self, tag: TypeTag, chunk: &Chunk) -> Option<TypeId> {
        Type::from_bytecode_tag(tag, chunk).map(|ty| self.alloc(ty))
    }

    /// Stores and returns the union of two existing type nodes.
    pub fn union(&mut self, lhs: TypeId, rhs: TypeId) -> TypeId {
        if lhs == rhs {
            return lhs;
        }

        let merged = self.get(lhs).clone().union(self.get(rhs).clone());
        self.alloc(merged)
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
                    .map(|tag| type_store.from_bytecode_tag(*tag, chunk))
                    .collect()
            })
            .unwrap_or_default();

        let upvalues = proto
            .type_info
            .upvalues
            .iter()
            .map(|tag| type_store.from_bytecode_tag(*tag, chunk))
            .collect();

        let locals = proto
            .type_info
            .locals
            .iter()
            .filter_map(|local| {
                let ty = type_store.from_bytecode_tag(local.ty, chunk)?;
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
    pub fn param(&self, index: u8) -> Option<TypeId> {
        self.params.get(index as usize).copied().flatten()
    }

    /// Returns the bytecode type for an upvalue, if one exists.
    pub fn upvalue(&self, index: u8) -> Option<TypeId> {
        self.upvalues.get(index as usize).copied().flatten()
    }

    /// Returns the bytecode local/temporary type active for `register` at `pc`.
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
