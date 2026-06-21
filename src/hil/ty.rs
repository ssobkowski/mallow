use id_arena::Id;
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::{
    common::is_valid_luau_identifier,
    disasm::Chunk,
    il::{BytecodeType, TypeTag},
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
        generics: Vec<SmolStr>,
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
    /// A custom type with an identifier.
    Var(TypeId),
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
                generics: Vec::new(),
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

                if !is_valid_luau_identifier(&name) {
                    return None;
                }

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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypePrecedence {
    Lowest = 0,
    Function = 1,
    Union = 2,
    Intersection = 3,
    Primary = 4,
}
