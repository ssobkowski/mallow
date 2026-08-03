//! The canonical, ID-backed HIL type graph.

use std::hash::Hash;

use id_arena::Id;
use smol_str::SmolStr;

/// Stable identity for one canonical type node.
pub type TypeId = Id<Type>;

/// Stable identity for one canonical type pack.
pub type TypePackId = Id<TypePack>;

/// A fixed prefix and optional open tail of type arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypePack {
    /// Positional elements in the pack.
    pub head: Vec<TypeId>,
    /// The homogeneous tail after the fixed prefix.
    pub tail: Option<TypePackTail>,
}

/// A homogeneous variadic tail of a type pack.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypePackTail {
    /// `...T`: repeats one type.
    Homogeneous(TypeId),
}

/// Identifies a Luau metamethod by its runtime operation.
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

/// A callable metatable entry attached to a canonical type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetamethodType {
    /// Runtime metamethod name.
    pub method: Metamethod,
    /// Canonical callable type stored for this method.
    pub ty: TypeId,
}

/// The broad runtime category used by subtype and intersection operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeKind {
    /// The `nil` value.
    Nil,
    /// Strings, including string singleton nodes.
    String,
    /// Numbers. Native integers intentionally have their own kind.
    Number,
    /// Native integer values.
    Integer,
    /// Booleans, including boolean singleton nodes.
    Boolean,
    /// Threads.
    Thread,
    /// Userdata values.
    Userdata,
    /// Vectors.
    Vector,
    /// Buffers.
    Buffer,
    /// Tables, including table shapes and metatabled tables.
    Table,
    /// Functions, including function signatures.
    Function,
}

/// A singleton value represented by a HIL type node.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeLiteral {
    /// One exact string value.
    String(String),
    /// One exact boolean value.
    Boolean(bool),
}

/// One node in the canonical HIL type graph.
///
/// Every recursive edge is an ID. Nodes therefore have one owner and one
/// canonical identity, while graph construction remains centralized in
/// [`crate::hil::ty::store::TypeStore`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// The empty type and lattice bottom.
    Never,
    /// The safe top type.
    Unknown,
    /// The dynamically checked escape type.
    Any,
    /// The `nil` type.
    Nil,
    /// The broad `string` type.
    String,
    /// The broad `number` type.
    Number,
    /// The broad `boolean` type.
    Boolean,
    /// The `thread` type.
    Thread,
    /// The `userdata` type.
    Userdata,
    /// The `vector` type.
    Vector,
    /// The native `integer` type, disjoint from `number`.
    Integer,
    /// The `buffer` type.
    Buffer,
    /// A host-provided named type.
    Named(SmolStr),
    /// An exact singleton literal.
    Literal(TypeLiteral),
    /// The broad table type with no structural information.
    Table,
    /// A table with canonical ordered fields and an optional indexer.
    TableShape {
        /// Named fields sorted lexicographically and containing no duplicates.
        fields: Vec<(SmolStr, TypeId)>,
        /// Homogeneous key/value indexer, if present.
        indexer: Option<(TypeId, TypeId)>,
    },
    /// The broad function type with no signature information.
    Function,
    /// A function with canonical parameter and return packs.
    FunctionSignature {
        /// Accepted argument pack.
        params: TypePackId,
        /// Produced return pack.
        returns: TypePackId,
    },
    /// A structurally normalized union.
    Union(Vec<TypeId>),
    /// A structurally normalized intersection.
    Intersection(Vec<TypeId>),
    /// A base type with statically modeled metamethods.
    WithMetatable {
        /// Type whose runtime behavior is extended.
        base: TypeId,
        /// Ordered, unique metatable methods.
        methods: Vec<MetamethodType>,
    },
}

/// The primitive IDs allocated by a [`TypeStore`].
#[derive(Debug, Clone, Copy)]
pub struct PrimitiveIds {
    /// Bottom.
    pub never: TypeId,
    /// Safe top.
    pub unknown: TypeId,
    /// Dynamic escape type.
    pub any: TypeId,
    /// Nil.
    pub nil: TypeId,
    /// String.
    pub string: TypeId,
    /// Number.
    pub number: TypeId,
    /// Integer.
    pub integer: TypeId,
    /// Boolean.
    pub boolean: TypeId,
    /// True singleton.
    pub true_literal: TypeId,
    /// False singleton.
    pub false_literal: TypeId,
    /// Table.
    pub table: TypeId,
    /// Function.
    pub function: TypeId,
    /// Thread.
    pub thread: TypeId,
    /// Userdata.
    pub userdata: TypeId,
    /// Vector.
    pub vector: TypeId,
    /// Buffer.
    pub buffer: TypeId,
}
