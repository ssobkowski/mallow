use smol_str::SmolStr;

use crate::common::ByteString;
use crate::ty::canonical::{TypeId, TypeLiteral, TypePackId, TypePackTail};
use crate::ty::store::TypeStore;

/// Returns every generated builtin definition.
pub(super) fn definitions() -> &'static [BuiltinDefinition] {
    generated_builtin_definitions()
}

/// One generated global builtin.
#[derive(Debug)]
pub(super) struct BuiltinDefinition {
    /// Global name.
    name: &'static str,
    /// Global generated type definition.
    scheme: BuiltinSchemeDefinition,
}

impl BuiltinDefinition {
    /// Returns the global name.
    pub(super) const fn name(&self) -> &'static str {
        self.name
    }

    /// Interns the definition in `store`.
    pub(super) fn intern(&self, store: &mut TypeStore) -> TypeId {
        self.scheme.intern(store)
    }
}

/// One generated builtin type body and its retained binder definitions.
#[derive(Debug)]
struct BuiltinSchemeDefinition {
    /// Generic binders retained for the future inference rewrite.
    binders: &'static [BuiltinBinderDefinition],
    /// Static type tree to intern.
    body: BuiltinType,
}

/// One generated generic binder retained with its substitution kind.
#[derive(Debug)]
enum BuiltinBinderDefinition {
    /// A binder substituted by one type.
    Type(&'static str),
    /// A binder substituted by one type pack.
    Pack(&'static str),
}

impl BuiltinSchemeDefinition {
    /// Lowers this generated definition into a monomorphic graph type.
    fn intern(&self, store: &mut TypeStore) -> TypeId {
        self.body.intern(store)
    }
}

/// A static builtin type tree generated before runtime type IDs exist.
#[derive(Debug)]
enum BuiltinType {
    /// One canonical primitive kind.
    Primitive(BuiltinPrimitive),
    /// A host-provided nominal type.
    Named(&'static str),
    /// A generic placeholder covered by its generated definition.
    Generic(&'static str),
    /// An exact singleton literal.
    Literal(BuiltinLiteral),
    /// A structural table.
    Table {
        /// Named fields.
        fields: &'static [(&'static str, BuiltinType)],
        /// Optional key and value indexer.
        indexer: Option<(&'static BuiltinType, &'static BuiltinType)>,
    },
    /// A function signature.
    Function {
        /// Accepted argument pack.
        params: BuiltinPack,
        /// Produced return pack.
        returns: BuiltinPack,
    },
    /// A structural union.
    Union(&'static [BuiltinType]),
    /// An overloaded intersection.
    Intersection(&'static [BuiltinType]),
}

impl BuiltinType {
    /// Recursively interns this static tree into the session's canonical store.
    fn intern(&self, store: &mut TypeStore) -> TypeId {
        match self {
            Self::Primitive(primitive) => primitive.id(store),
            Self::Named(name) => store.named(*name),
            Self::Generic(_) => {
                // TODO: Rework builtin generic instantiation with the new generic engine.
                store.primitives().any
            }
            Self::Literal(literal) => store.literal(literal.to_owned()),
            Self::Table { fields, indexer } => {
                let fields = fields
                    .iter()
                    .map(|(name, ty)| (SmolStr::new_static(name), ty.intern(store)))
                    .collect();
                let indexer = indexer.map(|(key, value)| (key.intern(store), value.intern(store)));
                store.table_shape(fields, indexer)
            }
            Self::Function { params, returns } => {
                let params = params.intern(store);
                let returns = returns.intern(store);
                store.function_signature(params, returns)
            }
            Self::Union(members) => {
                let members: Vec<_> = members.into_iter().map(|ty| ty.intern(store)).collect();
                store.union_all(members)
            }
            Self::Intersection(members) => {
                let members: Vec<_> = members.into_iter().map(|ty| ty.intern(store)).collect();
                store.intersection_all(members)
            }
        }
    }
}

/// A static singleton literal used by a generated builtin definition.
#[derive(Debug)]
enum BuiltinLiteral {
    /// One exact string value.
    String(&'static str),
    /// One exact boolean value.
    Boolean(bool),
}

impl BuiltinLiteral {
    /// Creates the owned literal stored in the canonical type graph.
    fn to_owned(&self) -> TypeLiteral {
        match self {
            Self::String(value) => TypeLiteral::String(ByteString::from(*value)),
            Self::Boolean(value) => TypeLiteral::Boolean(*value),
        }
    }
}

/// A primitive builtin kind mapped to the store's preallocated IDs.
#[derive(Debug, Clone, Copy)]
enum BuiltinPrimitive {
    /// Bottom type.
    Never,
    /// Safe top type.
    Unknown,
    /// Dynamic escape type.
    Any,
    /// Nil type.
    Nil,
    /// String type.
    String,
    /// Number type.
    Number,
    /// Native integer type.
    Integer,
    /// Boolean type.
    Boolean,
    /// Thread type.
    Thread,
    /// Vector type.
    Vector,
    /// Buffer type.
    Buffer,
}

impl BuiltinPrimitive {
    /// Returns this primitive's canonical ID in `store`.
    fn id(self, store: &TypeStore) -> TypeId {
        let primitives = store.primitives();
        match self {
            Self::Never => primitives.never,
            Self::Unknown => primitives.unknown,
            Self::Any => primitives.any,
            Self::Nil => primitives.nil,
            Self::String => primitives.string,
            Self::Number => primitives.number,
            Self::Integer => primitives.integer,
            Self::Boolean => primitives.boolean,
            Self::Thread => primitives.thread,
            Self::Vector => primitives.vector,
            Self::Buffer => primitives.buffer,
        }
    }
}

/// A static fixed-prefix function type pack.
#[derive(Debug)]
struct BuiltinPack {
    /// Fixed positional elements.
    head: &'static [BuiltinType],
    /// Optional open tail.
    tail: Option<BuiltinPackTail>,
}

impl BuiltinPack {
    /// Recursively interns this pack and all types it references.
    fn intern(&self, store: &mut TypeStore) -> TypePackId {
        let head = self.head.iter().map(|ty| ty.intern(store)).collect();
        let tail = self.tail.as_ref().map(|tail| tail.intern(store));
        store.pack(head, tail)
    }
}

/// The open tail of a static builtin type pack.
#[derive(Debug)]
enum BuiltinPackTail {
    /// Repeats one type indefinitely.
    Homogeneous(&'static BuiltinType),
    /// References one declared generic type pack.
    Generic(&'static str),
}

impl BuiltinPackTail {
    /// Interns the type carried by this pack tail.
    fn intern(&self, store: &mut TypeStore) -> TypePackTail {
        match self {
            Self::Homogeneous(ty) => TypePackTail::Homogeneous(ty.intern(store)),
            Self::Generic(_) => {
                // TODO: Support generics.
                TypePackTail::Homogeneous(store.primitives().any)
            }
        }
    }
}

include!("builtin_definitions.rs");
