use std::collections::HashMap;

use smol_str::SmolStr;

use crate::hil::{
    ir::Expr,
    ty2::{
        canonical::{GenericBinder, TypeId, TypeLiteral, TypePackId, TypePackTail, TypeScheme},
        store::TypeStore,
    },
};

/// Immutable builtin type schemes allocated once for an inference session.
#[derive(Debug)]
pub struct BuiltinEnvironment {
    /// Global names mapped to their polymorphic graph schemes.
    globals: HashMap<SmolStr, TypeScheme>,
    /// Namespace fields indexed without allocating temporary schemes.
    namespace_fields: HashMap<(SmolStr, SmolStr), TypeScheme>,
}

/// Stable symbolic reference into a [`BuiltinEnvironment`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BuiltinPath {
    /// A direct global builtin.
    Global(SmolStr),
    /// A field exported by a global builtin namespace.
    NamespaceField {
        /// Global namespace name.
        namespace: SmolStr,
        /// Field selected from the namespace.
        field: SmolStr,
    },
}

/// One argument source used by a builtin indexed-write effect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BuiltinIndex {
    /// Uses the argument at this zero-based call position.
    Argument(usize),
    /// Synthesizes the numeric array index used by append-like operations.
    Number,
}

/// A heap effect attached to one builtin call shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BuiltinCallEffect {
    /// Writes one value into an indexed table slot.
    SetIndex {
        /// Zero-based argument containing the mutated table.
        table_argument: usize,
        /// Source of the written index.
        index: BuiltinIndex,
        /// Zero-based argument containing the written value.
        value_argument: usize,
    },
    /// Attaches one metatable and returns the base table.
    SetMetatable {
        /// Zero-based argument containing the base table.
        table_argument: usize,
        /// Zero-based argument containing the metatable.
        metatable_argument: usize,
    },
}

impl BuiltinPath {
    /// Returns every heap effect possible for an argument arity range.
    pub(super) fn call_effects(
        &self,
        minimum: usize,
        maximum: Option<usize>,
    ) -> Vec<BuiltinCallEffect> {
        let includes =
            |arity: usize| minimum <= arity && maximum.is_none_or(|maximum| arity <= maximum);
        let reaches = |arity: usize| maximum.is_none_or(|maximum| maximum >= arity);
        match self {
            Self::Global(name) if name == "setmetatable" && reaches(2) => {
                vec![BuiltinCallEffect::SetMetatable {
                    table_argument: 0,
                    metatable_argument: 1,
                }]
            }
            Self::Global(name) if name == "rawset" && reaches(3) => {
                vec![BuiltinCallEffect::SetIndex {
                    table_argument: 0,
                    index: BuiltinIndex::Argument(1),
                    value_argument: 2,
                }]
            }
            Self::NamespaceField { namespace, field }
                if namespace == "table" && field == "insert" =>
            {
                let mut effects = Vec::new();
                if includes(2) {
                    effects.push(BuiltinCallEffect::SetIndex {
                        table_argument: 0,
                        index: BuiltinIndex::Number,
                        value_argument: 1,
                    });
                }
                if includes(3) {
                    effects.push(BuiltinCallEffect::SetIndex {
                        table_argument: 0,
                        index: BuiltinIndex::Argument(1),
                        value_argument: 2,
                    });
                }
                effects
            }
            _ => Vec::new(),
        }
    }
}

impl BuiltinPath {
    /// Recognizes a syntactic builtin path without allocating its type.
    #[must_use]
    pub fn from_expr(expr: &Expr) -> Option<Self> {
        match expr {
            Expr::Global(name) => Some(Self::Global(name.clone())),
            Expr::GetField { obj, field } => {
                let Expr::Global(namespace) = obj.as_ref() else {
                    return None;
                };
                Some(Self::NamespaceField {
                    namespace: namespace.clone(),
                    field: field.clone(),
                })
            }
            _ => None,
        }
    }
}

impl BuiltinEnvironment {
    /// Builds every builtin type scheme exactly once.
    #[must_use]
    pub fn new(type_store: &mut TypeStore) -> Self {
        let definitions = generated_builtin_definitions();
        let mut globals = HashMap::with_capacity(definitions.len());
        let mut namespace_fields = HashMap::new();
        for definition in definitions {
            let BuiltinDefinition {
                name,
                scheme,
                fields,
            } = definition;
            let name = SmolStr::new(name);
            let previous = globals.insert(name.clone(), scheme.intern(type_store));
            assert!(
                previous.is_none(),
                "generated builtin globals must be unique"
            );

            for field in fields {
                let field_name = SmolStr::new(field.name);
                let previous = namespace_fields
                    .insert((name.clone(), field_name), field.scheme.intern(type_store));
                assert!(
                    previous.is_none(),
                    "generated builtin namespace fields must be unique"
                );
            }
        }
        Self {
            globals,
            namespace_fields,
        }
    }

    /// Returns the type scheme at a previously recognized builtin path.
    #[must_use]
    pub fn get_path(&self, path: &BuiltinPath) -> Option<&TypeScheme> {
        match path {
            BuiltinPath::Global(name) => self.globals.get(name),
            BuiltinPath::NamespaceField { namespace, field } => self
                .namespace_fields
                .get(&(namespace.clone(), field.clone())),
        }
    }
}

/// One generated global builtin and its independently bound namespace fields.
#[derive(Debug)]
struct BuiltinDefinition {
    /// Global name.
    name: String,
    /// Global type scheme.
    scheme: BuiltinSchemeDefinition,
    /// Direct namespace field schemes.
    fields: Vec<BuiltinFieldDefinition>,
}

/// One direct field exported by a builtin namespace.
#[derive(Debug)]
struct BuiltinFieldDefinition {
    /// Exported field name.
    name: String,
    /// Independently instantiated field scheme.
    scheme: BuiltinSchemeDefinition,
}

/// One owned type body and its build-time-computed binders.
#[derive(Debug)]
struct BuiltinSchemeDefinition {
    /// Type and type-pack binders in declaration order.
    binders: Vec<BuiltinBinderDefinition>,
    /// Owned type tree to intern.
    body: BuiltinType,
}

/// One generated generic binder retained with its substitution kind.
#[derive(Debug)]
enum BuiltinBinderDefinition {
    /// A binder substituted by one type.
    Type(String),
    /// A binder substituted by one type pack.
    Pack(String),
}

impl BuiltinSchemeDefinition {
    /// Interns this owned definition and validates its precomputed binders.
    fn intern(self, store: &mut TypeStore) -> TypeScheme {
        let body = self.body.intern(store);
        let binders = self
            .binders
            .into_iter()
            .map(|binder| match binder {
                BuiltinBinderDefinition::Type(name) => GenericBinder::Type(SmolStr::new(name)),
                BuiltinBinderDefinition::Pack(name) => GenericBinder::Pack(SmolStr::new(name)),
            })
            .collect();
        store.type_scheme(body, binders)
    }
}

/// An owned builtin type tree generated before runtime type IDs exist.
#[derive(Debug)]
#[allow(dead_code)]
enum BuiltinType {
    /// One canonical primitive kind.
    Primitive(BuiltinPrimitive),
    /// A host-provided nominal type.
    Named(String),
    /// A generic placeholder covered by its generated scheme.
    Generic(String),
    /// An exact singleton literal.
    Literal(TypeLiteral),
    /// A structural table.
    Table {
        /// Named fields.
        fields: Vec<(String, BuiltinType)>,
        /// Optional key and value indexer.
        indexer: Option<(Box<BuiltinType>, Box<BuiltinType>)>,
    },
    /// A function signature.
    Function {
        /// Accepted argument pack.
        params: BuiltinPack,
        /// Produced return pack.
        returns: BuiltinPack,
    },
    /// A structural union.
    Union(Vec<BuiltinType>),
    /// An overloaded intersection.
    Intersection(Vec<BuiltinType>),
}

impl BuiltinType {
    /// Recursively interns this owned tree into the session's canonical store.
    fn intern(self, store: &mut TypeStore) -> TypeId {
        match self {
            Self::Primitive(primitive) => primitive.id(store),
            Self::Named(name) => store.named(name),
            Self::Generic(name) => store.generic(name),
            Self::Literal(literal) => store.literal(literal),
            Self::Table { fields, indexer } => {
                let fields = fields
                    .into_iter()
                    .map(|(name, ty)| (SmolStr::new(name), ty.intern(store)))
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
                let members = members
                    .into_iter()
                    .map(|ty| ty.intern(store))
                    .collect::<Vec<_>>();
                store.union_all(members)
            }
            Self::Intersection(members) => {
                let members = members
                    .into_iter()
                    .map(|ty| ty.intern(store))
                    .collect::<Vec<_>>();
                store.intersection_all(members)
            }
        }
    }
}

/// A primitive builtin kind mapped to the store's preallocated IDs.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
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

/// An owned fixed-prefix function type pack.
#[derive(Debug)]
struct BuiltinPack {
    /// Fixed positional elements.
    head: Vec<BuiltinType>,
    /// Optional open tail.
    tail: Option<BuiltinPackTail>,
}

impl BuiltinPack {
    /// Recursively interns this pack and all types it references.
    fn intern(self, store: &mut TypeStore) -> TypePackId {
        let head = self.head.into_iter().map(|ty| ty.intern(store)).collect();
        let tail = self.tail.map(|tail| tail.intern(store));
        store.pack(head, tail)
    }
}

/// The open tail of an owned builtin type pack.
#[derive(Debug)]
enum BuiltinPackTail {
    /// Repeats one type indefinitely.
    Homogeneous(Box<BuiltinType>),
    /// References one declared generic type pack.
    Generic(String),
}

impl BuiltinPackTail {
    /// Interns the type carried by this pack tail.
    fn intern(self, store: &mut TypeStore) -> TypePackTail {
        match self {
            Self::Homogeneous(ty) => TypePackTail::Homogeneous(ty.intern(store)),
            Self::Generic(name) => TypePackTail::Generic(SmolStr::new(name)),
        }
    }
}

include!(concat!(env!("OUT_DIR"), "/builtin_definitions.rs"));
