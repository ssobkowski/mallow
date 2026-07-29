use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt,
};

use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::hil::{
    lifted::LiftedFunction,
    ty2::{
        canonical::{
            GenericBinder, Type, TypeId, TypeLiteral, TypePackId, TypePackTail, TypeScheme,
        },
        store::TypeStore,
    },
};

/// Inferred types indexed by named locals from debug information.
pub struct TypesView {
    /// Canonical graph shared by inferred and test-constructed types.
    store: RefCell<TypeStore>,
    /// Named locals retained from Luau debug information.
    locals: Vec<LocalType>,
    /// Declaration indices grouped by exact source name.
    locals_by_name: HashMap<String, SmallVec<[usize; 2]>>,
}

/// One named source declaration and its inferred scheme.
struct LocalType {
    /// Source name from the bytecode debug record.
    name: String,
    /// Function proto that owns this declaration.
    proto: u16,
    /// First bytecode PC covered by this declaration.
    start_pc: u32,
    /// First bytecode PC after this declaration.
    end_pc: u32,
    /// Type produced solely by whole-program inference.
    scheme: Option<TypeScheme>,
}

impl TypesView {
    /// Builds a source-level view from functions after inference has completed.
    pub(crate) fn from_inferred(functions: &[LiftedFunction]) -> Self {
        let mut store = TypeStore::new();
        let mut locals = Vec::new();

        for function in functions {
            for local in &function.symbols.named_locals {
                let schemes: Vec<_> = local
                    .symbols
                    .iter()
                    .filter_map(|symbol| function.types.symbol_type_scheme(*symbol))
                    .map(|scheme| store.import_scheme(function.types.type_store(), scheme))
                    .collect();

                let scheme = merge_schemes(&mut store, schemes);
                locals.push(LocalType {
                    name: local.name.clone(),
                    proto: function.proto.0,
                    start_pc: local.start_pc,
                    end_pc: local.end_pc,
                    scheme,
                });
            }
        }

        let mut locals_by_name: HashMap<String, SmallVec<_>> = HashMap::new();
        for (index, local) in locals.iter().enumerate() {
            locals_by_name
                .entry(local.name.clone())
                .or_default()
                .push(index);
        }

        Self {
            store: RefCell::new(store),
            locals,
            locals_by_name,
        }
    }

    /// Returns the inferred type of the unique named local called `name`.
    ///
    /// # Panics
    ///
    /// Panics when the name is missing, ambiguous, or has no inferred type.
    #[track_caller]
    pub fn local(&self, name: &str) -> TypeView<'_> {
        let Some(matches) = self.locals_by_name.get(name) else {
            panic!("named local `{name}` does not exist in this type view");
        };
        let [index] = matches.as_slice() else {
            let locations = matches
                .iter()
                .map(|&index| {
                    let local = &self.locals[index];
                    format!(
                        "proto {} PCs {}..{}",
                        local.proto, local.start_pc, local.end_pc
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            panic!("named local `{name}` is ambiguous: {locations}");
        };
        let local = &self.locals[*index];
        let scheme = local.scheme.clone().unwrap_or_else(|| {
            panic!(
                "named local `{name}` at proto {} PCs {}..{} has no inferred type",
                local.proto, local.start_pc, local.end_pc,
            )
        });

        TypeView {
            owner: self,
            scheme,
        }
    }

    /// Returns a factory that creates expected types in this view's canonical graph.
    #[must_use]
    pub const fn types(&self) -> TypeFactory<'_> {
        TypeFactory { owner: self }
    }

    /// Wraps one monomorphic graph node as a type view.
    fn monomorphic(&self, body: TypeId) -> TypeView<'_> {
        let scheme = self.store.borrow().type_scheme(body, Vec::new());
        TypeView {
            owner: self,
            scheme,
        }
    }
}

/// Combines inferred SSA versions that belong to one source declaration.
fn merge_schemes(store: &mut TypeStore, schemes: Vec<TypeScheme>) -> Option<TypeScheme> {
    let distinct: HashSet<_> = schemes.into_iter().collect();

    if distinct.is_empty() {
        return None;
    }
    if distinct.len() == 1 {
        return distinct.into_iter().next();
    }
    if distinct.iter().any(|scheme| !scheme.binders().is_empty()) {
        return None;
    }

    let body = store.union_all(distinct.into_iter().map(|scheme| scheme.body()));
    Some(store.type_scheme(body, Vec::new()))
}

/// One canonical type scheme owned by a [`TypesView`].
#[derive(Clone)]
pub struct TypeView<'a> {
    /// View whose graph owns `scheme`.
    owner: &'a TypesView,
    /// Generic binders and canonical root node.
    scheme: TypeScheme,
}

impl PartialEq for TypeView<'_> {
    /// Compares canonical schemes from the same graph.
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.owner, other.owner) && self.scheme == other.scheme
    }
}

impl Eq for TypeView<'_> {}

impl fmt::Debug for TypeView<'_> {
    /// Formats the complete canonical type instead of its arena IDs.
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let store = self.owner.store.borrow();
        if !self.scheme.binders().is_empty() {
            formatter.write_str("<")?;
            for (index, binder) in self.scheme.binders().iter().enumerate() {
                if index != 0 {
                    formatter.write_str(", ")?;
                }
                match binder {
                    GenericBinder::Type(name) => write!(formatter, "{name}"),
                    GenericBinder::Pack(name) => write!(formatter, "{name}..."),
                }?;
            }
            formatter.write_str("> ")?;
        }

        TypeFormatter::new(&store).format(self.scheme.body(), formatter)
    }
}

/// One canonical type pack owned by a [`TypesView`].
#[derive(Clone, Copy)]
pub struct TypePackView<'a> {
    /// View whose graph owns `id`.
    owner: &'a TypesView,
    /// Canonical pack root.
    id: TypePackId,
}

/// Contextual constructors for expected canonical types.
#[derive(Clone, Copy)]
pub struct TypeFactory<'a> {
    /// View whose graph receives constructed nodes.
    owner: &'a TypesView,
}

impl<'a> TypeFactory<'a> {
    /// Returns the canonical `never` type.
    pub fn never(self) -> TypeView<'a> {
        let id = self.owner.store.borrow().primitives().never;
        self.owner.monomorphic(id)
    }

    /// Returns the canonical `unknown` type.
    pub fn unknown(self) -> TypeView<'a> {
        let id = self.owner.store.borrow().primitives().unknown;
        self.owner.monomorphic(id)
    }

    /// Returns the canonical `any` type.
    pub fn any(self) -> TypeView<'a> {
        let id = self.owner.store.borrow().primitives().any;
        self.owner.monomorphic(id)
    }

    /// Returns the canonical `nil` type.
    pub fn nil(self) -> TypeView<'a> {
        let id = self.owner.store.borrow().primitives().nil;
        self.owner.monomorphic(id)
    }

    /// Returns the canonical `string` type.
    pub fn string(self) -> TypeView<'a> {
        let id = self.owner.store.borrow().primitives().string;
        self.owner.monomorphic(id)
    }

    /// Returns the canonical `number` type.
    pub fn number(self) -> TypeView<'a> {
        let id = self.owner.store.borrow().primitives().number;
        self.owner.monomorphic(id)
    }

    /// Returns the canonical `integer` type.
    pub fn integer(self) -> TypeView<'a> {
        let id = self.owner.store.borrow().primitives().integer;
        self.owner.monomorphic(id)
    }

    /// Returns the canonical `boolean` type.
    pub fn boolean(self) -> TypeView<'a> {
        let id = self.owner.store.borrow().primitives().boolean;
        self.owner.monomorphic(id)
    }

    /// Returns one generic placeholder for a later [`Self::forall`] call.
    pub fn generic(self, name: impl Into<SmolStr>) -> TypeView<'a> {
        let id = self.owner.store.borrow_mut().generic(name);
        self.owner.monomorphic(id)
    }

    /// Returns a union containing every supplied type.
    pub fn union<const N: usize>(self, members: [TypeView<'a>; N]) -> TypeView<'a> {
        let ids: Vec<_> = members
            .into_iter()
            .map(|member| self.checked_body(member))
            .collect();
        let id = self.owner.store.borrow_mut().union_all(ids);
        self.owner.monomorphic(id)
    }

    /// Returns the union of `nil` and `ty`.
    pub fn optional(self, ty: TypeView<'a>) -> TypeView<'a> {
        self.union([self.nil(), ty])
    }

    /// Returns one fixed canonical type pack.
    pub fn pack<const N: usize>(self, values: [TypeView<'a>; N]) -> TypePackView<'a> {
        let values = values
            .into_iter()
            .map(|value| self.checked_body(value))
            .collect();
        let id = self.owner.store.borrow_mut().pack(values, None);
        TypePackView {
            owner: self.owner,
            id,
        }
    }

    /// Returns a type pack with a homogeneous variadic tail.
    pub fn variadic_pack<const N: usize>(
        self,
        head: [TypeView<'a>; N],
        tail: TypeView<'a>,
    ) -> TypePackView<'a> {
        let head = head
            .into_iter()
            .map(|value| self.checked_body(value))
            .collect();
        let tail = self.checked_body(tail);
        let id = self
            .owner
            .store
            .borrow_mut()
            .pack(head, Some(TypePackTail::Homogeneous(tail)));
        TypePackView {
            owner: self.owner,
            id,
        }
    }

    /// Returns a fixed-arity function signature.
    pub fn function<const P: usize, const R: usize>(
        self,
        params: [TypeView<'a>; P],
        returns: [TypeView<'a>; R],
    ) -> TypeView<'a> {
        let params = self.pack(params);
        let returns = self.pack(returns);
        self.function_packs(params, returns)
    }

    /// Returns a function signature from complete argument and return packs.
    pub fn function_packs(
        self,
        params: TypePackView<'a>,
        returns: TypePackView<'a>,
    ) -> TypeView<'a> {
        self.check_pack(params);
        self.check_pack(returns);
        let id = self
            .owner
            .store
            .borrow_mut()
            .function_signature(params.id, returns.id);
        self.owner.monomorphic(id)
    }

    /// Returns a structural table with the supplied named fields.
    pub fn table<const N: usize>(self, fields: [(&str, TypeView<'a>); N]) -> TypeView<'a> {
        let fields = fields
            .into_iter()
            .map(|(name, ty)| (SmolStr::new(name), self.checked_body(ty)))
            .collect();
        let id = self.owner.store.borrow_mut().table_shape(fields, None);
        self.owner.monomorphic(id)
    }

    /// Returns a homogeneous indexed table.
    pub fn indexed_table(self, key: TypeView<'a>, value: TypeView<'a>) -> TypeView<'a> {
        let key = self.checked_body(key);
        let value = self.checked_body(value);
        let id = self
            .owner
            .store
            .borrow_mut()
            .table_shape(Vec::new(), Some((key, value)));
        self.owner.monomorphic(id)
    }

    /// Quantifies generic placeholders contained in `body`.
    pub fn forall<const N: usize>(self, binders: [&str; N], body: TypeView<'a>) -> TypeView<'a> {
        let body = self.checked_body(body);
        let binders = binders
            .into_iter()
            .map(|name| GenericBinder::Type(SmolStr::new(name)))
            .collect();
        let scheme = self.owner.store.borrow().type_scheme(body, binders);
        TypeView {
            owner: self.owner,
            scheme,
        }
    }

    /// Checks that a type pack belongs to this factory.
    fn check_pack(self, pack: TypePackView<'a>) {
        assert!(
            std::ptr::eq(self.owner, pack.owner),
            "expected type pack belongs to another TypesView"
        );
    }

    /// Returns a body ID after checking that it belongs to this factory.
    fn checked_body(self, ty: TypeView<'a>) -> TypeId {
        assert!(
            std::ptr::eq(self.owner, ty.owner),
            "expected type belongs to another TypesView"
        );
        assert!(
            ty.scheme.binders().is_empty(),
            "a nested expected type cannot carry its own generic binders"
        );
        ty.scheme.body()
    }
}

/// Recursive formatter for canonical graph nodes.
struct TypeFormatter<'a> {
    /// Graph that owns all formatted IDs.
    store: &'a TypeStore,
    /// Nodes currently on the recursion stack.
    active: HashSet<TypeId>,
}

impl<'a> TypeFormatter<'a> {
    /// Creates a formatter for one canonical graph.
    fn new(store: &'a TypeStore) -> Self {
        Self {
            store,
            active: HashSet::new(),
        }
    }

    /// Formats one graph node and guards recursive edges.
    fn format(&mut self, id: TypeId, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.active.insert(id) {
            return formatter.write_str("<recursive>");
        }

        let result = match self.store.get(id) {
            Type::Never => formatter.write_str("never"),
            Type::Unknown => formatter.write_str("unknown"),
            Type::Any => formatter.write_str("any"),
            Type::Nil => formatter.write_str("nil"),
            Type::String => formatter.write_str("string"),
            Type::Number => formatter.write_str("number"),
            Type::Boolean => formatter.write_str("boolean"),
            Type::Thread => formatter.write_str("thread"),
            Type::Userdata => formatter.write_str("userdata"),
            Type::Vector => formatter.write_str("vector"),
            Type::Integer => formatter.write_str("integer"),
            Type::Buffer => formatter.write_str("buffer"),
            Type::Named(name) | Type::Generic(name) => write!(formatter, "{name}"),
            Type::Literal(TypeLiteral::String(value)) => write!(formatter, "{value:?}"),
            Type::Literal(TypeLiteral::Boolean(value)) => write!(formatter, "{value}"),
            Type::Table => formatter.write_str("table"),
            Type::TableShape { fields, indexer } => {
                formatter.write_str("{")?;
                let mut needs_separator = false;
                for (name, field) in fields {
                    if needs_separator {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{name}: ")?;
                    self.format(*field, formatter)?;
                    needs_separator = true;
                }
                if let Some((key, value)) = indexer {
                    if needs_separator {
                        formatter.write_str(", ")?;
                    }
                    formatter.write_str("[")?;
                    self.format(*key, formatter)?;
                    formatter.write_str("]: ")?;
                    self.format(*value, formatter)?;
                }
                formatter.write_str("}")
            }
            Type::Function => formatter.write_str("function"),
            Type::FunctionSignature { params, returns } => {
                self.format_pack(*params, formatter)?;
                formatter.write_str(" -> ")?;
                self.format_pack(*returns, formatter)
            }
            Type::Union(members) => self.format_joined(members, " | ", formatter),
            Type::Intersection(members) => self.format_joined(members, " & ", formatter),
            Type::WithMetatable { base, methods } => {
                self.format(*base, formatter)?;
                formatter.write_str(" with {")?;
                for (index, method) in methods.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{}: ", method.method.field())?;
                    self.format(method.ty, formatter)?;
                }
                formatter.write_str("}")
            }
        };

        self.active.remove(&id);
        result
    }

    /// Formats one canonical type pack.
    fn format_pack(&mut self, id: TypePackId, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pack = self.store.get_pack(id);
        formatter.write_str("(")?;
        for (index, ty) in pack.head.iter().enumerate() {
            if index != 0 {
                formatter.write_str(", ")?;
            }
            self.format(*ty, formatter)?;
        }
        if let Some(tail) = &pack.tail {
            if !pack.head.is_empty() {
                formatter.write_str(", ")?;
            }
            match tail {
                TypePackTail::Homogeneous(ty) => {
                    formatter.write_str("...")?;
                    self.format(*ty, formatter)?;
                }
                TypePackTail::Generic(name) => write!(formatter, "{name}...")?,
            }
        }
        formatter.write_str(")")
    }

    /// Formats graph nodes with one separator.
    fn format_joined(
        &mut self,
        ids: &[TypeId],
        separator: &str,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        for (index, id) in ids.iter().enumerate() {
            if index != 0 {
                formatter.write_str(separator)?;
            }
            self.format(*id, formatter)?;
        }
        Ok(())
    }
}
