//! Generates owned builtin type definitions from Luau's JSON AST.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::{env, fs};

use mallow_luau_toolchain::{BytecodeVersion, Manager};
use serde::Deserialize;

/// The Luau declarations used to generate mallow-core's builtin definitions.
const BUILTIN_SOURCES: &[&str] = &[
    "builtin-definitions/base.luau",
    "builtin-definitions/extra.luau",
];

/// The Rust module committed for hermetic mallow-core builds.
const GENERATED_FILE: &str = "../crates/mallow-core/src/ty/builtin_definitions.rs";

/// Parses the checked-in declarations and updates their owned Rust representation.
fn main() {
    generate_builtin_definitions().expect("failed to generate builtin definitions");
}

/// Runs the managed V9 `luau-ast`, lowers its AST, and writes the generated module.
fn generate_builtin_definitions() -> Result<(), String> {
    let manifest_dir = PathBuf::from(
        env::var_os("CARGO_MANIFEST_DIR")
            .ok_or_else(|| "Cargo did not provide CARGO_MANIFEST_DIR".to_owned())?,
    );
    let manager =
        Manager::new().map_err(|error| format!("could not create Luau manager: {error}"))?;

    let mut statements = Vec::new();
    for source in BUILTIN_SOURCES {
        let source_path = manifest_dir.join(source);
        statements.extend(parse_luau_ast(&manager, &source_path)?.root.body);
    }
    let document = AstDocument {
        root: AstBlock { body: statements },
    };

    let definitions = BuiltinLowerer::new(&document)?.lower_document(&document)?;
    let generated = render_definitions(&definitions);
    let output_path = manifest_dir.join(GENERATED_FILE);

    fs::write(&output_path, generated)
        .map_err(|error| format!("could not write {}: {error}", output_path.display()))?;

    Ok(())
}

/// Invokes the managed official parser and deserializes its JSON AST.
fn parse_luau_ast(manager: &Manager, source_path: &Path) -> Result<AstDocument, String> {
    let output = manager
        .ast(BytecodeVersion::V9)
        .map_err(|error| format!("could not obtain luau-ast: {error}"))?
        .arg(source_path)
        .output()
        .map_err(|error| format!("could not run managed luau-ast: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "luau-ast rejected {}:\n{}",
            source_path.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    // AstStatDeclareGlobal contains both a discriminator and its annotation under
    // the key `type`. Normalizing through Value gives the annotation its intended
    // last-key-wins meaning before the derived statement model is applied.
    let value: serde_json::Value = serde_json::from_slice(&output.stdout)
        .map_err(|error| format!("luau-ast produced invalid JSON: {error}"))?;
    serde_json::from_value(value)
        .map_err(|error| format!("luau-ast produced an unsupported AST shape: {error}"))
}

/// The top-level JSON document produced by `luau-ast`.
#[derive(Debug, Clone, Deserialize)]
struct AstDocument {
    /// The parsed source block.
    root: AstBlock,
}

/// A source block containing the builtin declarations.
#[derive(Debug, Clone, Deserialize)]
struct AstBlock {
    /// Statements in source order.
    body: Vec<AstStatement>,
}

/// A statement shape accepted from builtin definition files.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
enum AstStatement {
    /// A declared global function.
    DeclareFunction(AstDeclareFunction),
    /// A local type alias used by later declarations.
    TypeAlias(AstTypeAlias),
    /// An externally supplied nominal type.
    DeclareExtern(AstDeclareExtern),
    /// A declared global value.
    DeclareGlobal(AstDeclareGlobal),
}

/// A declared global function and its complete type-pack signature.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AstDeclareFunction {
    /// The global function name.
    name: String,
    /// Fixed parameters and an optional open tail.
    params: AstTypeList,
    /// Return pack.
    ret_types: AstType,
    /// Explicit type binders.
    #[serde(default)]
    generics: Vec<AstGeneric>,
    /// Explicit type-pack binders.
    #[serde(default)]
    generic_packs: Vec<AstGeneric>,
}

/// A declared global value with its Luau type annotation.
#[derive(Debug, Clone, Deserialize)]
struct AstDeclareGlobal {
    /// The global value name.
    name: String,
    /// The global's type annotation, stored under Luau's duplicate `type` key.
    #[serde(rename = "type")]
    luau_type: AstType,
}

/// A source-level type alias used by builtin declarations.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AstTypeAlias {
    /// The alias name.
    name: String,
    /// Explicit type parameters, unsupported by the current builtin graph.
    #[serde(default)]
    generics: Vec<AstGeneric>,
    /// Explicit pack parameters, unsupported by the current builtin graph.
    #[serde(default)]
    generic_packs: Vec<AstGeneric>,
    /// The aliased type.
    value: AstType,
}

/// An extern type declaration supplied by the Luau host.
#[derive(Debug, Clone, Deserialize)]
struct AstDeclareExtern {
    /// The nominal type name.
    name: String,
    /// Properties prove this is an extern declaration in the untagged statement model.
    props: Vec<AstExternProperty>,
}

/// One property carried by an extern type declaration.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AstExternProperty {
    /// The property name.
    name: String,
    /// The property's Luau type.
    luau_type: AstType,
}

/// One explicit generic type or pack binder.
#[derive(Debug, Clone, Deserialize)]
struct AstGeneric {
    /// Binder name without pack punctuation.
    name: String,
}

/// A fixed type-list prefix and optional pack tail.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AstTypeList {
    /// Fixed positional types.
    types: Vec<AstType>,
    /// Optional variadic or generic pack tail.
    tail_type: Option<Box<AstType>>,
}

/// A named property in a structural table type.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AstTableProperty {
    /// Property name.
    name: String,
    /// Property value type.
    prop_type: AstType,
}

/// The key and value annotations of a table indexer.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AstTableIndexer {
    /// Accepted key type.
    index_type: AstType,
    /// Produced value type.
    result_type: AstType,
}

/// A Luau type or type-pack node used by the builtin sources.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "type")]
enum AstType {
    /// A primitive, generic, alias, or extern type reference.
    #[serde(rename = "AstTypeReference")]
    Reference {
        /// Referenced name.
        name: String,
        /// Type arguments, currently unused by the selected builtin sources.
        #[serde(default)]
        parameters: Vec<AstType>,
    },
    /// A structural table with named properties and an optional indexer.
    #[serde(rename = "AstTypeTable")]
    Table {
        /// Named table properties.
        props: Vec<AstTableProperty>,
        /// Homogeneous table indexer.
        indexer: Option<Box<AstTableIndexer>>,
    },
    /// A function with fixed and open argument and result packs.
    #[serde(rename = "AstTypeFunction", rename_all = "camelCase")]
    Function {
        /// Explicit type binders scoped to the function.
        #[serde(default)]
        generics: Vec<AstGeneric>,
        /// Explicit type-pack binders scoped to the function.
        #[serde(default)]
        generic_packs: Vec<AstGeneric>,
        /// Argument pack.
        arg_types: AstTypeList,
        /// Return pack.
        return_types: Box<AstType>,
    },
    /// A union whose optional sentinel lowers to nil.
    #[serde(rename = "AstTypeUnion")]
    Union {
        /// Union members.
        types: Vec<AstType>,
    },
    /// An intersection, used for overloaded functions.
    #[serde(rename = "AstTypeIntersection")]
    Intersection {
        /// Intersection members.
        types: Vec<AstType>,
    },
    /// A transparent parenthesized type.
    #[serde(rename = "AstTypeGroup")]
    Group {
        /// Parenthesized type.
        inner: Box<AstType>,
    },
    /// An exact string singleton.
    #[serde(rename = "AstTypeSingletonString")]
    SingletonString {
        /// Singleton value.
        value: String,
    },
    /// An exact boolean singleton.
    #[serde(rename = "AstTypeSingletonBool")]
    SingletonBool {
        /// Singleton value.
        value: bool,
    },
    /// The nil member emitted inside the union representation of `T?`.
    #[serde(rename = "AstTypeOptional")]
    Optional,
    /// An explicit fixed-prefix type pack.
    #[serde(rename = "AstTypePackExplicit", rename_all = "camelCase")]
    PackExplicit {
        /// Fixed types and optional tail.
        type_list: AstTypeList,
    },
    /// A homogeneous variadic type pack.
    #[serde(rename = "AstTypePackVariadic", rename_all = "camelCase")]
    PackVariadic {
        /// Repeated element type.
        variadic_type: Box<AstType>,
    },
    /// A generic type pack.
    #[serde(rename = "AstTypePackGeneric", rename_all = "camelCase")]
    PackGeneric {
        /// Pack binder name.
        generic_name: String,
    },
}

/// A generated builtin global.
#[derive(Debug)]
struct GeneratedBuiltin {
    /// Global name.
    name: String,
    /// Global type scheme.
    scheme: GeneratedScheme,
}

/// A generated type body with its precomputed binders.
#[derive(Debug)]
struct GeneratedScheme {
    /// Type and pack binders in declaration order.
    binders: Vec<GeneratedBinder>,
    /// Owned structural body.
    body: GeneratedType,
}

/// The kind and name of one generated generic binder.
#[derive(Debug, Clone, PartialEq, Eq)]
enum GeneratedBinder {
    /// A binder substituted by one type.
    Type(String),
    /// A binder substituted by one type pack.
    Pack(String),
}

impl GeneratedBinder {
    /// Returns the source-level binder name.
    fn name(&self) -> &str {
        match self {
            Self::Type(name) | Self::Pack(name) => name,
        }
    }
}

/// An owned type tree independent of any runtime [`TypeStore`].
#[derive(Debug)]
enum GeneratedType {
    /// One canonical primitive kind.
    Primitive(GeneratedPrimitive),
    /// A host-provided nominal type.
    Named(String),
    /// A generic placeholder.
    Generic(String),
    /// An exact singleton value.
    Literal(GeneratedLiteral),
    /// A structural table.
    Table {
        /// Named fields in source order.
        fields: Vec<(String, GeneratedType)>,
        /// Optional key and value indexer.
        indexer: Option<(Box<GeneratedType>, Box<GeneratedType>)>,
    },
    /// A function signature.
    Function {
        /// Accepted arguments.
        params: GeneratedPack,
        /// Produced results.
        returns: GeneratedPack,
    },
    /// A structural union.
    Union(Vec<GeneratedType>),
    /// An overloaded intersection.
    Intersection(Vec<GeneratedType>),
}

/// A primitive type understood directly by `TypeStore`.
#[derive(Debug, Clone, Copy)]
enum GeneratedPrimitive {
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

/// An owned singleton literal.
#[derive(Debug)]
enum GeneratedLiteral {
    /// Exact string.
    String(String),
    /// Exact boolean.
    Boolean(bool),
}

/// An owned fixed-prefix type pack.
#[derive(Debug)]
struct GeneratedPack {
    /// Fixed positional elements.
    head: Vec<GeneratedType>,
    /// Optional open tail.
    tail: Option<GeneratedPackTail>,
}

/// The open tail of an owned type pack.
#[derive(Debug)]
enum GeneratedPackTail {
    /// Repeats one type indefinitely.
    Homogeneous(Box<GeneratedType>),
    /// References one declared generic pack.
    Generic(String),
}

/// A lexical generic scope active while lowering one scheme.
#[derive(Debug, Default)]
struct GenericScope {
    /// Type binders declared at this level.
    types: HashSet<String>,
    /// Type-pack binders declared at this level.
    packs: HashSet<String>,
}

/// Per-scheme lowering state, including precomputed flattened binders.
#[derive(Debug, Default)]
struct SchemeContext {
    /// Active lexical scopes, from outermost to innermost.
    scopes: Vec<GenericScope>,
    /// Unique binders retained by the rank-one canonical scheme.
    binders: Vec<GeneratedBinder>,
}

impl SchemeContext {
    /// Pushes one function's generic declarations and records their scheme binders.
    fn push(&mut self, types: &[AstGeneric], packs: &[AstGeneric]) -> Result<(), String> {
        let mut scope = GenericScope::default();
        for generic in types {
            if self.contains_type(&generic.name) || self.contains_pack(&generic.name) {
                return Err(format!(
                    "nested generic binder {} shadows an outer binder",
                    generic.name
                ));
            }
            if !scope.types.insert(generic.name.clone()) {
                return Err(format!("duplicate generic type binder {}", generic.name));
            }
            self.record_binder(GeneratedBinder::Type(generic.name.clone()))?;
        }
        for generic in packs {
            if self.contains_type(&generic.name) || self.contains_pack(&generic.name) {
                return Err(format!(
                    "nested generic binder {} shadows an outer binder",
                    generic.name
                ));
            }
            if !scope.packs.insert(generic.name.clone()) {
                return Err(format!("duplicate generic pack binder {}", generic.name));
            }
            self.record_binder(GeneratedBinder::Pack(generic.name.clone()))?;
        }
        self.scopes.push(scope);
        Ok(())
    }

    /// Pops the innermost lexical generic scope.
    fn pop(&mut self) {
        self.scopes
            .pop()
            .expect("generic scope must be balanced during lowering");
    }

    /// Returns whether `name` resolves to an active type binder.
    fn contains_type(&self, name: &str) -> bool {
        self.scopes
            .iter()
            .rev()
            .any(|scope| scope.types.contains(name))
    }

    /// Returns whether `name` resolves to an active type-pack binder.
    fn contains_pack(&self, name: &str) -> bool {
        self.scopes
            .iter()
            .rev()
            .any(|scope| scope.packs.contains(name))
    }

    /// Records a binder once because canonical schemes are rank one.
    fn record_binder(&mut self, binder: GeneratedBinder) -> Result<(), String> {
        if let Some(existing) = self
            .binders
            .iter()
            .find(|existing| existing.name() == binder.name())
        {
            if existing != &binder {
                return Err(format!(
                    "generic binder {} is declared as both a type and a pack",
                    binder.name()
                ));
            }
            return Ok(());
        }
        self.binders.push(binder);
        Ok(())
    }
}

/// Resolves aliases and lowers Luau AST nodes into owned generated definitions.
#[derive(Debug)]
struct BuiltinLowerer {
    /// Non-generic source aliases available to global definitions.
    aliases: HashMap<String, AstType>,
    /// Nominal types declared by the host.
    extern_types: HashSet<String>,
}

impl BuiltinLowerer {
    /// Indexes aliases and extern types before any global is lowered.
    fn new(document: &AstDocument) -> Result<Self, String> {
        let mut aliases = HashMap::new();
        let mut extern_types = HashSet::new();
        for statement in &document.root.body {
            match statement {
                AstStatement::TypeAlias(alias) => {
                    if !alias.generics.is_empty() || !alias.generic_packs.is_empty() {
                        return Err(format!(
                            "generic builtin alias {} is not supported",
                            alias.name
                        ));
                    }
                    if aliases
                        .insert(alias.name.clone(), alias.value.clone())
                        .is_some()
                    {
                        return Err(format!("duplicate builtin alias {}", alias.name));
                    }
                }
                AstStatement::DeclareExtern(extern_type) => {
                    if !extern_types.insert(extern_type.name.clone()) {
                        return Err(format!("duplicate extern type {}", extern_type.name));
                    }
                    // Validate that the derived extern-property model remains aligned
                    // with luau-ast even though canonical primitives own these fields.
                    for property in &extern_type.props {
                        let _ = (&property.name, &property.luau_type);
                    }
                }
                AstStatement::DeclareFunction(_) | AstStatement::DeclareGlobal(_) => {}
            }
        }
        Ok(Self {
            aliases,
            extern_types,
        })
    }

    /// Lowers every declared global while retaining source order.
    fn lower_document(&self, document: &AstDocument) -> Result<Vec<GeneratedBuiltin>, String> {
        let mut definitions = Vec::new();
        let mut names = HashSet::new();
        for statement in &document.root.body {
            let definition = match statement {
                AstStatement::DeclareFunction(function) => {
                    Some(self.lower_function_declaration(function)?)
                }
                AstStatement::DeclareGlobal(global) => Some(self.lower_global_declaration(global)?),
                AstStatement::TypeAlias(_) | AstStatement::DeclareExtern(_) => None,
            };
            if let Some(definition) = definition {
                if !names.insert(definition.name.clone()) {
                    return Err(format!("duplicate builtin global {}", definition.name));
                }
                definitions.push(definition);
            }
        }
        Ok(definitions)
    }

    /// Lowers a declared function into a global function scheme.
    fn lower_function_declaration(
        &self,
        function: &AstDeclareFunction,
    ) -> Result<GeneratedBuiltin, String> {
        let function_type = AstType::Function {
            generics: function.generics.clone(),
            generic_packs: function.generic_packs.clone(),
            arg_types: function.params.clone(),
            return_types: Box::new(function.ret_types.clone()),
        };
        Ok(GeneratedBuiltin {
            name: function.name.clone(),
            scheme: self.lower_scheme(&function_type)?,
        })
    }

    /// Lowers a global annotation into one complete type scheme.
    fn lower_global_declaration(
        &self,
        global: &AstDeclareGlobal,
    ) -> Result<GeneratedBuiltin, String> {
        Ok(GeneratedBuiltin {
            name: global.name.clone(),
            scheme: self.lower_scheme(&global.luau_type)?,
        })
    }

    /// Lowers one independently instantiable scheme and returns its declared binders.
    fn lower_scheme(&self, ty: &AstType) -> Result<GeneratedScheme, String> {
        let mut context = SchemeContext::default();
        let mut alias_stack = Vec::new();
        let body = self.lower_type(ty, &mut context, &mut alias_stack)?;
        Ok(GeneratedScheme {
            binders: context.binders,
            body,
        })
    }

    /// Recursively lowers one AST type using the active lexical generic scopes.
    fn lower_type(
        &self,
        ty: &AstType,
        context: &mut SchemeContext,
        alias_stack: &mut Vec<String>,
    ) -> Result<GeneratedType, String> {
        match ty {
            AstType::Reference { name, parameters } => {
                self.lower_reference(name, parameters, context, alias_stack)
            }
            AstType::Table { props, indexer } => {
                let fields = props
                    .iter()
                    .map(|property| {
                        Ok((
                            property.name.clone(),
                            self.lower_type(&property.prop_type, context, alias_stack)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                let indexer = indexer
                    .as_ref()
                    .map(|indexer| -> Result<_, String> {
                        Ok((
                            Box::new(self.lower_type(&indexer.index_type, context, alias_stack)?),
                            Box::new(self.lower_type(
                                &indexer.result_type,
                                context,
                                alias_stack,
                            )?),
                        ))
                    })
                    .transpose()?;
                Ok(GeneratedType::Table { fields, indexer })
            }
            AstType::Function {
                generics,
                generic_packs,
                arg_types,
                return_types,
            } => {
                context.push(generics, generic_packs)?;
                let params = self.lower_type_list(arg_types, context, alias_stack);
                let returns = params.and_then(|params| {
                    self.lower_pack(return_types, context, alias_stack)
                        .map(|returns| (params, returns))
                });
                context.pop();
                let (params, returns) = returns?;
                Ok(GeneratedType::Function { params, returns })
            }
            AstType::Union { types } => Ok(GeneratedType::Union(
                types
                    .iter()
                    .map(|member| self.lower_type(member, context, alias_stack))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            AstType::Intersection { types } => Ok(GeneratedType::Intersection(
                types
                    .iter()
                    .map(|member| self.lower_type(member, context, alias_stack))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            AstType::Group { inner } => self.lower_type(inner, context, alias_stack),
            AstType::SingletonString { value } => Ok(GeneratedType::Literal(
                GeneratedLiteral::String(value.clone()),
            )),
            AstType::SingletonBool { value } => {
                Ok(GeneratedType::Literal(GeneratedLiteral::Boolean(*value)))
            }
            AstType::Optional => Ok(GeneratedType::Primitive(GeneratedPrimitive::Nil)),
            AstType::PackExplicit { .. }
            | AstType::PackVariadic { .. }
            | AstType::PackGeneric { .. } => {
                Err("type-pack node appeared where a type was required".to_owned())
            }
        }
    }

    /// Resolves one reference as a primitive, generic, alias, or extern type.
    fn lower_reference(
        &self,
        name: &str,
        parameters: &[AstType],
        context: &mut SchemeContext,
        alias_stack: &mut Vec<String>,
    ) -> Result<GeneratedType, String> {
        if !parameters.is_empty() {
            return Err(format!(
                "parameterized builtin type reference {name} is not supported"
            ));
        }
        if let Some(primitive) = GeneratedPrimitive::from_name(name) {
            return Ok(GeneratedType::Primitive(primitive));
        }
        if context.contains_type(name) {
            return Ok(GeneratedType::Generic(name.to_owned()));
        }
        if let Some(alias) = self.aliases.get(name) {
            if alias_stack.iter().any(|active| active == name) {
                let mut cycle = alias_stack.join(" -> ");
                if !cycle.is_empty() {
                    cycle.push_str(" -> ");
                }
                cycle.push_str(name);
                return Err(format!("recursive builtin type alias: {cycle}"));
            }
            alias_stack.push(name.to_owned());
            let result = self.lower_type(alias, context, alias_stack);
            alias_stack.pop();
            return result;
        }
        if self.extern_types.contains(name) || name == "class" {
            return Ok(GeneratedType::Named(name.to_owned()));
        }
        Err(format!("unresolved builtin type reference {name}"))
    }

    /// Lowers a fixed-prefix AST type list into an owned type pack.
    fn lower_type_list(
        &self,
        list: &AstTypeList,
        context: &mut SchemeContext,
        alias_stack: &mut Vec<String>,
    ) -> Result<GeneratedPack, String> {
        let head: Vec<_> = list
            .types
            .iter()
            .map(|ty| self.lower_type(ty, context, alias_stack))
            .collect::<Result<_, _>>()?;
        let tail = list
            .tail_type
            .as_deref()
            .map(|tail| self.lower_pack_tail(tail, context, alias_stack))
            .transpose()?;
        Ok(GeneratedPack { head, tail })
    }

    /// Lowers a standalone explicit, variadic, or generic pack node.
    fn lower_pack(
        &self,
        pack: &AstType,
        context: &mut SchemeContext,
        alias_stack: &mut Vec<String>,
    ) -> Result<GeneratedPack, String> {
        match pack {
            AstType::PackExplicit { type_list } => {
                self.lower_type_list(type_list, context, alias_stack)
            }
            tail @ (AstType::PackVariadic { .. } | AstType::PackGeneric { .. }) => {
                Ok(GeneratedPack {
                    head: Vec::new(),
                    tail: Some(self.lower_pack_tail(tail, context, alias_stack)?),
                })
            }
            _ => Err("function return annotation was not a type pack".to_owned()),
        }
    }

    /// Lowers one open pack tail and validates generic pack scope.
    fn lower_pack_tail(
        &self,
        tail: &AstType,
        context: &mut SchemeContext,
        alias_stack: &mut Vec<String>,
    ) -> Result<GeneratedPackTail, String> {
        match tail {
            AstType::PackVariadic { variadic_type } => Ok(GeneratedPackTail::Homogeneous(
                Box::new(self.lower_type(variadic_type, context, alias_stack)?),
            )),
            AstType::PackGeneric { generic_name } if context.contains_pack(generic_name) => {
                Ok(GeneratedPackTail::Generic(generic_name.clone()))
            }
            AstType::PackGeneric { generic_name } => {
                Err(format!("unbound generic type pack {generic_name}"))
            }
            _ => Err("type-list tail was not variadic or generic".to_owned()),
        }
    }
}

impl GeneratedPrimitive {
    /// Recognizes a canonical primitive by its Luau spelling.
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "never" => Some(Self::Never),
            "unknown" => Some(Self::Unknown),
            "any" => Some(Self::Any),
            "nil" => Some(Self::Nil),
            "string" => Some(Self::String),
            "number" => Some(Self::Number),
            "integer" => Some(Self::Integer),
            "boolean" => Some(Self::Boolean),
            "thread" => Some(Self::Thread),
            "vector" => Some(Self::Vector),
            "buffer" => Some(Self::Buffer),
            _ => None,
        }
    }

    /// Returns the runtime enum variant emitted for this primitive.
    fn variant_name(self) -> &'static str {
        match self {
            Self::Never => "Never",
            Self::Unknown => "Unknown",
            Self::Any => "Any",
            Self::Nil => "Nil",
            Self::String => "String",
            Self::Number => "Number",
            Self::Integer => "Integer",
            Self::Boolean => "Boolean",
            Self::Thread => "Thread",
            Self::Vector => "Vector",
            Self::Buffer => "Buffer",
        }
    }
}

/// Renders all lowered definitions as one static included Rust slice.
fn render_definitions(definitions: &[GeneratedBuiltin]) -> String {
    let mut output = String::from(
        "// @generated by `cargo run -p xtask` - do not edit by hand.\n\
         // Edit the Luau sources in xtask/builtin-definitions and rerun the command instead.\n\n\
         fn generated_builtin_definitions() -> &'static [BuiltinDefinition] {\n    &[\n",
    );
    for definition in definitions {
        output.push_str("        BuiltinDefinition { name: ");
        output.push_str(&rust_string(&definition.name));
        output.push_str(", scheme: ");
        output.push_str(&render_scheme(&definition.scheme));
        output.push_str(" },\n");
    }
    output.push_str("    ]\n}\n");
    output
}

/// Renders one pre-bound static type scheme.
fn render_scheme(scheme: &GeneratedScheme) -> String {
    let binders = scheme
        .binders
        .iter()
        .map(|binder| match binder {
            GeneratedBinder::Type(name) => {
                format!("BuiltinBinderDefinition::Type({})", rust_string(name))
            }
            GeneratedBinder::Pack(name) => {
                format!("BuiltinBinderDefinition::Pack({})", rust_string(name))
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "BuiltinSchemeDefinition {{ binders: &[{binders}], body: {} }}",
        render_type(&scheme.body)
    )
}

/// Renders one recursive static type expression.
fn render_type(ty: &GeneratedType) -> String {
    match ty {
        GeneratedType::Primitive(primitive) => format!(
            "BuiltinType::Primitive(BuiltinPrimitive::{})",
            primitive.variant_name()
        ),
        GeneratedType::Named(name) => format!("BuiltinType::Named({})", rust_string(name)),
        GeneratedType::Generic(name) => format!("BuiltinType::Generic({})", rust_string(name)),
        GeneratedType::Literal(GeneratedLiteral::String(value)) => format!(
            "BuiltinType::Literal(BuiltinLiteral::String({}))",
            rust_string(value)
        ),
        GeneratedType::Literal(GeneratedLiteral::Boolean(value)) => {
            format!("BuiltinType::Literal(BuiltinLiteral::Boolean({value}))")
        }
        GeneratedType::Table { fields, indexer } => {
            let fields = fields
                .iter()
                .map(|(name, ty)| format!("({}, {})", rust_string(name), render_type(ty)))
                .collect::<Vec<_>>()
                .join(", ");
            let indexer = match indexer {
                Some((key, value)) => {
                    format!("Some((&{}, &{}))", render_type(key), render_type(value))
                }
                None => "None".to_owned(),
            };
            format!("BuiltinType::Table {{ fields: &[{fields}], indexer: {indexer} }}")
        }
        GeneratedType::Function { params, returns } => format!(
            "BuiltinType::Function {{ params: {}, returns: {} }}",
            render_pack(params),
            render_pack(returns)
        ),
        GeneratedType::Union(types) => format!(
            "BuiltinType::Union(&[{}])",
            types.iter().map(render_type).collect::<Vec<_>>().join(", ")
        ),
        GeneratedType::Intersection(types) => format!(
            "BuiltinType::Intersection(&[{}])",
            types.iter().map(render_type).collect::<Vec<_>>().join(", ")
        ),
    }
}

/// Renders one fixed-prefix static type pack.
fn render_pack(pack: &GeneratedPack) -> String {
    let head = pack
        .head
        .iter()
        .map(render_type)
        .collect::<Vec<_>>()
        .join(", ");
    let tail = match &pack.tail {
        Some(GeneratedPackTail::Homogeneous(ty)) => {
            format!("Some(BuiltinPackTail::Homogeneous(&{}))", render_type(ty))
        }
        Some(GeneratedPackTail::Generic(name)) => {
            format!("Some(BuiltinPackTail::Generic({}))", rust_string(name))
        }
        None => "None".to_owned(),
    };
    format!("BuiltinPack {{ head: &[{head}], tail: {tail} }}")
}

/// Quotes one generated string using Rust-compatible JSON escaping.
fn rust_string(value: &str) -> String {
    serde_json::to_string(value).expect("serializing a Rust string cannot fail")
}
