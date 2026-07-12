use std::collections::HashMap;

use smol_str::SmolStr;

use crate::hil::{
    ir::HilExpr,
    ty::{FunctionTypeParam, FunctionTypeReturn, Type, TypeLiteral},
};

/// Immutable builtin type schemes allocated once for an inference session.
#[derive(Debug)]
pub struct BuiltinEnvironment {
    /// Global names mapped to their polymorphic surface type schemes.
    globals: HashMap<SmolStr, Type>,
}

/// Stable symbolic reference into a [`BuiltinEnvironment`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    /// Returns the heap effect for this builtin and fixed call arity.
    pub(super) fn call_effect(&self, argument_count: usize) -> Option<BuiltinCallEffect> {
        match (self, argument_count) {
            (Self::Global(name), 2..) if name == "setmetatable" => {
                Some(BuiltinCallEffect::SetMetatable {
                    table_argument: 0,
                    metatable_argument: 1,
                })
            }
            (Self::Global(name), 3..) if name == "rawset" => Some(BuiltinCallEffect::SetIndex {
                table_argument: 0,
                index: BuiltinIndex::Argument(1),
                value_argument: 2,
            }),
            (Self::NamespaceField { namespace, field }, 2)
                if namespace == "table" && field == "insert" =>
            {
                Some(BuiltinCallEffect::SetIndex {
                    table_argument: 0,
                    index: BuiltinIndex::Number,
                    value_argument: 1,
                })
            }
            (Self::NamespaceField { namespace, field }, 3)
                if namespace == "table" && field == "insert" =>
            {
                Some(BuiltinCallEffect::SetIndex {
                    table_argument: 0,
                    index: BuiltinIndex::Argument(1),
                    value_argument: 2,
                })
            }
            _ => None,
        }
    }
}

impl BuiltinPath {
    /// Recognizes a syntactic builtin path without allocating its type.
    #[must_use]
    pub fn from_expr(expr: &HilExpr) -> Option<Self> {
        match expr {
            HilExpr::Global(name) => Some(Self::Global(name.clone())),
            HilExpr::GetField { obj, field } => {
                let HilExpr::Global(namespace) = obj.as_ref() else {
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

impl Default for BuiltinEnvironment {
    /// Builds the standard Luau builtin environment.
    fn default() -> Self {
        Self::new()
    }
}

impl BuiltinEnvironment {
    /// Builds every builtin type scheme exactly once.
    #[must_use]
    pub fn new() -> Self {
        let globals = GLOBAL_NAMES
            .iter()
            .map(|name| {
                let name = SmolStr::new_static(name);
                let ty = global_type(&name)
                    .unwrap_or_else(|| panic!("builtin environment is missing global {name}"));
                (name, ty)
            })
            .collect();
        Self { globals }
    }

    /// Returns the type scheme at a previously recognized builtin path.
    #[must_use]
    pub fn get_path(&self, path: &BuiltinPath) -> Option<&Type> {
        match path {
            BuiltinPath::Global(name) => self.globals.get(name),
            BuiltinPath::NamespaceField { namespace, field } => {
                let Type::Table { fields, .. } = self.globals.get(namespace)? else {
                    return None;
                };
                fields.get(field)
            }
        }
    }
}

macro_rules! generic_name {
    ($g:ident) => {
        SmolStr::new_static(&stringify!($g))
    };
}

macro_rules! ty {
    // Core Primitives
    (nil) => { Type::Nil };
    (string) => { Type::String };
    (number) => { Type::Number };
    (boolean) => { Type::Boolean };
    (any) => { Type::Any };
    (never) => { Type::Never };
    (thread) => { Type::Thread };
    (unit) => { Type::Unit };
    (integer) => { Type::Integer };
    (buffer) => { Type::Buffer };
    (vector) => { Type::Vector };
    (unknown) => { Type::Unknown };

    // Generics
    ($g:ident) => {
        Type::Generic(generic_name!($g))
    };

    // Named types exported by builtin libraries.
    (named $name:literal) => {
        Type::Named(SmolStr::new_static($name))
    };

    // String singleton types.
    ($s:literal) => {
        Type::Literal(TypeLiteral::String($s.to_owned()))
    };

    // Unified Tables: { key => value, field: type, field2: type }
    ({ $k:tt => $v:tt, $($field:ident : $t:tt),+ $(,)? }) => {
        Type::Table {
            fields: HashMap::<SmolStr, Type>::from([
                $( (SmolStr::new_static(stringify!($field)), ty!($t)) ),+
            ]),
            array: Some(Box::new((ty!($k), ty!($v)))),
        }
    };

    // Array Tables: { key => value }
    ({ $k:tt => $v:tt }) => {
        Type::Table {
            fields: HashMap::new(),
            array: Some(Box::new((ty!($k), ty!($v)))),
        }
    };

    // Field Tables / Namespaces: { field: type, field2: type }
    ({ $($field:ident : $t:tt),* $(,)? }) => {
        Type::Table {
            fields: HashMap::<SmolStr, Type>::from([
                $( (SmolStr::new_static(stringify!($field)), ty!($t)) ),*
            ]),
            array: None,
        }
    };

    // Functions with Generics: fn<'A, 'B>(params) -> returns
    (fn <$($gen:ident),*> ( $($p:tt)* ) -> $($r:tt)* ) => {
        Type::Function {
            generics: vec![ $( generic_name!($gen) ),* ],
            params: parse_params!( $($p)* ),
            return_type: parse_returns!( $($r)* ),
        }
    };

    // Functions without Generics: fn(params) -> returns
    (fn ( $($p:tt)* ) -> $($r:tt)* ) => {
        Type::Function {
            generics: Vec::new(),
            params: parse_params!( $($p)* ),
            return_type: parse_returns!( $($r)* ),
        }
    };

    // Unwrapping explicit parenthesis groupings (e.g. for complex unions),
    // e.g. `(fn(number) -> string) | nil`. Tried before the union/optional
    // fallback below so a parenthesized group is treated as a single atom
    // rather than being re-fed into it.
    (( $($inner:tt)* )) => {
        ty!($($inner)*)
    };

    // Fallback: a `|`-separated union of atoms, where each atom may carry a
    // trailing `?` sugar for "atom | nil" (e.g. `number? | nil`, `'T?`).
    // Every other arm above matches the *entire* remaining input verbatim
    // (a bare keyword, a lifetime, a `{ .. }` group, or a `fn` signature that
    // greedily consumes everything up to the end as its return type), so by
    // the time we get here we know the input isn't one of those and must be
    // split on `|`. A multi-token atom that isn't already handled above
    // (such as a bare, unparenthesized `fn(...) -> T`) must be wrapped in
    // parens to form one token tree, same as the rule above.
    ($($rest:tt)*) => {
        parse_union!([]; $($rest)*)
    };
}

// Internal Helper: Splits a `|`-separated union of type atoms (each
// optionally suffixed with `?`) into a flat list of `Type` expressions at
// macro-expansion time, only wrapping them in `Type::Union` if more than one
// remains. This differs from `Type::union`, which merges two already-
// materialized `Type` values at runtime and so must defensively deduplicate
// and flatten nested unions since it can't assume anything about its inputs'
// shape; here, the members are exactly the atoms written in the source, so
// building the final `Vec` once, directly, is enough - at the cost of not
// deduplicating a redundant union written by hand (e.g. `number? | nil`
// duplicates `nil`). Authors are expected not to write redundant unions.
macro_rules! parse_union {
    ([$($members:tt)*]; $t:tt ?) => {
        parse_union!(@finish [$($members)* ty!($t), Type::Nil,])
    };
    ([$($members:tt)*]; $t:tt) => {
        parse_union!(@finish [$($members)* ty!($t),])
    };
    ([$($members:tt)*]; $t:tt ? | $($rest:tt)*) => {
        parse_union!([$($members)* ty!($t), Type::Nil,]; $($rest)*)
    };
    ([$($members:tt)*]; $t:tt | $($rest:tt)*) => {
        parse_union!([$($members)* ty!($t),]; $($rest)*)
    };

    (@finish [$only:expr $(,)?]) => { $only };
    (@finish [$($members:expr),+ $(,)?]) => { Type::Union(vec![$($members),+]) };
}

// Internal Helper: Parses a comma-separated parameter stream into a
// `Vec<FunctionTypeParam>`. Delegates to `parse_slots!` so each parameter may
// itself be a `|`-separated union type (e.g. `'V | nil`).
macro_rules! parse_params {
    ( $($all:tt)* ) => {
        parse_slots!(FunctionTypeParam::Type, FunctionTypeParam::Vararg; []; $($all)*)
    };
}

// Internal Helper: Parses a function's return type(s) into a
// `Vec<FunctionTypeReturn>`. Accepts either a single (possibly `|`-unioned)
// type, or an explicitly parenthesized, comma-separated tuple of types, each
// of which may itself be a `|`-unioned type.
macro_rules! parse_returns {
    ( ( $($inner:tt)* ) ) => {
        parse_slots!(FunctionTypeReturn::Type, FunctionTypeReturn::Vararg; []; $($inner)*)
    };
    ( $($r:tt)* ) => {
        parse_slots!(FunctionTypeReturn::Type, FunctionTypeReturn::Vararg; []; $($r)*)
    };
}

// Internal Helper: Token muncher shared by `parse_params!` and
// `parse_returns!`. Splits the trailing token stream on top-level commas into
// slots, building a `$type_ctor(ty!(slot))` element for each one (or
// `$vararg_ctor(ty!(slot))` for a slot prefixed with `...`), and finally
// expands to a `vec![...]` literal of those elements. Each slot's tokens are
// accumulated verbatim and only handed to `ty!` once its end (a comma or the
// end of input) is found, so a slot may itself contain a `|`-separated union,
// e.g. `'V | nil`.
//
// `$type_ctor`/`$vararg_ctor` are the full paths to the enum's tuple-variant
// constructors (e.g. `FunctionTypeParam::Type`), passed in as `path`
// fragments so they can be invoked directly as `$ctor(...)`. A `path`
// fragment can't be extended with further `::` segments once bound, which is
// why the variant isn't selected by gluing an ident onto a shared enum path.
//
// `$elems` accumulates the already-built `$ctor(ty!(..))` elements (with
// trailing commas) so the whole list can be produced as a single `vec![...]`
// expression, rather than an initially-empty, conditionally-mutated `Vec`.
macro_rules! parse_slots {
    ($type_ctor:path, $vararg_ctor:path; [$($elems:tt)*]; ) => {
        vec![$($elems)*]
    };
    ($type_ctor:path, $vararg_ctor:path; [$($elems:tt)*]; @ $($rest:tt)*) => {
        parse_slots!(@collect $type_ctor, $vararg_ctor, $vararg_ctor, []; [$($elems)*]; $($rest)*)
    };
    ($type_ctor:path, $vararg_ctor:path; [$($elems:tt)*]; $($rest:tt)*) => {
        parse_slots!(@collect $type_ctor, $vararg_ctor, $type_ctor, []; [$($elems)*]; $($rest)*)
    };

    (@collect $type_ctor:path, $vararg_ctor:path, $ctor:path, [$($acc:tt)+]; [$($elems:tt)*]; , $($rest:tt)*) => {
        parse_slots!($type_ctor, $vararg_ctor; [$($elems)* $ctor(ty!($($acc)+)),]; $($rest)*)
    };
    (@collect $type_ctor:path, $vararg_ctor:path, $ctor:path, [$($acc:tt)+]; [$($elems:tt)*]; ) => {
        vec![$($elems)* $ctor(ty!($($acc)+))]
    };
    (@collect $type_ctor:path, $vararg_ctor:path, $ctor:path, [$($acc:tt)*]; [$($elems:tt)*]; $next:tt $($rest:tt)*) => {
        parse_slots!(@collect $type_ctor, $vararg_ctor, $ctor, [$($acc)* $next]; [$($elems)*]; $($rest)*)
    };
}

macro_rules! namespace_types {
    ($type_fn:ident, $field_fn:ident { $($field:literal => $ty:expr),* $(,)? }) => {
        #[doc = concat!("Builds the builtin `", stringify!($type_fn), "` namespace type.")]
        fn $type_fn() -> Type {
            Type::Table {
                fields: HashMap::from([$( (SmolStr::new_static($field), $ty) ),*]),
                array: None,
            }
        }
    };
}

/// Declares the flat table of global builtin names and their type schemes.
/// Expands to both `GLOBAL_NAMES` (the flattened list of installed names)
/// and `global_type` (the name -> type scheme lookup) from a single source
/// of truth, so a name can never be listed in one without appearing, with
/// its type, in the other.
macro_rules! global_types {
    ($($($name:literal)|+ => $ty:expr),* $(,)?) => {
        /// Names installed in the Luau global builtin environment.
        const GLOBAL_NAMES: &[&str] = &[$($($name),+),*];

        /// Builds one global type scheme from Luau's embedded builtin definitions.
        // luau/Analysis/src/EmbeddedBuiltinDefinitions.cpp
        fn global_type(name: &SmolStr) -> Option<Type> {
            Some(match name.as_str() {
                $($($name)|+ => $ty,)*
                _ => return None,
            })
        }
    };
}

global_types! {
    "getfenv" => ty!(fn(any) -> { string => any }),
    "_G" => ty!(any),
    "_VERSION" => ty!(string),
    "gcinfo" => ty!(fn() -> number),
    "print" => ty!(fn<T>(@T) -> unit),
    "type" | "typeof" => ty!(fn<T>(T) -> string),
    "assert" => ty!(fn<T>(T, string?) -> T),
    "error" => ty!(fn<T>(T, number?) -> never),
    "tostring" => ty!(fn<T>(T) -> string),
    "tonumber" => ty!(fn<T>(T, number?) -> number?),
    "rawequal" => ty!(fn<A, B>(A, B) -> boolean),
    "rawget" => ty!(fn<K, V>({ K => V }, K) -> V?),
    "rawset" => ty!(fn<K, V>({ K => V }, K, V) -> { K => V }),
    "rawlen" => ty!(fn<K, V>({ K => V } | string) -> number),
    "setmetatable" => ty!(fn<T, M>(T, M) -> T),
    "setfenv" => ty!(fn<T, R>(number | (fn(@T) -> @R), { string => any }) -> (fn(@T) -> @R)?),
    "ipairs" => ty!(fn<V>({ number => V }) -> (
        fn({ number => V }, number) -> (number?, V),
        { number => V },
        number
    )),
    "pcall" => ty!(fn<A, R>(fn(@A) -> @R, @A) -> (boolean, @R)),
    "xpcall" => ty!(fn<E, A, R1, R2>(fn(@A) -> @R1, fn(E) -> @R2, @A) -> (boolean, @R1)),
    "select" => ty!(fn<A>(string | number, @A) -> @any),
    "loadstring" => ty!(fn<A>(string, string?) -> ((fn(@A) -> any)?, string?)),
    "newproxy" => ty!(fn(boolean?) -> any),
    "unpack" => ty!(fn<V>({ number => V }, number?, number?) -> @V),
    "string" => string_type(),

    "bit32" => bit32_type(),
    "math" => math_type(),
    "os" => os_type(),
    "coroutine" => coroutine_type(),
    "table" => table_type(),
    "debug" => debug_type(),
    "utf8" => utf8_type(),
    "buffer" => buffer_type(),
    "vector" => vector_type(),
    "integer" => integer_type(),
    "class" => class_type(),
    "types" => types_type(),
}
namespace_types!(string_type, string_field_type {
    "byte" => ty!(fn(string, number?, number?) -> @number),
    "char" => ty!(fn(@number) -> string),
    "find" => ty!(fn(string, string, number?, boolean?) -> (number?, number?, @string)),
    "format" => ty!(fn(string, @any) -> string),
    "gmatch" => ty!(fn(string, string) -> (fn() -> @string)),
    "gsub" => ty!(fn(string, string, any, number?) -> (string, number)),
    "len" => ty!(fn(string) -> number),
    "lower" => ty!(fn(string) -> string),
    "match" => ty!(fn(string, string, number?) -> @string),
    "pack" => ty!(fn(string, @any) -> string),
    "packsize" => ty!(fn(string) -> number),
    "rep" => ty!(fn(string, number, string?) -> string),
    "reverse" => ty!(fn(string) -> string),
    "split" => ty!(fn(string, string?) -> { number => string }),
    "sub" => ty!(fn(string, number, number?) -> string),
    "unpack" => ty!(fn(string, string, number?) -> @any),
    "upper" => ty!(fn(string) -> string),
});

namespace_types!(bit32_type, bit32_field_type {
    "band" => ty!(fn(@number) -> number),
    "bor" => ty!(fn(@number) -> number),
    "bxor" => ty!(fn(@number) -> number),
    "btest" => ty!(fn(number, @number) -> boolean),
    "rrotate" => ty!(fn(number, number) -> number),
    "lrotate" => ty!(fn(number, number) -> number),
    "lshift" => ty!(fn(number, number) -> number),
    "arshift" => ty!(fn(number, number) -> number),
    "rshift" => ty!(fn(number, number) -> number),
    "bnot" => ty!(fn(number) -> number),
    "extract" => ty!(fn(number, number, number?) -> number),
    "replace" => ty!(fn(number, number, number, number?) -> number),
    "countlz" => ty!(fn(number) -> number),
    "countrz" => ty!(fn(number) -> number),
    "byteswap" => ty!(fn(number) -> number),
});

namespace_types!(math_type, math_field_type {
    "frexp" => ty!(fn(number) -> (number, number)),
    "ldexp" => ty!(fn(number, number) -> number),
    "fmod" => ty!(fn(number, number) -> number),
    "modf" => ty!(fn(number) -> (number, number)),
    "pow" => ty!(fn(number, number) -> number),
    "exp" => ty!(fn(number) -> number),
    "ceil" => ty!(fn(number) -> number),
    "floor" => ty!(fn(number) -> number),
    "abs" => ty!(fn(number) -> number),
    "sqrt" => ty!(fn(number) -> number),
    "log" => ty!(fn(number, number?) -> number),
    "log10" => ty!(fn(number) -> number),
    "rad" => ty!(fn(number) -> number),
    "deg" => ty!(fn(number) -> number),
    "sin" => ty!(fn(number) -> number),
    "cos" => ty!(fn(number) -> number),
    "tan" => ty!(fn(number) -> number),
    "sinh" => ty!(fn(number) -> number),
    "cosh" => ty!(fn(number) -> number),
    "tanh" => ty!(fn(number) -> number),
    "atan" => ty!(fn(number) -> number),
    "acos" => ty!(fn(number) -> number),
    "asin" => ty!(fn(number) -> number),
    "atan2" => ty!(fn(number, number) -> number),
    "min" => ty!(fn(number, @number) -> number),
    "max" => ty!(fn(number, @number) -> number),
    "pi" => ty!(number),
    "huge" => ty!(number),
    "nan" => ty!(number),
    "e" => ty!(number),
    "phi" => ty!(number),
    "sqrt2" => ty!(number),
    "tau" => ty!(number),
    "randomseed" => ty!(fn(number) -> unit),
    "random" => ty!(fn(number?, number?) -> number),
    "sign" => ty!(fn(number) -> number),
    "clamp" => ty!(fn(number, number, number) -> number),
    "noise" => ty!(fn(number, number?, number?) -> number),
    "round" => ty!(fn(number) -> number),
    "map" => ty!(fn(number, number, number, number, number) -> number),
    "lerp" => ty!(fn(number, number, number) -> number),
    "isnan" => ty!(fn(number) -> boolean),
    "isinf" => ty!(fn(number) -> boolean),
    "isfinite" => ty!(fn(number) -> boolean),
});

/// Builds the record returned by the table-producing `os.date` overload.
fn date_type_result() -> Type {
    ty!({
        year: number,
        month: number,
        wday: number,
        yday: number,
        day: number,
        hour: number,
        min: number,
        sec: number,
        isdst: boolean,
    })
}

/// Builds the overloaded type of `os.date`.
fn os_date_type() -> Type {
    Type::Intersection(vec![
        Type::Function {
            generics: Vec::new(),
            params: vec![
                FunctionTypeParam::Type(ty!("*t" | "!*t")),
                FunctionTypeParam::Type(ty!(number?)),
            ],
            return_type: vec![FunctionTypeReturn::Type(date_type_result())],
        },
        ty!(fn(string?, number?) -> string),
    ])
}

/// Builds the type of `os.difftime` using its shared date-record shape.
fn os_difftime_type() -> Type {
    let date_or_number = date_type_result().union(ty!(number));

    Type::Function {
        generics: Vec::new(),
        params: vec![
            FunctionTypeParam::Type(date_or_number.clone()),
            FunctionTypeParam::Type(date_or_number),
        ],
        return_type: vec![FunctionTypeReturn::Type(ty!(number))],
    }
}

namespace_types!(os_type, os_field_type {
    "time" => ty!(fn({
        year: number,
        month: number,
        day: number,
        hour: (number?),
        min: (number?),
        sec: (number?),
        isdst: (boolean?),
    }?) -> number),
    "date" => os_date_type(),
    "difftime" => os_difftime_type(),
    "clock" => ty!(fn() -> number),
});

namespace_types!(coroutine_type, coroutine_field_type {
    "create" => ty!(fn<A, R>(fn(@A) -> @R) -> thread),
    "resume" => ty!(fn<A, R>(thread, @A) -> (boolean, @R)),
    "running" => ty!(fn() -> thread),
    "status" => ty!(fn(thread) -> ("dead" | "running" | "normal" | "suspended")),
    "wrap" => ty!(fn<A, R>(fn(@A) -> @R) -> (fn(@A) -> @R)),
    "yield" => ty!(fn<A, R>(@A) -> @R),
    "isyieldable" => ty!(fn() -> boolean),
    "close" => ty!(fn(thread) -> (boolean, any)),
});

namespace_types!(table_type, table_field_type {
    "concat" => ty!(fn<V>({ number => V }, string?, number?, number?) -> string),
    "insert" => Type::Intersection(vec![
        ty!(fn<V>({ number => V }, V) -> unit),
        ty!(fn<V>({ number => V }, number, V) -> unit),
    ]),
    "maxn" => ty!(fn<V>({ number => V }) -> number),
    "remove" => ty!(fn<V>({ number => V }, number?) -> V?),
    "sort" => ty!(fn<V>({ number => V }, (fn(V, V) -> boolean)?) -> unit),
    "create" => ty!(fn<V>(number, V?) -> { number => V }),
    "find" => ty!(fn<V>({ number => V }, V, number?) -> number?),
    "unpack" => ty!(fn<V>({ number => V }, number?, number?) -> @V),
    "pack" => ty!(fn<V>(@V) -> { number => V, n: number }),
    "getn" => ty!(fn<V>({ number => V }) -> number),
    "foreach" => ty!(fn<K, V>({ K => V }, fn(K, V) -> unit) -> unit),
    "foreachi" => ty!(fn<V>({ number => V }, fn(number, V) -> unit) -> unit),
    "move" => ty!(fn<V>({ number => V }, number, number, number, { number => V }?) -> { number => V }),
    "clear" => ty!(fn({}) -> unit),
    "isfrozen" => ty!(fn({}) -> boolean),
});

namespace_types!(debug_type, debug_field_type {
    "info" => Type::Intersection(vec![
        ty!(fn(thread, number, string) -> @any),
        ty!(fn(number, string) -> @any),
        ty!(fn<A, R>(fn(@A) -> @R, string) -> @any),
    ]),
    "traceback" => Type::Intersection(vec![
        ty!(fn(string?, number?) -> string),
        ty!(fn(thread, string?, number?) -> string),
    ]),
});

namespace_types!(utf8_type, utf8_field_type {
    "char" => ty!(fn(@number) -> string),
    "charpattern" => ty!(string),
    "codes" => ty!(fn(string) -> (fn(string, number) -> (number, number), string, number)),
    "codepoint" => ty!(fn(string, number?, number?) -> @number),
    "len" => ty!(fn(string, number?, number?) -> (number?, number?)),
    "offset" => ty!(fn(string, number?, number?) -> number),
});

namespace_types!(buffer_type, buffer_field_type {
    "create" => ty!(fn(number) -> buffer),
    "fromstring" => ty!(fn(string) -> buffer),
    "tostring" => ty!(fn(buffer) -> string),
    "len" => ty!(fn(buffer) -> number),
    "copy" => ty!(fn(buffer, number, buffer, number?, number?) -> unit),
    "fill" => ty!(fn(buffer, number, number, number?) -> unit),
    "readi8" => ty!(fn(buffer, number) -> number),
    "readu8" => ty!(fn(buffer, number) -> number),
    "readi16" => ty!(fn(buffer, number) -> number),
    "readu16" => ty!(fn(buffer, number) -> number),
    "readi32" => ty!(fn(buffer, number) -> number),
    "readu32" => ty!(fn(buffer, number) -> number),
    "readf32" => ty!(fn(buffer, number) -> number),
    "readf64" => ty!(fn(buffer, number) -> number),
    "writei8" => ty!(fn(buffer, number, number) -> unit),
    "writeu8" => ty!(fn(buffer, number, number) -> unit),
    "writei16" => ty!(fn(buffer, number, number) -> unit),
    "writeu16" => ty!(fn(buffer, number, number) -> unit),
    "writei32" => ty!(fn(buffer, number, number) -> unit),
    "writeu32" => ty!(fn(buffer, number, number) -> unit),
    "writef32" => ty!(fn(buffer, number, number) -> unit),
    "writef64" => ty!(fn(buffer, number, number) -> unit),
    "readstring" => ty!(fn(buffer, number, number) -> string),
    "writestring" => ty!(fn(buffer, number, string, number?) -> unit),
    "readbits" => ty!(fn(buffer, number, number) -> number),
    "writebits" => ty!(fn(buffer, number, number, number) -> unit),
    "readinteger" => ty!(fn(buffer, number) -> integer),
    "writeinteger" => ty!(fn(buffer, number, integer) -> unit),
});

namespace_types!(vector_type, vector_field_type {
    "create" => ty!(fn(number, number, number?) -> vector),
    "magnitude" => ty!(fn(vector) -> number),
    "normalize" => ty!(fn(vector) -> vector),
    "cross" => ty!(fn(vector, vector) -> vector),
    "dot" => ty!(fn(vector, vector) -> number),
    "angle" => ty!(fn(vector, vector, vector?) -> number),
    "floor" => ty!(fn(vector) -> vector),
    "ceil" => ty!(fn(vector) -> vector),
    "abs" => ty!(fn(vector) -> vector),
    "sign" => ty!(fn(vector) -> vector),
    "clamp" => ty!(fn(vector, vector, vector) -> vector),
    "max" => ty!(fn(vector, @vector) -> vector),
    "min" => ty!(fn(vector, @vector) -> vector),
    "lerp" => ty!(fn(vector, vector, number) -> vector),
    "zero" => ty!(vector),
    "one" => ty!(vector),
});

namespace_types!(integer_type, integer_field_type {
    "create" => ty!(fn(number) -> integer),
    "tonumber" => ty!(fn(integer) -> number),
    "neg" => ty!(fn(integer) -> integer),
    "add" => ty!(fn(integer, integer) -> integer),
    "sub" => ty!(fn(integer, integer) -> integer),
    "mul" => ty!(fn(integer, integer) -> integer),
    "div" => ty!(fn(integer, integer) -> integer),
    "rem" => ty!(fn(integer, integer) -> integer),
    "idiv" => ty!(fn(integer, integer) -> integer),
    "mod" => ty!(fn(integer, integer) -> integer),
    "udiv" => ty!(fn(integer, integer) -> integer),
    "urem" => ty!(fn(integer, integer) -> integer),
    "min" => ty!(fn(integer, @integer) -> integer),
    "max" => ty!(fn(integer, @integer) -> integer),
    "band" => ty!(fn(@integer) -> integer),
    "bor" => ty!(fn(@integer) -> integer),
    "bnot" => ty!(fn(integer) -> integer),
    "bxor" => ty!(fn(@integer) -> integer),
    "lt" => ty!(fn(integer, integer) -> boolean),
    "le" => ty!(fn(integer, integer) -> boolean),
    "ult" => ty!(fn(integer, integer) -> boolean),
    "ule" => ty!(fn(integer, integer) -> boolean),
    "gt" => ty!(fn(integer, integer) -> boolean),
    "ge" => ty!(fn(integer, integer) -> boolean),
    "ugt" => ty!(fn(integer, integer) -> boolean),
    "uge" => ty!(fn(integer, integer) -> boolean),
    "lshift" => ty!(fn(integer, integer) -> integer),
    "rshift" => ty!(fn(integer, integer) -> integer),
    "arshift" => ty!(fn(integer, integer) -> integer),
    "lrotate" => ty!(fn(integer, integer) -> integer),
    "rrotate" => ty!(fn(integer, integer) -> integer),
    "extract" => ty!(fn(integer, integer, integer?) -> integer),
    "replace" => ty!(fn(integer, integer, integer, integer?) -> integer),
    "clamp" => ty!(fn(integer, integer, integer) -> integer),
    "btest" => ty!(fn(@integer) -> boolean),
    "countrz" => ty!(fn(integer) -> integer),
    "countlz" => ty!(fn(integer) -> integer),
    "bswap" => ty!(fn(integer) -> integer),
    "fromstring" => ty!(fn(string, number?) -> integer),
    "minsigned" => ty!(integer),
    "maxsigned" => ty!(integer),
});

namespace_types!(class_type, class_field_type {
    "isinstance" => ty!(fn(unknown, named "class") -> boolean),
    "classof" => ty!(fn(unknown) -> (named "class")?),
});

/// Returns the named reflection type exported by the `types` library.
fn type_named() -> Type {
    ty!(named "type")
}

/// Builds the property descriptor accepted by `types.newtable`.
fn type_properties_type() -> Type {
    ty!({
        (named "type") => {
            read: ((named "type")?),
            write: ((named "type")?),
        }
    })
}

/// Builds the full signature of `types.newtable`.
fn types_newtable_type() -> Type {
    Type::Function {
        generics: Vec::new(),
        params: vec![
            FunctionTypeParam::Type(
                ty!({ (named "type") => (named "type") })
                    .union(type_properties_type())
                    .union(ty!(nil)),
            ),
            FunctionTypeParam::Type(
                ty!({
                    index: (named "type"),
                    readresult: (named "type"),
                    writeresult: (named "type"),
                })
                .union(ty!(nil)),
            ),
            FunctionTypeParam::Type(type_named().union(ty!(nil))),
        ],
        return_type: vec![FunctionTypeReturn::Type(type_named())],
    }
}

/// Builds the full signature of `types.newfunction`.
fn types_newfunction_type() -> Type {
    let head_tail = ty!({
        head: ({ number => (named "type") }?),
        tail: ((named "type")?),
    });

    Type::Function {
        generics: Vec::new(),
        params: vec![
            FunctionTypeParam::Type(head_tail.clone().union(ty!(nil))),
            FunctionTypeParam::Type(head_tail.union(ty!(nil))),
            FunctionTypeParam::Type(ty!({ number => (named "type") }).union(ty!(nil))),
        ],
        return_type: vec![FunctionTypeReturn::Type(type_named())],
    }
}

namespace_types!(types_type, types_field_type {
    "unknown" => type_named(),
    "never" => type_named(),
    "any" => type_named(),
    "boolean" => type_named(),
    "number" => type_named(),
    "string" => type_named(),
    "thread" => type_named(),
    "buffer" => type_named(),
    "integer" => type_named(),
    "singleton" => ty!(fn(string | boolean | nil) -> (named "type")),
    "optional" => ty!(fn(named "type") -> (named "type")),
    "generic" => ty!(fn(string, boolean?) -> (named "type")),
    "negationof" => ty!(fn(named "type") -> (named "type")),
    "unionof" => ty!(fn(@(named "type")) -> (named "type")),
    "intersectionof" => ty!(fn(@(named "type")) -> (named "type")),
    "newtable" => types_newtable_type(),
    "newfunction" => types_newfunction_type(),
    "copy" => ty!(fn(named "type") -> (named "type")),
});
