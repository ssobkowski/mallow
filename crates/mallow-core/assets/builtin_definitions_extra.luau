-- Luau constructs these globals programmatically in BuiltinDefinitions.cpp,
-- so they are absent from EmbeddedBuiltinDefinitions.cpp.

declare function setmetatable<T, M>(table: T, metatable: M): T

declare string: {
    byte: (string, number?, number?) -> ...number,
    char: (...number) -> string,
    find: (string, string, number?, boolean?) -> (number?, number?, ...string),
    format: (string, ...any) -> string,
    gmatch: (string, string) -> (() -> ...string),
    gsub: (string, string, any, number?) -> (string, number),
    len: (string) -> number,
    lower: (string) -> string,
    match: (string, string, number?) -> ...string,
    pack: (string, ...any) -> string,
    packsize: (string) -> number,
    rep: (string, number, string?) -> string,
    reverse: (string) -> string,
    split: (string, string?) -> {string},
    sub: (string, number, number?) -> string,
    unpack: (string, string, number?) -> ...any,
    upper: (string) -> string,
}
