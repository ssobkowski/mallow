# mallow-luau-toolchain

Crate that manages Luau binaries (`luau`, `luau-compile`, `luau-analyze` and, when available, `luau-ast`) used by [mallow-core/tests](crates/mallow-core/tests) to run tests across various Luau versions.

Every release version is kept in a centralized [registry](registry.json) along with the bytecode version the compiler produces, and hashes of the zip files.

By default, the crate downloads and caches the necessary Luau binaries in the platform cache directory. You can override this by setting `MALLOW_TOOLCHAIN_CACHE_DIR` to a different directory.
