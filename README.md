# mallow

a Luau bytecode disassembler and decompiler.

> **Note:** only Luau bytecode version 6 is supported.

## Features

- **disassembly** - dump raw IL instructions for manual analysis
- **decompilation** - reconstruct readable Luau source from bytecode
- **control flow graphs** - interactive HTML visualizations (optional feature flag)

## Example

Input (`fib.luau`):

```luau
local memo: {number} = {}

local fib: (number) -> number
fib = function(n: number)
    if memo[n] then
        return memo[n]
    end
    if n <= 1 then
        return n
    end
    memo[n] = fib(n - 1) + fib(n - 2)
    return memo[n]
end

print(fib(24))
```

Decompiled output:

```luau
local v0 = {}
local v1 = nil
local v2
v2 = function(p0)
    if v0[p0] then
        return v0[p0]
    else
        if p0 > 1 then
            v0[p0] = v2(p0 - 1) + v2(p0 - 2)
            return v0[p0]
        else
            return p0
        end
    end
end
print(v2(24))
```

Control flow graph of the inner closure:

![CFG of the fib closure](docs/fib-cfg.png)

## Building

Requires Cargo.

```sh
cargo build --release
```

To include CFG visualization support:

```sh
cargo build --release --features visualize
```

Binary lands at `target/release/mallow`.

## Usage

**disassemble** - dump the raw instruction stream:

```sh
mallow disasm -i <bytecode>
```

**decompile** - reconstruct source from bytecode:

```sh
mallow decompile -i <bytecode>
```

**roundtrip** - compile a `.luau` file then immediately decompile it (requires `luau-compile` in PATH):

```sh
mallow roundtrip -i <source.luau>
```

**visualize** - generate an interactive CFG as HTML (requires `--features visualize`):

```sh
mallow visualize -i <bytecode> -o <output.html>
```

## Testing

Tests live in `tests/cases`. Each case is compiled with `luau-compile`, decompiled, and both versions are executed - stdout is compared for semantic equivalence rather than source text matching.

```sh
cargo test
```

