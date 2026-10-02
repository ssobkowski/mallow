set positional-arguments := false

cli := "cargo run -q -p mallow-cli"
dev := cli + " --features luau-toolchain --"

# List recipes
default:
    @just --list

# Decompile a bytecode file
decompile file *args:
    {{cli}} -- decompile -i {{file}} {{args}}

# Disassemble a bytecode file
disasm file *args:
    {{cli}} -- disasm -i {{file}} {{args}}

# Compile Luau source with luau-compile on PATH and decompile it
rt file *args:
    {{cli}} roundtrip -i {{file}} {{args}}

# Roundtrip with the managed compiler for a bytecode version, e.g. `just rtb 6 foo.luau`
rtb bytecode file *args:
    {{dev}} roundtrip -i {{file}} --luau-bytecode {{bytecode}} {{args}}

# Roundtrip with an exact managed Luau release
rtr release file *args:
    {{dev}} roundtrip -i {{file}} --luau-release {{release}} {{args}}

# Decompile with a Chrome trace written to trace.json
profile file *args:
    cargo run -q --release -p mallow-cli --features profile -- decompile -i {{file}} --profile-output trace.json {{args}}

# Render a CFG visualization
viz file out *args:
    cargo run -q -p mallow-cli --features visualize -- visualize -i {{file}} -o {{out}} {{args}}

# Run the whole test suite with every feature enabled
test *args:
    cargo test --workspace --all-features {{args}}

# Run clippy with every feature enabled
lint:
    cargo clippy --workspace --all-features --all-targets -- -D warnings

# Install the CLI with every feature enabled
install:
    cargo install --path crates/mallow-cli --all-features
