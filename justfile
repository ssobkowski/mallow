set positional-arguments := false

cli := "cargo run -q -p mallow-cli"
dev := cli + " --features luau-toolchain --"

# List recipes
default:
    @just --list

# Decompile a bytecode or Luau source file
decompile file *args:
    {{cli}} -- decompile {{file}} {{args}}

# Disassemble a bytecode or Luau source file
disasm file *args:
    {{cli}} -- disasm {{file}} {{args}}

# Decompile Luau source with a managed compiler, e.g. `just rt bc6 foo.luau` or `just rt 0.700 foo.luau`
rt luau file *args:
    {{dev}} decompile {{file}} --luau {{luau}} {{args}}

# Disassemble Luau source with a managed compiler, e.g. `just rtd bc6 foo.luau`
rtd luau file *args:
    {{dev}} disasm {{file}} --luau {{luau}} {{args}}

# Manage cached Luau releases, e.g. `just toolchain list --all`
toolchain *args:
    {{dev}} toolchain {{args}}

# Decompile with a Chrome trace written to trace.json
profile file *args:
    cargo run -q --release -p mallow-cli --features profile -- decompile {{file}} --profile-output trace.json {{args}}

# Render a CFG visualization
viz file out *args:
    cargo run -q -p mallow-cli --features visualize,luau-toolchain -- visualize {{file}} -o {{out}} {{args}}

# Run the whole test suite with every feature enabled
test *args:
    cargo test --workspace --all-features {{args}}

# Run clippy with every feature enabled
lint:
    cargo clippy --workspace --all-features --all-targets -- -D warnings

# Install the CLI with every feature enabled
install:
    cargo install --path crates/mallow-cli --all-features
