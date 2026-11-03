# mallow-fuzzer

A random Luau program generator for differential testing of mallow.

For any generated program `P`, running `P` must print the same output as
running `decompile(compile(P))`. The generator only builds programs that are
valid, halt and never raise, so any difference is a mallow bug.

Programs focus on control flow. Every value is a number, which keeps every
expression free of runtime errors without a type model. The generated shapes
are `if`/`elseif` chains, guards ending in `break`, `continue`, `return` or
`error`, `while`, `repeat`, numeric `for`, `ipairs`, `pairs` and generalized
iteration, stateless and closure iterators, deferred initialization, closures
over loop variables, upvalue mutation, multiple returns and assignments,
varargs, `pcall`, self-recursion with fuel, if-expressions and
`a and b or c`.

## Usage

Print a program:

```bash
cargo run -p mallow-fuzzer -- gen --seed 42
```

Run the differential check. This installs the managed Luau release through
`mallow-luau-toolchain` on first use, then compiles at `-O0`, `-O1` and `-O2`:

```bash
just fuzz --count 1000
just fuzz --count 1000 --luau 0.700 -O 2
```

Only check that generated programs run cleanly:

```bash
just fuzz --count 10000 --no-decompile
```

Failures are saved to `findings/<category>/<seed>/` with the program, the
bytecode, the decompiled source, expected and actual output, and an
`info.txt` with the command that regenerates the program. Categories with a
`generator/` prefix are generator bugs. Categories with a `mallow/O<n>-`
prefix are `decompile-panic`, `decompile-error`, `decompile-stack-overflow`,
`decompile-timeout`, `invalid-output`, `output-runtime-error`,
`output-timeout` and `mismatch`.

Each decompilation runs in a child process (`mallow-fuzzer decompile`), so a
stack overflow or a hang fails only its own case.

## Tuning

```bash
--stmts 200                 # program size
--block-depth 3             # nesting
--expr-depth 4
--weight while_loop=20      # statement mix, repeatable, 0 turns a shape off
```

The weight names are `local assign multi_assign compound_assign print call
if_stmt guard numeric_for while_loop repeat_loop ipairs_for pairs_for
iterator_for do_block local_function deferred_init closures pcall recursion`.

