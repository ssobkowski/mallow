//! Knobs that shape generated programs.

use anyhow::{Result, bail};

/// Settings for generating one program.
#[derive(Debug, Clone)]
pub struct Config {
    /// Rough number of statements in a program.
    pub max_stmts: u32,
    /// Deepest nesting of blocks such as `if`, loops, functions and `do`.
    pub max_block_depth: u32,
    /// Most statements generated directly inside one block.
    pub max_block_len: u32,
    /// Deepest nesting of one expression.
    pub max_expr_depth: u32,
    /// Deepest nesting of function definitions.
    pub max_fn_depth: u32,
    pub weights: Weights,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            max_stmts: 120,
            max_block_depth: 5,
            max_block_len: 6,
            max_expr_depth: 3,
            max_fn_depth: 3,
            weights: Weights::default(),
        }
    }
}

/// Declares [`Weights`] with one field per statement shape, plus the lookup by
/// name that the command line uses.
macro_rules! weights {
    ($($name:ident = $default:expr),* $(,)?) => {
        /// Relative weights of statement shapes. A weight of 0 turns a shape off.
        #[derive(Debug, Clone)]
        pub struct Weights {
            $(pub $name: u32,)*
        }

        impl Default for Weights {
            fn default() -> Self {
                Self { $($name: $default,)* }
            }
        }

        impl Weights {
            /// Every weight name, in declaration order.
            pub const NAMES: &[&str] = &[$(stringify!($name),)*];

            /// Sets one weight from a `name=value` string.
            pub fn set(&mut self, spec: &str) -> Result<()> {
                let Some((name, value)) = spec.split_once('=') else {
                    bail!("expected name=value, got {spec:?}");
                };
                let value: u32 = value.trim().parse()?;
                match name.trim() {
                    $(stringify!($name) => self.$name = value,)*
                    other => bail!(
                        "unknown weight {other:?}, known weights are {}",
                        Self::NAMES.join(", ")
                    ),
                }
                Ok(())
            }
        }
    };
}

weights! {
    local = 14,
    assign = 8,
    multi_assign = 2,
    compound_assign = 5,
    print = 10,
    call = 5,
    if_stmt = 10,
    guard = 6,
    numeric_for = 5,
    while_loop = 4,
    repeat_loop = 3,
    ipairs_for = 3,
    pairs_for = 2,
    iterator_for = 2,
    do_block = 1,
    local_function = 5,
    deferred_init = 3,
    closures = 2,
    pcall = 2,
    recursion = 1,
}
