//! Random Luau program generator for differential testing of mallow.
//!
//! Fuzzing a decompiler checks one property on many random programs. For any
//! program `P`, running `P` prints the same output as running
//! `decompile(compile(P))`. [`Generator`] only builds programs that are valid,
//! halt and never raise, so any difference is a mallow bug. [`harness`]
//! runs that check.
//!
//! Programs focus on control flow. Every value is a number, and the shapes
//! that stress a decompiler are `if` chains, guards with `break`, `continue`
//! and `return`, every loop form, deferred initialization, closures over loop
//! variables, multiple returns, varargs, `pcall` and recursion.

mod config;
mod dice;
mod expr;
mod generator;
pub mod harness;
mod scope;
mod syntax;

pub use config::{Config, Weights};
pub use generator::Generator;
use mallow_core::ast::Block;

/// Generates the program for `seed`.
pub fn generate(seed: u64, config: &Config) -> Block {
    Generator::new(seed, config.clone()).program()
}

/// Generates the program for `seed` and prints it with mallow's printer.
pub fn generate_source(seed: u64, config: &Config) -> String {
    mallow_core::printer::print(&generate(seed, config))
}
