//! Canonical types and SSA-first inference.
//!
//! This module owns the type graph, bytecode type metadata, builtins, and
//! whole-program inference.

#![allow(dead_code)]

pub mod builtins;
pub mod bytecode;
pub mod canonical;
pub mod inference;
pub mod store;
