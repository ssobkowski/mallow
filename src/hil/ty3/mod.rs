//! SSA-first type inference experiments.
//!
//! This module owns the next inference architecture. It reuses the existing
//! canonical type graph while keeping inference state separate from `ty2`.

#![allow(dead_code)]

pub mod inference;
