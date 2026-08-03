//! Capture storage resolution for whole-program inference.

use crate::hil::ir::{Capture, Expr};
use crate::hil::lifted::LiftedFunction;
use crate::hil::visitor::{Visitor, walk_expr};
use crate::il::ProtoId;

/// Describes where one child upvalue gets its binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CaptureOrigin {
    /// The child receives a copy of the current value.
    Value,
    /// The child shares a local binding owned by its parent.
    Ref,
    /// The child shares one of its parent's upvalue bindings.
    Upvalue(usize),
}

/// Describes the captures used to create one child function.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CaptureLayout {
    /// Proto that creates the child closure.
    parent: ProtoId,
    /// Origin of each child upvalue slot.
    origins: Vec<CaptureOrigin>,
}

/// Says whether calls may replace the value in one captured binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StorageMutability {
    /// Calls cannot replace the captured value.
    ReadOnly,
    /// A closure call may replace the captured value.
    Mutable,
}

/// Tracks progress while resolving one captured binding.
#[derive(Debug, Default, Clone, Copy)]
enum StorageResolution {
    /// The binding has not been resolved yet.
    #[default]
    Unresolved,
    /// The binding is being resolved through a parent upvalue.
    Resolving,
    /// The binding has a resolved mutability.
    Resolved(StorageMutability),
}

/// Resolves capture storage across the lexical function graph.
pub(super) struct CaptureResolver {
    /// Mutability of each upvalue slot, indexed by proto ID.
    storage: Vec<Vec<StorageMutability>>,
}

impl CaptureResolver {
    /// Builds capture layouts and resolves every declared upvalue binding.
    pub(super) fn new(functions: &[LiftedFunction]) -> Self {
        let mut layouts = vec![None; functions.len()];
        for function in functions {
            CaptureLayoutCollector {
                parent: function,
                functions,
                layouts: &mut layouts,
            }
            .visit_graph(&function.cfg);
        }

        let mut resolutions: Vec<_> = functions
            .iter()
            .map(|function| vec![StorageResolution::Unresolved; function.symbols.upvalues().len()])
            .collect();
        for (proto, function) in functions.iter().enumerate() {
            for slot in 0..function.symbols.upvalues().len() {
                Self::resolve(proto, slot, &layouts, &mut resolutions);
            }
        }

        let storage = resolutions
            .into_iter()
            .map(|slots| {
                slots
                    .into_iter()
                    .map(|resolution| match resolution {
                        StorageResolution::Resolved(storage) => storage,
                        StorageResolution::Unresolved | StorageResolution::Resolving => {
                            unreachable!("all upvalue storage must be resolved")
                        }
                    })
                    .collect()
            })
            .collect();

        Self { storage }
    }

    /// Returns the mutability of one declared upvalue binding.
    #[inline]
    #[must_use]
    pub(super) fn storage(&self, proto: ProtoId, slot: usize) -> StorageMutability {
        self.storage
            .get(proto.0 as usize)
            .and_then(|slots| slots.get(slot))
            .copied()
            .expect("upvalue slot must index resolved capture storage")
    }

    /// Resolves one upvalue slot through its capture origin.
    fn resolve(
        proto: usize,
        slot: usize,
        layouts: &[Option<CaptureLayout>],
        resolutions: &mut [Vec<StorageResolution>],
    ) -> StorageMutability {
        match resolutions[proto][slot] {
            StorageResolution::Resolved(storage) => return storage,
            StorageResolution::Resolving => panic!("capture storage must not form a cycle"),
            StorageResolution::Unresolved => {}
        }
        resolutions[proto][slot] = StorageResolution::Resolving;

        let layout = layouts[proto]
            .as_ref()
            .expect("function with upvalues must have a capture layout");
        let origin = *layout
            .origins
            .get(slot)
            .expect("capture layout must cover every child upvalue");
        let storage = match origin {
            CaptureOrigin::Value => StorageMutability::ReadOnly,
            CaptureOrigin::Ref => StorageMutability::Mutable,
            CaptureOrigin::Upvalue(parent_slot) => {
                Self::resolve(layout.parent.0 as usize, parent_slot, layouts, resolutions)
            }
        };

        resolutions[proto][slot] = StorageResolution::Resolved(storage);
        storage
    }
}

/// Collects and validates the capture layout for each child proto.
struct CaptureLayoutCollector<'a> {
    /// Function that owns the visited closure expressions.
    parent: &'a LiftedFunction,
    /// Lifted functions indexed by proto ID.
    functions: &'a [LiftedFunction],
    /// Capture layouts indexed by child proto ID.
    layouts: &'a mut [Option<CaptureLayout>],
}

impl CaptureLayoutCollector<'_> {
    /// Resolves one HIL capture to its storage origin.
    fn origin(&self, capture: Capture) -> CaptureOrigin {
        match capture {
            Capture::Value(_) => CaptureOrigin::Value,
            Capture::Ref(_) => CaptureOrigin::Ref,
            Capture::Upvalue(symbol) => {
                let slot = self
                    .parent
                    .symbols
                    .slot_for_upvalue(symbol)
                    .expect("upvalue capture must use a declared parent upvalue");
                CaptureOrigin::Upvalue(slot)
            }
        }
    }
}

impl Visitor for CaptureLayoutCollector<'_> {
    /// Records the capture layout for one child closure.
    fn visit_expr(&mut self, expr: &Expr) {
        if let Expr::Closure { proto, captures } = expr {
            let child = self
                .functions
                .get(proto.0 as usize)
                .filter(|function| function.proto == *proto)
                .expect("closure proto must index its lifted function");
            assert_eq!(
                captures.len(),
                child.symbols.upvalues().len(),
                "closure captures must match child upvalues"
            );

            let layout = CaptureLayout {
                parent: self.parent.proto,
                origins: captures
                    .iter()
                    .copied()
                    .map(|capture| self.origin(capture))
                    .collect(),
            };
            let known = self
                .layouts
                .get_mut(proto.0 as usize)
                .expect("closure proto must index capture layouts");
            if let Some(known) = known {
                assert_eq!(known, &layout, "closure proto must use one capture layout");
            } else {
                *known = Some(layout);
            }
        }

        walk_expr(self, expr);
    }
}
