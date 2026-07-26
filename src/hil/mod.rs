pub mod cflow;
pub mod ir;
pub mod lifted;
pub mod lifter;
pub mod passes;
pub mod ty2;
pub mod visitor;

use anyhow::Result;

use crate::{
    hil::{
        cflow::{
            cfg::ControlFlowGraph,
            graph::GraphView,
            region::{self, RegionNode},
        },
        lifted::{FunctionTypes, LiftedFunction},
        lifter::ssa::FunctionSymbols,
    },
    il::ProtoId,
    logging::{Diagnostics, LogLevel, LogTarget},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReturnArity {
    Exact(usize),
    Unknown,
}

impl ReturnArity {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (ReturnArity::Unknown, _) | (_, ReturnArity::Unknown) => ReturnArity::Unknown,
            (ReturnArity::Exact(a), ReturnArity::Exact(b)) if a == b => ReturnArity::Exact(a),
            _ => ReturnArity::Unknown,
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructuredFunction {
    pub proto: ProtoId,
    pub debug_name: Option<String>,
    pub root: RegionNode,

    pub symbols: FunctionSymbols,
    pub types: FunctionTypes,
    pub is_vararg: bool,
    pub return_arity: Option<ReturnArity>,
}

impl StructuredFunction {
    /// Structures a lifted function without destroying SSA or running passes.
    pub(crate) fn from_lifted_ssa(lifted: LiftedFunction, diagnostics: &Diagnostics) -> Self {
        let diagnostics = diagnostics.for_proto(lifted.proto.0);
        let info = diagnostics.at(LogLevel::Info, LogTarget::Hil);

        dump_cfg(&lifted.cfg, &diagnostics);
        info.line(1, format_args!("structuring SSA region..."));
        let root = region::structure(&lifted.cfg, &diagnostics);

        Self {
            proto: lifted.proto,
            debug_name: lifted.debug_name,
            root,
            symbols: lifted.symbols,
            types: lifted.types,
            is_vararg: lifted.is_vararg,
            return_arity: None,
        }
    }

    pub fn from_lifted(mut lifted: LiftedFunction, diagnostics: &Diagnostics) -> Result<Self> {
        let diagnostics = diagnostics.for_proto(lifted.proto.0);
        let info = diagnostics.at(LogLevel::Info, LogTarget::Hil);

        lifted.destruct_ssa();
        lifted.cfg.unfold_phis();

        info.line(1, format_args!("running pre-region passes..."));
        let pre_region_changed = {
            let span = tracing::info_span!(
                "pre_region_passes",
                proto = lifted.proto.0,
                changed = tracing::field::Empty,
            );
            let _enter = span.enter();
            let changed = passes::run_pre_region(&mut lifted.cfg, &lifted.symbols);
            span.record("changed", changed);
            changed
        };
        if pre_region_changed {
            let span = tracing::info_span!("simplify_conditions", proto = lifted.proto.0);
            let _enter = span.enter();
            lifted.cfg.simplify_conditions();
        }

        dump_cfg(&lifted.cfg, &diagnostics);

        info.line(1, format_args!("structuring region..."));
        let root = {
            let span = tracing::info_span!("structure_region", proto = lifted.proto.0);
            let _enter = span.enter();
            region::structure(&lifted.cfg, &diagnostics)
        };

        Ok(Self {
            proto: lifted.proto,
            debug_name: lifted.debug_name,
            root,
            symbols: lifted.symbols,
            types: lifted.types,
            is_vararg: lifted.is_vararg,
            return_arity: None,
        })
    }
}

fn dump_cfg(cfg: &ControlFlowGraph, diagnostics: &Diagnostics) {
    let debug = diagnostics.at(LogLevel::Debug, LogTarget::Cfg);
    debug.block("cfg {", |debug| {
        let idoms = cfg.build_idoms();

        for (i, block) in cfg.blocks().enumerate() {
            debug.line(1, format_args!("block {} {{", i));

            if block.stmts().is_empty() {
                debug.line(2, format_args!("stmts: [empty]"));
            } else {
                debug.line(2, format_args!("stmts: ["));
                for stmt in block.stmts() {
                    debug.line(2, format_args!("  {}", stmt));
                }
                debug.line(2, format_args!("]"));
            }

            debug.line(2, format_args!("exit: {:?}", block.exit()));
            debug.line(2, format_args!("predecessors: {:?}", cfg.predecessors(i)));
            debug.line(2, format_args!("successors: {:?}", cfg.successors(i)));
            debug.line(2, format_args!("idom: {:?}", idoms.idom(i)));

            debug.line(1, format_args!("}}"));
        }
    });
    debug.line(0, format_args!("}}"));
}
