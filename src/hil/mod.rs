pub mod cflow;
pub mod common;
pub mod ir;
pub mod lifter;
pub mod passes;
pub mod visitor;

use crate::{
    disasm::Proto,
    hil::{
        cflow::{
            cfg::ControlFlowGraph,
            graph::GraphView,
            region::{self, RegionNode},
        },
        lifter::ssa::SymbolId,
    },
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
    pub proto: usize,
    pub debug_name: Option<String>,
    pub cfg: ControlFlowGraph,
    pub root: RegionNode,

    pub params: Vec<SymbolId>,
    pub upvalues: Vec<SymbolId>,
    pub is_vararg: bool,
    pub return_arity: Option<ReturnArity>,
}

impl StructuredFunction {
    pub fn from_proto(proto: &Proto, all_protos: &[Proto], diagnostics: &Diagnostics) -> Self {
        let span = tracing::info_span!(
            "structure_proto",
            proto = proto.index as usize,
            instr_count = proto.instrs.len(),
            param_count = proto.num_params,
            upvalue_count = proto.num_upvals,
        );
        let _enter = span.enter();

        let diagnostics = diagnostics.for_proto(proto.index as usize);
        let info = diagnostics.at(LogLevel::Info, LogTarget::Hil);

        info.line(
            0,
            format_args!("{} params, {} upvalues", proto.num_params, proto.num_upvals),
        );

        info.line(1, format_args!("building cfg..."));
        let mut cfg = {
            let span = tracing::info_span!("build_cfg", proto = proto.index as usize);
            let _enter = span.enter();
            ControlFlowGraph::from_proto(proto, all_protos)
        };

        info.line(1, format_args!("running pre-region passes..."));
        let pre_region_changed = {
            let span = tracing::info_span!(
                "pre_region_passes",
                proto = proto.index as usize,
                changed = tracing::field::Empty,
            );
            let _enter = span.enter();
            let changed = passes::run_pre_region(&mut cfg);
            span.record("changed", changed);
            changed
        };
        if pre_region_changed {
            let span = tracing::info_span!("simplify_conditions", proto = proto.index as usize);
            let _enter = span.enter();
            cfg.simplify_conditions();
        }

        dump_cfg(&cfg, &diagnostics);

        info.line(1, format_args!("structuring region..."));
        let root = {
            let span = tracing::info_span!("structure_region", proto = proto.index as usize);
            let _enter = span.enter();
            region::structure(&cfg, &diagnostics)
        };

        let params = cfg.params().to_vec();
        let upvalues = cfg.upvalues().to_vec();

        Self {
            proto: proto.index as usize,
            debug_name: proto.debug_name.clone(),
            cfg,
            root,
            params,
            upvalues,
            is_vararg: proto.is_vararg,
            return_arity: None,
        }
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
