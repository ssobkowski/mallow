use crate::{
    disasm::Proto,
    hil::{
        cflow::{
            cfg::ControlFlowGraph,
            graph::GraphView,
            phoenix,
            region::{self, RegionNode},
        },
        lifter::ssa::SymbolId,
    },
    logging::{is_verbose, verbose},
};

pub mod cflow;
pub mod common;
pub mod ir;
pub mod lifter;
pub mod passes;
pub mod visitor;

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

    pub was_reduced: bool,
}

impl StructuredFunction {
    pub fn from_proto(proto: &Proto, all_protos: &[Proto]) -> Self {
        verbose!(
            "proto {} ({} params, {} upvalues)",
            proto.index,
            proto.num_params,
            proto.num_upvals
        );

        verbose!(indent: 1, "building cfg...");
        let mut cfg = ControlFlowGraph::from_proto(proto, all_protos);

        verbose!(indent: 1, "running pre-region passes...");
        if passes::run_pre_region(&mut cfg) {
            cfg.simplify_conditions();
        }

        if is_verbose() {
            let idoms = cfg.build_idoms();

            verbose!(indent: 1, "cfg {{");
            for (i, block) in cfg.blocks().enumerate() {
                verbose!(indent: 2, "block {} {{", i);

                if block.stmts().is_empty() {
                    verbose!(indent: 3, "stmts: [empty]");
                } else {
                    verbose!(indent: 3, "stmts: [");
                    for stmt in block.stmts() {
                        verbose!(indent: 3, "  {}", stmt.node);
                    }
                    verbose!(indent: 3, "]");
                }

                verbose!(indent: 3, "exit: {:?}", block.exit());

                verbose!(indent: 3, "predecessors: {:?}", cfg.predecessors(i));
                verbose!(indent: 3, "successors: {:?}", cfg.successors(i));
                verbose!(indent: 3, "idom: {:?}", idoms.idom(i));

                verbose!(indent: 2, "}}");
            }
            verbose!(indent: 1, "}}");
        }

        verbose!(indent: 1, "structuring region...");
        let (root, was_reduced) =
            if std::env::var("MALLOW_LEGACY_STRUCTURER").is_ok_and(|f| f == "1") {
                region::structure(&cfg)
            } else {
                phoenix::structure(&cfg)
            };

        if !was_reduced {
            eprintln!(
                "[proto {}] Failed to structure region properly. The output may be incorrect.",
                proto.index
            )
        }

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
            was_reduced,
        }
    }
}
