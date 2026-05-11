use crate::{
    disasm::Proto,
    hil::{
        cflow::{
            cfg::ControlFlowGraph,
            phoenix,
            region::{self, RegionNode},
        },
        lifter::ssa::SymbolId,
    },
    logging::verbose,
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
    pub cfg: ControlFlowGraph,
    pub root: RegionNode,

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

        eprintln!("{:#?}", cfg);

        verbose!(indent: 1, "structuring region...");
        let (root, was_reduced) = if std::env::var("MALLOW_PHOENIX").is_ok_and(|f| f == "1") {
            phoenix::structure(&cfg)
        } else {
            region::structure(&cfg)
        };

        if !was_reduced {
            eprintln!(
                "[proto {}] Failed to structure region properly. The output may be incorrect.",
                proto.index
            )
        }

        let upvalues = cfg.upvalues.clone();

        Self {
            proto: proto.index as usize,
            cfg,
            root,
            upvalues,
            is_vararg: proto.is_vararg,
            return_arity: None,
            was_reduced,
        }
    }
}
