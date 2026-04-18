use crate::{
    disasm::Proto,
    hil::{
        cflow::{
            graph::ControlFlowGraph,
            region::{self, RegionNode},
        },
        lifter::ssa::SymbolId,
    },
};

pub mod cflow;
pub mod common;
pub mod ir;
pub mod lifter;
pub mod passes;

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
}

impl StructuredFunction {
    pub fn from_proto(proto: &Proto, all_protos: &[Proto]) -> Self {
        let cfg = ControlFlowGraph::from_proto(proto, all_protos);
        let (root, was_reduced) = region::structure(&cfg);

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
        }
    }
}
