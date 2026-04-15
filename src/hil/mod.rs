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

#[derive(Debug, Clone)]
pub struct StructuredFunction {
    pub cfg: ControlFlowGraph,
    pub root: RegionNode,

    pub upvalues: Vec<SymbolId>,
    pub is_vararg: bool,
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
            cfg,
            root,
            upvalues,
            is_vararg: proto.is_vararg,
        }
    }
}
