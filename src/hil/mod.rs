use crate::{
    disasm::Proto,
    hil::cflow::{
        graph::ControlFlowGraph,
        region2::{self, RegionNode},
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

    pub is_vararg: bool,
}

impl StructuredFunction {
    pub fn from_proto(proto: &Proto, all_protos: &[Proto]) -> Self {
        let cfg = ControlFlowGraph::from_proto(proto, all_protos);
        let root = region2::structure(&cfg);

        Self {
            cfg,
            root,
            is_vararg: proto.is_vararg,
        }
    }
}
