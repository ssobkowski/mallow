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

    pub num_params: u8,
    pub is_vararg: bool,
}

impl StructuredFunction {
    pub fn from_proto(proto: &Proto, all_protos: &[Proto]) -> Self {
        let cfg = ControlFlowGraph::from_proto(proto, all_protos);
        eprintln!("{:#?}", cfg);

        let root = region2::structure(&cfg);
        eprintln!("Region: {:#?}", root);

        Self {
            cfg,
            root,
            num_params: proto.num_params,
            is_vararg: proto.is_vararg,
        }
    }
}
