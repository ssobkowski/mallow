use crate::{
    disasm::Proto,
    hil::cflow::{
        graph::ControlFlowGraph,
        region::{RegionBlock, RegionBuilder},
        region2,
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
    pub root: RegionBlock,

    pub num_params: u8,
    pub is_vararg: bool,
}

impl StructuredFunction {
    pub fn from_proto(proto: &Proto, all_protos: &[Proto]) -> Self {
        let cfg = ControlFlowGraph::from_proto(proto, all_protos);
        let mut region = RegionBuilder::new(&cfg);
        let root = region.build_region(cfg.entry_block, None);

        eprintln!("{:#?}", cfg);

        let re2 = region2::structure(&cfg);
        eprintln!("{:#?}", re2);

        Self {
            cfg,
            root,
            num_params: proto.num_params,
            is_vararg: proto.is_vararg,
        }
    }
}
