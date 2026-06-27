use std::collections::HashMap;

use anyhow::Result;

use crate::{
    Diagnostics, LogLevel, LogTarget,
    disasm::Chunk,
    hil::{
        cflow::cfg::{self, ControlFlowGraph},
        lifter::ssa::SymbolId,
        ty::{Type, TypeId, TypeStore},
    },
    il::{Proto, ProtoId},
};

#[derive(Debug, Clone)]
pub struct SymbolTypeFacts {
    bytecode: Option<TypeId>,
    inferred: Option<TypeId>,
}

impl SymbolTypeFacts {
    fn from_bytecode(type_id: TypeId) -> Self {
        Self {
            bytecode: Some(type_id),
            inferred: None,
        }
    }

    fn from_inferred(type_id: TypeId) -> Self {
        Self {
            bytecode: None,
            inferred: Some(type_id),
        }
    }
}

/// Final symbol identities discovered while lifting one proto.
#[derive(Debug, Clone)]
pub struct FunctionSymbols {
    pub params: Vec<SymbolId>,
    pub upvalues: Vec<SymbolId>,
}

/// Type facts discovered or inferred for one lifted proto.
#[derive(Debug, Clone)]
pub struct FunctionTypes {
    symbol_types: HashMap<SymbolId, SymbolTypeFacts>,
    type_store: TypeStore,
}

impl FunctionTypes {
    fn from_facts(
        bytecode_symbol_types: HashMap<SymbolId, TypeId>,
        inferred_symbol_types: HashMap<SymbolId, TypeId>,
        type_store: TypeStore,
    ) -> Self {
        let mut symbol_types: HashMap<_, _> = bytecode_symbol_types
            .into_iter()
            .map(|(sym, type_id)| (sym, SymbolTypeFacts::from_bytecode(type_id)))
            .collect();

        for (sym, type_id) in inferred_symbol_types {
            symbol_types
                .entry(sym)
                .and_modify(|facts| facts.inferred = Some(type_id))
                .or_insert_with(|| SymbolTypeFacts::from_inferred(type_id));
        }

        Self {
            symbol_types,
            type_store,
        }
    }

    /// Returns the bytecode-provided type for a final HIL symbol.
    pub fn bytecode_symbol_type(&self, sym: SymbolId) -> Option<&Type> {
        self.symbol_types
            .get(&sym)
            .and_then(|facts| facts.bytecode)
            .and_then(|type_id| self.type_store.get(type_id))
    }

    /// Returns the best available type for a final HIL symbol.
    pub fn symbol_type(&self, sym: SymbolId) -> Option<&Type> {
        let bytecode = self.bytecode_symbol_type(sym);
        let inferred = self
            .symbol_types
            .get(&sym)
            .and_then(|facts| facts.inferred)
            .and_then(|type_id| self.type_store.get(type_id));

        match (bytecode, inferred) {
            (_, Some(inferred)) if inferred.is_meaningful() => Some(inferred),
            (Some(bytecode), _) if bytecode.is_meaningful() => Some(bytecode),
            (Some(bytecode), _) => Some(bytecode),
            (None, inferred) => inferred,
        }
    }

    /// Returns all currently known best symbol types.
    pub fn symbol_types(&self) -> impl Iterator<Item = (SymbolId, &Type)> + '_ {
        self.symbol_types.iter().filter_map(|(&sym, facts)| {
            let bytecode = facts
                .bytecode
                .and_then(|type_id| self.type_store.get(type_id));
            let inferred = facts
                .inferred
                .and_then(|type_id| self.type_store.get(type_id));

            match (bytecode, inferred) {
                (_, Some(inferred)) if inferred.is_meaningful() => Some((sym, inferred)),
                (Some(bytecode), _) if bytecode.is_meaningful() => Some((sym, bytecode)),
                (Some(bytecode), _) => Some((sym, bytecode)),
                (None, inferred) => inferred.map(|ty| (sym, ty)),
            }
        })
    }

    /// Records an inferred type for a final HIL symbol.
    pub fn set_inferred_symbol_type(&mut self, sym: SymbolId, ty: Type) {
        let type_id = self.type_store.alloc_unique(ty);
        self.symbol_types
            .entry(sym)
            .and_modify(|facts| facts.inferred = Some(type_id))
            .or_insert_with(|| SymbolTypeFacts::from_inferred(type_id));
    }
}

/// HIL control-flow output plus durable per-function metadata discovered while lifting.
#[derive(Debug, Clone)]
pub struct LiftedFunction {
    pub proto: ProtoId,
    pub debug_name: Option<String>,
    pub cfg: ControlFlowGraph,
    pub symbols: FunctionSymbols,
    pub types: FunctionTypes,
    pub is_vararg: bool,
}

impl LiftedFunction {
    pub fn from_proto(proto: &Proto, chunk: &Chunk, diagnostics: &Diagnostics) -> Result<Self> {
        let diagnostics = diagnostics.for_proto(proto.id.0);
        let info = diagnostics.at(LogLevel::Info, LogTarget::Hil);

        info.line(
            0,
            format_args!("{} params, {} upvalues", proto.num_params, proto.num_upvals),
        );

        info.line(1, format_args!("building cfg..."));
        let cfg::CfgBuild {
            cfg,
            params,
            upvalues,
            symbol_types,
            type_store,
        } = cfg::build_from_proto(proto, chunk)?;

        Ok(Self {
            proto: proto.id,
            debug_name: proto
                .debug_name
                .and_then(|id| chunk.get_string(id))
                .map(|s| s.to_string()),
            cfg,
            symbols: FunctionSymbols { params, upvalues },
            types: FunctionTypes::from_facts(symbol_types, HashMap::new(), type_store),
            is_vararg: proto.is_vararg,
        })
    }
}
