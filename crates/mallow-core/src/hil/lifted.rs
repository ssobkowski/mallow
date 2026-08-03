use std::collections::{BTreeMap, HashMap};

use anyhow::Result;

use crate::{
    Diagnostics, LogLevel, LogTarget,
    disasm::Chunk,
    hil::{
        cflow::{
            cfg::{self, BlockExit, ControlFlowGraph},
            union_find::UnionFind,
        },
        ir::{PhiNode, Stmt},
        lifter::ssa::{FunctionSymbols, SymbolId},
        ty2::{canonical::TypeId, canonical::TypeScheme, store::TypeStore},
        visitor::VisitorMut,
    },
    il::{Proto, ProtoId},
};

/// Stores bytecode and inferred type evidence for one HIL symbol identity.
#[derive(Debug, Clone)]
pub struct SymbolTypeFacts {
    /// Canonical graph node decoded from bytecode metadata, when present.
    bytecode: Option<TypeId>,
    /// Inferred graph-backed scheme, including any quantified binders.
    inferred: Option<TypeScheme>,
}

impl SymbolTypeFacts {
    /// Creates facts containing only bytecode-provided evidence.
    fn from_bytecode(type_id: TypeId) -> Self {
        Self {
            bytecode: Some(type_id),
            inferred: None,
        }
    }

    /// Creates facts containing only inferred scheme evidence.
    fn from_inferred(scheme: TypeScheme) -> Self {
        Self {
            bytecode: None,
            inferred: Some(scheme),
        }
    }
}

/// Type facts discovered or inferred for one lifted proto.
#[derive(Debug)]
pub struct FunctionTypes {
    symbol_types: HashMap<SymbolId, SymbolTypeFacts>,
    type_store: TypeStore,
}

impl Clone for FunctionTypes {
    /// Clones metadata into a fresh graph and remaps every stored graph ID.
    fn clone(&self) -> Self {
        let mut type_store = TypeStore::new();
        let symbol_types = self
            .symbol_types
            .iter()
            .map(|(symbol, facts)| {
                let bytecode = facts
                    .bytecode
                    .map(|id| type_store.import(&self.type_store, id));
                let inferred = facts
                    .inferred
                    .as_ref()
                    .map(|scheme| type_store.import_scheme(&self.type_store, scheme));

                (*symbol, SymbolTypeFacts { bytecode, inferred })
            })
            .collect();

        Self {
            symbol_types,
            type_store,
        }
    }
}

impl FunctionTypes {
    /// Combines bytecode and inferred facts in one durable canonical graph.
    fn from_facts(
        bytecode_symbol_types: HashMap<SymbolId, TypeId>,
        inferred_symbol_types: HashMap<SymbolId, TypeScheme>,
        type_store: TypeStore,
    ) -> Self {
        for type_id in bytecode_symbol_types.values() {
            assert!(
                !type_store.contains_generic(*type_id),
                "bytecode type facts must be monomorphic"
            );
        }
        let mut symbol_types: HashMap<_, _> = bytecode_symbol_types
            .into_iter()
            .map(|(sym, type_id)| (sym, SymbolTypeFacts::from_bytecode(type_id)))
            .collect();

        for (sym, scheme) in inferred_symbol_types {
            symbol_types
                .entry(sym)
                .and_modify(|facts| facts.inferred = Some(scheme.clone()))
                .or_insert_with(|| SymbolTypeFacts::from_inferred(scheme));
        }

        Self {
            symbol_types,
            type_store,
        }
    }

    /// Returns the bytecode-provided graph ID for one HIL symbol.
    pub fn bytecode_symbol_type(&self, sym: SymbolId) -> Option<TypeId> {
        self.symbol_types.get(&sym).and_then(|facts| facts.bytecode)
    }

    /// Returns only bytecode evidence, which is the monomorphic input allowed
    /// to seed a later inference run.
    ///
    /// Inferred facts remain schemes because their bodies may contain generic
    /// placeholders. Keeping this iterator tied to the bytecode field makes
    /// that provenance explicit instead of selecting a scheme body and
    /// accidentally treating it as a solver bound.
    pub fn monomorphic_symbol_types(&self) -> impl Iterator<Item = (SymbolId, TypeId)> + '_ {
        self.symbol_types
            .iter()
            .filter_map(|(&symbol, facts)| facts.bytecode.map(|type_id| (symbol, type_id)))
    }

    /// Returns the best available graph ID for one HIL symbol.
    pub fn symbol_type_id(&self, sym: SymbolId) -> Option<TypeId> {
        let bytecode = self.bytecode_symbol_type(sym);
        let inferred = self
            .symbol_types
            .get(&sym)
            .and_then(|facts| facts.inferred.as_ref())
            .map(TypeScheme::body)
            .filter(|id| self.type_store.is_meaningful(*id));

        match (bytecode, inferred) {
            (_, Some(inferred)) => Some(inferred),
            (Some(bytecode), _) if self.type_store.is_meaningful(bytecode) => Some(bytecode),
            (Some(bytecode), _) => Some(bytecode),
            (None, inferred) => inferred,
        }
    }

    /// Returns the inferred generic scheme for a symbol, when one exists.
    pub fn symbol_type_scheme(&self, sym: SymbolId) -> Option<&TypeScheme> {
        self.symbol_types
            .get(&sym)
            .and_then(|facts| facts.inferred.as_ref())
    }

    /// Returns all currently known best canonical graph IDs.
    pub fn symbol_type_ids(&self) -> impl Iterator<Item = (SymbolId, TypeId)> + '_ {
        self.symbol_types
            .keys()
            .copied()
            .filter_map(|sym| self.symbol_type_id(sym).map(|ty| (sym, ty)))
    }

    /// Re-keys facts after SSA versions have been coalesced for structuring.
    fn canonicalize_symbols(&mut self, disjoint_set: &mut UnionFind<SymbolId>) {
        let mut classes: BTreeMap<SymbolId, Vec<(SymbolId, SymbolTypeFacts)>> = BTreeMap::new();
        for (symbol, facts) in std::mem::take(&mut self.symbol_types) {
            classes
                .entry(disjoint_set.find(symbol))
                .or_default()
                .push((symbol, facts));
        }

        for (canonical, mut members) in classes {
            members.sort_by_key(|(symbol, _)| *symbol);
            let inferred = members
                .iter()
                .find(|(symbol, _)| *symbol == canonical)
                .and_then(|(_, facts)| facts.inferred.clone())
                .or_else(|| members.iter().find_map(|(_, facts)| facts.inferred.clone()));
            let bytecode = members
                .into_iter()
                .filter_map(|(_, facts)| facts.bytecode)
                .fold(None, |combined, type_id| {
                    Some(match combined {
                        Some(existing) => self.type_store.union(existing, type_id),
                        None => type_id,
                    })
                });

            self.symbol_types
                .insert(canonical, SymbolTypeFacts { bytecode, inferred });
        }
    }

    /// Records an inferred graph-backed scheme for one HIL symbol.
    pub fn set_inferred_symbol_type(&mut self, sym: SymbolId, scheme: TypeScheme) {
        // the body must exist
        let _ = self.type_store.get(scheme.body());

        self.symbol_types
            .entry(sym)
            .and_modify(|facts| facts.inferred = Some(scheme.clone()))
            .or_insert_with(|| SymbolTypeFacts::from_inferred(scheme));
    }

    /// Imports and records one inferred graph node produced by another store.
    pub fn import_inferred_symbol_type(
        &mut self,
        sym: SymbolId,
        source: &TypeStore,
        scheme: &TypeScheme,
    ) {
        let scheme = self.type_store.import_scheme(source, scheme);
        self.set_inferred_symbol_type(sym, scheme);
    }

    /// Returns the graph owned by this function's durable metadata.
    pub fn type_store(&self) -> &TypeStore {
        &self.type_store
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
            symbols,
            symbol_types,
            type_store,
        } = cfg::build_from_proto(proto, chunk)?;

        // Runtime check the SSA invariant that each symbol is defined at most once.
        // Debug only for development regressions.
        #[cfg(debug_assertions)]
        {
            use crate::hil::ir::Expr;
            use std::collections::HashSet;

            let mut symbols = HashSet::new();
            for stmt in cfg.blocks().flat_map(|b| b.stmts()) {
                match stmt {
                    Stmt::Assign {
                        left: Expr::Symbol(sym),
                        ..
                    } => {
                        debug_assert!(
                            symbols.insert(sym),
                            "SSA produced duplicate symbol definitions for {:?}",
                            sym
                        );
                    }
                    Stmt::AssignMany { left, .. } => {
                        for expr in left {
                            if let Expr::Symbol(sym) = expr {
                                debug_assert!(
                                    symbols.insert(sym),
                                    "SSA produced duplicate symbol definitions for {:?}",
                                    sym
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        Ok(Self {
            proto: proto.id,
            debug_name: proto
                .debug_name
                .and_then(|id| chunk.get_string(id))
                .and_then(|name| name.as_utf8().map(str::to_owned)),
            cfg,
            symbols,
            types: FunctionTypes::from_facts(symbol_types, HashMap::new(), type_store),
            is_vararg: proto.is_vararg,
        })
    }

    /// Coalesces SSA versions into the logical symbols expected by structuring.
    ///
    /// When enabled, whole-program inference must run before this method. The
    /// explicit Phi targets carry merged inferred schemes, while distinct
    /// versions of mutable storage are equated during constraint collection.
    pub(crate) fn destruct_ssa(&mut self) {
        let mut disjoint_set = UnionFind::new();
        for (target, source) in self.symbols.loop_carried_versions.drain(..) {
            disjoint_set.union(target, source);
        }

        union_phi_versions(&self.cfg, &mut disjoint_set);
        union_generic_for_versions(&self.cfg, &mut disjoint_set);
        union_version_groups(
            self.symbols
                .upvalue_version_groups
                .drain(..)
                .chain(self.symbols.captured_version_groups.drain(..))
                .map(|versions| versions.into_iter()),
            &mut disjoint_set,
        );

        for symbol in &mut self.symbols.params {
            *symbol = disjoint_set.find(*symbol);
        }
        for symbol in &mut self.symbols.upvalues {
            *symbol = disjoint_set.find(*symbol);
        }
        self.types.canonicalize_symbols(&mut disjoint_set);
        for local in &mut self.symbols.named_locals {
            for symbol in &mut local.symbols {
                *symbol = disjoint_set.find(*symbol);
            }
            local.symbols.sort();
            local.symbols.dedup();
        }

        let mut canonicalizer = SymbolCanonicalizer {
            disjoint_set: &mut disjoint_set,
        };
        for block in self.cfg.blocks_mut() {
            canonicalizer.visit_block(block);
        }
    }
}

/// Unions nontrivial Phi versions except source-level loop initializers.
fn union_phi_versions(cfg: &ControlFlowGraph, disjoint_set: &mut UnionFind<SymbolId>) {
    for (block_index, block) in cfg.blocks().enumerate() {
        for statement in block.stmts() {
            let Stmt::Phi(phi) = statement else {
                continue;
            };
            for &(predecessor, operand) in &phi.operands {
                if !is_loop_header_loop_var_operand(cfg, block_index, predecessor, phi.target) {
                    disjoint_set.union(phi.target, operand);
                }
            }
        }
    }
}

/// Unions generic-for loop versions that represent one source variable.
fn union_generic_for_versions(cfg: &ControlFlowGraph, disjoint_set: &mut UnionFind<SymbolId>) {
    for block in cfg.blocks() {
        let BlockExit::ForgPrep {
            exit_block,
            vars: entry_vars,
            ..
        } = block.exit()
        else {
            continue;
        };

        let BlockExit::ForgLoop {
            vars: body_vars, ..
        } = cfg.get(*exit_block).exit()
        else {
            continue;
        };

        // A body assignment creates a new SSA version of the loop variable.
        for (entry_var, body_var) in entry_vars.iter().zip(body_vars) {
            disjoint_set.union(*entry_var, *body_var);
        }
    }
}

/// Unions each nonempty version group into its first symbol.
fn union_version_groups<I, G>(groups: I, disjoint_set: &mut UnionFind<SymbolId>)
where
    I: IntoIterator<Item = G>,
    G: IntoIterator<Item = SymbolId>,
{
    for group in groups {
        let mut versions = group.into_iter();
        let Some(first) = versions.next() else {
            continue;
        };
        for version in versions {
            disjoint_set.union(first, version);
        }
    }
}

/// Returns whether an operand is the source-level initializer of a loop variable.
fn is_loop_header_loop_var_operand(
    cfg: &ControlFlowGraph,
    block_index: usize,
    predecessor: usize,
    target: SymbolId,
) -> bool {
    let predecessor = cfg.get(predecessor);

    match predecessor.exit() {
        BlockExit::FornPrep {
            body_block, var, ..
        } if *body_block == block_index => *var == target,
        BlockExit::ForgPrep {
            body_block, vars, ..
        } if *body_block == block_index => vars.contains(&target),
        _ => false,
    }
}

/// Visitor that rewrites every SSA reference to its coalesced logical symbol.
struct SymbolCanonicalizer<'a> {
    /// Equivalence classes produced by deferred SSA destruction.
    disjoint_set: &'a mut UnionFind<SymbolId>,
}

impl VisitorMut for SymbolCanonicalizer<'_> {
    /// Rewrites one ordinary symbol reference.
    fn visit_symbol(&mut self, symbol: &mut SymbolId) {
        *symbol = self.disjoint_set.find(*symbol);
    }

    /// Rewrites a closure capture owned by the enclosing function.
    fn visit_capture(&mut self, _index: usize, symbol: &mut SymbolId) {
        self.visit_symbol(symbol);
    }

    /// Rewrites both sides of a synthetic Phi statement.
    fn visit_phi(&mut self, phi: &mut PhiNode) {
        self.visit_symbol(&mut phi.target);
        for (_, operand) in &mut phi.operands {
            self.visit_symbol(operand);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, panic::AssertUnwindSafe};

    use id_arena::Arena;

    use super::FunctionTypes;
    use crate::hil::{
        cflow::union_find::UnionFind,
        lifter::ssa::Symbol,
        ty2::{canonical::Type, store::TypeStore},
    };

    /// Cloned metadata owns remapped IDs and rejects IDs from its source graph.
    #[test]
    fn function_types_clone_imports_facts_into_a_fresh_store() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let bytecode_symbol = symbols.alloc(Symbol::reg(0));
        let inferred_symbol = symbols.alloc(Symbol::reg(1));
        let mut type_store = TypeStore::new();
        let bytecode = type_store.named("BytecodeType");
        let generic = type_store.generic("T");
        let scheme = type_store.type_scheme(generic, vec!["T".into()]);
        let mut original = FunctionTypes::from_facts(
            HashMap::from([(bytecode_symbol, bytecode)]),
            HashMap::from([(inferred_symbol, scheme)]),
            type_store,
        );

        let mut cloned = original.clone();
        let cloned_bytecode = cloned.bytecode_symbol_type(bytecode_symbol).unwrap();
        let cloned_generic = cloned.symbol_type_scheme(inferred_symbol).unwrap().body();

        assert_ne!(bytecode, cloned_bytecode);
        assert_ne!(generic, cloned_generic);
        assert_eq!(
            original.type_store.get(bytecode),
            &Type::Named("BytecodeType".into())
        );
        assert_eq!(
            cloned.type_store.get(cloned_bytecode),
            &Type::Named("BytecodeType".into())
        );
        assert_eq!(
            original.type_store.get(generic),
            cloned.type_store.get(cloned_generic)
        );

        let source_only = original.type_store.named("SourceOnly");
        let clone_only = cloned.type_store.named("CloneOnly");
        assert!(
            std::panic::catch_unwind(AssertUnwindSafe(|| cloned.type_store.get(source_only)))
                .is_err()
        );
        assert!(
            std::panic::catch_unwind(AssertUnwindSafe(|| original.type_store.get(clone_only)))
                .is_err()
        );
    }

    /// Deferred coalescing keeps the Phi root's inferred scheme and merges
    /// monomorphic evidence from every member of its version class.
    #[test]
    fn canonicalized_facts_prefer_root_inference_and_merge_bytecode() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let target = symbols.alloc(Symbol::reg(0));
        let left = symbols.alloc(Symbol::reg(0));
        let right = symbols.alloc(Symbol::reg(0));
        let mut type_store = TypeStore::new();
        let number = type_store.primitives().number;
        let string = type_store.primitives().string;
        let target_type = type_store.named("PhiTarget");
        let operand_type = type_store.named("Operand");
        let target_scheme = type_store.type_scheme(target_type, Vec::new());
        let operand_scheme = type_store.type_scheme(operand_type, Vec::new());
        let mut facts = FunctionTypes::from_facts(
            HashMap::from([(left, number), (right, string)]),
            HashMap::from([
                (target, target_scheme),
                (left, operand_scheme.clone()),
                (right, operand_scheme),
            ]),
            type_store,
        );
        let mut disjoint_set = UnionFind::new();
        disjoint_set.union(target, left);
        disjoint_set.union(target, right);

        facts.canonicalize_symbols(&mut disjoint_set);

        assert_eq!(facts.symbol_types.len(), 1);
        assert_eq!(
            facts.symbol_type_scheme(target).unwrap().body(),
            target_type
        );
        let bytecode = facts.bytecode_symbol_type(target).unwrap();
        let Type::Union(members) = facts.type_store.get(bytecode) else {
            panic!("coalesced bytecode evidence must remain a union");
        };
        assert_eq!(members.len(), 2);
        assert!(members.contains(&number));
        assert!(members.contains(&string));
        assert!(facts.symbol_type_id(left).is_none());
        assert!(facts.symbol_type_id(right).is_none());
    }

    /// Repeated inference seeds only durable bytecode evidence, never a
    /// generic placeholder retained in an inferred scheme.
    #[test]
    fn monomorphic_seeds_exclude_inferred_generic_schemes() {
        let mut symbols: Arena<Symbol> = Arena::new();
        let bytecode_symbol = symbols.alloc(Symbol::reg(0));
        let inferred_only_symbol = symbols.alloc(Symbol::reg(1));

        let mut type_store = TypeStore::new();
        let bytecode = type_store.primitives().number;
        let generic = type_store.generic("T");
        let generic_scheme = type_store.type_scheme(generic, vec!["T".into()]);
        let facts = FunctionTypes::from_facts(
            HashMap::from([(bytecode_symbol, bytecode)]),
            HashMap::from([
                (bytecode_symbol, generic_scheme.clone()),
                (inferred_only_symbol, generic_scheme),
            ]),
            type_store,
        );

        assert_eq!(facts.symbol_type_id(bytecode_symbol), Some(generic));
        let seeds: Vec<_> = facts.monomorphic_symbol_types().collect();
        assert_eq!(seeds, vec![(bytecode_symbol, bytecode)]);
        assert!(
            seeds
                .iter()
                .all(|(_, type_id)| !facts.type_store.contains_generic(*type_id))
        );
        assert!(
            facts
                .symbol_type_scheme(bytecode_symbol)
                .is_some_and(|scheme| facts.type_store.contains_generic(scheme.body()))
        );
        assert!(
            facts
                .symbol_type_scheme(inferred_only_symbol)
                .is_some_and(|scheme| facts.type_store.contains_generic(scheme.body()))
        );
    }
}
