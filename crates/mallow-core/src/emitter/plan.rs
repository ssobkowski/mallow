use std::collections::{HashMap, HashSet};

use anyhow::{Result, bail};
use smol_str::SmolStr;

use super::name::{LocalNameCtx, LocalRole, LocalSource, Namer, Names};
use super::storage::Storage;
use crate::ast::Identifier;
use crate::hil::ir::CellId;
use crate::nir::visitor::Visitor;
use crate::nir::{self, LocalId, PackLocalId};

/// Maximum number of active Luau locals accepted by the compiler.
const SOURCE_LOCAL_LIMIT: usize = 200;

/// Identity of one binding that may need source storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum BindingKey {
    Local(LocalId),
    Cell(CellId),
    Pack(PackLocalId),
}

/// How one named binding enters its source scope.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Declaration {
    Syntax,
    Prefix,
    Inline(usize),
}

/// One binding assigned to its declaration scope.
struct BindingFact<'a> {
    key: BindingKey,
    role: LocalRole,
    value: Option<&'a nir::Expr>,
    declaration: Declaration,
    order: usize,
}

impl BindingFact<'_> {
    /// Returns whether Luau syntax requires this binding to be named.
    fn must_be_named(&self) -> bool {
        matches!(self.role, LocalRole::Parameter | LocalRole::LoopVariable)
    }

    /// Builds the context passed to the configured namer.
    fn name_context(&self) -> LocalNameCtx<'_> {
        LocalNameCtx {
            source: match self.key {
                BindingKey::Local(local) => LocalSource::Local(local),
                BindingKey::Cell(cell) => LocalSource::Cell(cell),
                BindingKey::Pack(pack) => LocalSource::Pack(pack),
            },
            role: self.role,
            value: self.value,
        }
    }
}

/// Bindings and ancestry of one source lexical scope.
struct ScopeFacts<'a> {
    parent: Option<usize>,
    bindings: Vec<BindingFact<'a>>,
}

/// Storage introduced at the start of one source scope.
#[derive(Default)]
pub(crate) struct ScopePlan {
    /// Spill table declared by the scope, when one is needed.
    pub(crate) spill_table: Option<Identifier>,
    /// Regular locals that must exist before the first statement.
    pub(crate) prefix_names: Vec<Identifier>,
}

/// Complete storage and naming plan for one NIR function.
pub(crate) struct FunctionPlan {
    locals: HashMap<LocalId, Storage>,
    cells: HashMap<CellId, Storage>,
    packs: HashMap<PackLocalId, Storage>,
    inline_declarations: HashMap<BindingKey, usize>,
    scopes: Vec<ScopePlan>,
    /// Identifier namespace retained for emitter-generated helper bindings.
    pub(crate) names: Names,
}

impl FunctionPlan {
    /// Plans every source binding and its declaration scope.
    pub(crate) fn build<N: Namer>(
        function: &nir::Function,
        inherited_cells: &HashMap<CellId, Storage>,
        spill_locals: bool,
        namer: &mut N,
    ) -> Result<Self> {
        let mut reserved = collect_globals(function);
        reserved.extend([
            SmolStr::new("_G"),
            SmolStr::new("select"),
            SmolStr::new("table"),
        ]);
        reserved.extend(
            inherited_cells
                .values()
                .map(|storage| storage.base_name().0.clone()),
        );
        let mut names = Names::new(reserved);
        let mut facts = BindingCollector::collect(function, inherited_cells);
        let mut locals = HashMap::new();
        let mut cells = inherited_cells.clone();
        let mut packs = HashMap::new();
        let mut inline_declarations = HashMap::new();
        let mut scopes = Vec::with_capacity(facts.len());
        let mut active_named = vec![0usize; facts.len()];

        for scope_index in 0..facts.len() {
            let inherited_count = facts[scope_index]
                .parent
                .map(|parent| active_named[parent])
                .unwrap_or_default();
            facts[scope_index]
                .bindings
                .sort_unstable_by_key(|binding| binding.order);
            let bindings = std::mem::take(&mut facts[scope_index].bindings);
            let mandatory_count = bindings
                .iter()
                .filter(|binding| binding.must_be_named())
                .count();
            let available = SOURCE_LOCAL_LIMIT.saturating_sub(inherited_count);
            if spill_locals && mandatory_count > available {
                bail!("mandatory locals exceed the Luau local limit");
            }

            let optional_count = bindings.len() - mandatory_count;
            let needs_spill = spill_locals && mandatory_count + optional_count > available;
            let optional_named = if needs_spill {
                available
                    .checked_sub(mandatory_count + 1)
                    .ok_or_else(|| anyhow::anyhow!("no local slot remains for a spill table"))?
            } else {
                optional_count
            };
            let spill_table = needs_spill.then(|| names.internal("values"));
            let mut remaining_optional_names = optional_named;
            let mut spill_index = 1usize;
            let mut prefix_names = Vec::new();

            for binding in bindings {
                let named = binding.must_be_named() || remaining_optional_names > 0;
                let storage = if named {
                    if !binding.must_be_named() {
                        remaining_optional_names -= 1;
                    }
                    let suggestion = namer.name(binding.name_context());
                    let name = names.claim(suggestion);
                    if binding.declaration == Declaration::Prefix {
                        prefix_names.push(name.clone());
                    }
                    Storage::Named(name)
                } else {
                    let table = spill_table
                        .as_ref()
                        .expect("spilled bindings require a spill table")
                        .clone();
                    let storage = Storage::Spilled {
                        table,
                        index: spill_index,
                    };
                    spill_index += 1;
                    storage
                };
                if let Declaration::Inline(scope) = binding.declaration {
                    inline_declarations.insert(binding.key, scope);
                }
                insert_storage(binding.key, storage, &mut locals, &mut cells, &mut packs);
            }

            active_named[scope_index] =
                inherited_count + mandatory_count + optional_named + usize::from(needs_spill);
            scopes.push(ScopePlan {
                spill_table,
                prefix_names,
            });
        }

        Ok(Self {
            locals,
            cells,
            packs,
            inline_declarations,
            scopes,
            names,
        })
    }

    /// Returns storage for one NIR local.
    pub(crate) fn local(&self, local: LocalId) -> Result<&Storage> {
        self.locals
            .get(&local)
            .ok_or_else(|| anyhow::anyhow!("missing source storage for local {}", local.index()))
    }

    /// Returns storage for one NIR cell.
    pub(crate) fn cell(&self, cell: CellId) -> Result<&Storage> {
        self.cells
            .get(&cell)
            .ok_or_else(|| anyhow::anyhow!("missing source storage for cell {}", cell.index()))
    }

    /// Returns storage for one materialized pack.
    pub(crate) fn pack(&self, pack: PackLocalId) -> Result<&Storage> {
        self.packs
            .get(&pack)
            .ok_or_else(|| anyhow::anyhow!("missing source storage for pack {}", pack.index()))
    }

    /// Claims one pending declaration in the given source scope.
    ///
    /// Returns whether the declaration was claimed.
    pub(crate) fn claim_declaration(&mut self, key: BindingKey, scope: usize) -> bool {
        if self.inline_declarations.get(&key) != Some(&scope) {
            return false;
        }
        self.inline_declarations.remove(&key);
        true
    }

    /// Returns the source plan for one lexical scope.
    pub(crate) fn scope(&self, scope: usize) -> Result<&ScopePlan> {
        self.scopes
            .get(scope)
            .ok_or_else(|| anyhow::anyhow!("missing source scope {scope}"))
    }
}

/// Stores one planned location in its identity map.
fn insert_storage(
    key: BindingKey,
    storage: Storage,
    locals: &mut HashMap<LocalId, Storage>,
    cells: &mut HashMap<CellId, Storage>,
    packs: &mut HashMap<PackLocalId, Storage>,
) {
    match key {
        BindingKey::Local(local) => {
            locals.insert(local, storage);
        }
        BindingKey::Cell(cell) => {
            cells.insert(cell, storage);
        }
        BindingKey::Pack(pack) => {
            packs.insert(pack, storage);
        }
    }
}

/// First source access observed for one binding.
#[derive(Clone, Copy)]
struct FirstAccess {
    scope: usize,
    is_write: bool,
}

/// Source facts accumulated for one binding identity.
struct BindingData<'a> {
    role: LocalRole,
    value: Option<&'a nir::Expr>,
    scope: usize,
    first: FirstAccess,
    order: usize,
}

/// Collects declaration scopes from every read and write.
struct BindingCollector<'a> {
    scopes: Vec<ScopeFacts<'a>>,
    bindings: HashMap<BindingKey, BindingData<'a>>,
    inherited_cells: &'a HashMap<CellId, Storage>,
    next_order: usize,
}

impl<'a> BindingCollector<'a> {
    /// Collects and groups all bindings by their common lexical scope.
    fn collect(
        function: &'a nir::Function,
        inherited_cells: &'a HashMap<CellId, Storage>,
    ) -> Vec<ScopeFacts<'a>> {
        let mut collector = Self {
            scopes: vec![ScopeFacts {
                parent: None,
                bindings: Vec::new(),
            }],
            bindings: HashMap::new(),
            inherited_cells,
            next_order: 0,
        };
        for &parameter in &function.params {
            collector.touch(
                BindingKey::Local(parameter),
                0,
                true,
                LocalRole::Parameter,
                None,
            );
        }
        collector.stmts(&function.prologue, 0);
        collector.region(&function.body, 0);

        for (key, data) in collector.bindings {
            let declaration = if matches!(data.role, LocalRole::Parameter | LocalRole::LoopVariable)
            {
                Declaration::Syntax
            } else if data.first.scope == data.scope && data.first.is_write {
                Declaration::Inline(data.scope)
            } else {
                Declaration::Prefix
            };
            collector.scopes[data.scope].bindings.push(BindingFact {
                key,
                role: data.role,
                value: data.value,
                declaration,
                order: data.order,
            });
        }
        collector.scopes
    }

    /// Records one source access and extends its declaration scope as needed.
    fn touch(
        &mut self,
        key: BindingKey,
        scope: usize,
        is_write: bool,
        role: LocalRole,
        value: Option<&'a nir::Expr>,
    ) {
        if matches!(key, BindingKey::Cell(cell) if self.inherited_cells.contains_key(&cell)) {
            return;
        }
        let order = self.next_order;
        self.next_order += 1;
        if let Some(data) = self.bindings.get_mut(&key) {
            data.scope = common_scope(&self.scopes, data.scope, scope);
            if role.priority() > data.role.priority() {
                data.role = role;
            }
            if data.value.is_none() {
                data.value = value;
            }
            return;
        }
        self.bindings.insert(
            key,
            BindingData {
                role,
                value,
                scope,
                first: FirstAccess { scope, is_write },
                order,
            },
        );
    }

    /// Adds one lexical child scope.
    fn push_scope(&mut self, parent: usize) -> usize {
        let scope = self.scopes.len();
        self.scopes.push(ScopeFacts {
            parent: Some(parent),
            bindings: Vec::new(),
        });
        scope
    }

    /// Visits one structured region with its source scope.
    fn region(&mut self, region: &'a nir::Region, scope: usize) {
        match region {
            nir::Region::Block { stmts, .. } => self.stmts(stmts, scope),
            nir::Region::Sequence(nodes) => {
                for node in nodes {
                    self.region(node, scope);
                }
            }
            nir::Region::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, scope);
                let then_scope = self.push_scope(scope);
                self.region(then_branch, then_scope);
                if let Some(else_branch) = else_branch {
                    let else_scope = self.push_scope(scope);
                    self.region(else_branch, else_scope);
                }
            }
            nir::Region::While { condition, body } => {
                self.expr(condition, scope);
                let body_scope = self.push_scope(scope);
                self.region(body, body_scope);
            }
            nir::Region::RepeatUntil { condition, body } => {
                let body_scope = self.push_scope(scope);
                self.region(body, body_scope);
                self.expr(condition, body_scope);
            }
            nir::Region::NumericFor {
                variable,
                start,
                end,
                step,
                body,
            } => {
                self.expr(start, scope);
                self.expr(end, scope);
                self.expr(step, scope);
                let body_scope = self.push_scope(scope);
                self.touch(
                    BindingKey::Local(*variable),
                    body_scope,
                    true,
                    LocalRole::LoopVariable,
                    None,
                );
                self.region(body, body_scope);
            }
            nir::Region::GenericFor {
                variables,
                values,
                body,
            } => {
                for value in values {
                    self.expr(value, scope);
                }
                let body_scope = self.push_scope(scope);
                for &variable in variables {
                    self.touch(
                        BindingKey::Local(variable),
                        body_scope,
                        true,
                        LocalRole::LoopVariable,
                        None,
                    );
                }
                self.region(body, body_scope);
            }
            nir::Region::Return(values) => self.pack_expr(values, scope),
            nir::Region::Continue | nir::Region::Break => {}
        }
    }

    /// Visits statements in source evaluation order.
    fn stmts(&mut self, stmts: &'a [nir::Stmt], scope: usize) {
        for stmt in stmts {
            match stmt {
                nir::Stmt::Bind { target, value, .. } => {
                    self.place(target, scope);
                    self.expr(value, scope);
                    match target {
                        nir::Place::Local(local) => self.touch(
                            BindingKey::Local(*local),
                            scope,
                            true,
                            LocalRole::Value,
                            Some(value),
                        ),
                        nir::Place::Cell(cell) => self.touch(
                            BindingKey::Cell(*cell),
                            scope,
                            true,
                            LocalRole::Cell,
                            Some(value),
                        ),
                        nir::Place::Global(_) | nir::Place::Table { .. } => {}
                        nir::Place::Discard => {}
                    }
                }
                nir::Stmt::BindMany { targets, values } => {
                    self.pack_expr(values, scope);
                    for target in targets {
                        if let nir::Place::Local(local) = target {
                            self.touch(
                                BindingKey::Local(*local),
                                scope,
                                true,
                                LocalRole::Value,
                                None,
                            );
                        }
                    }
                }
                nir::Stmt::BindPack { local, value } => {
                    self.pack_expr(value, scope);
                    self.touch(BindingKey::Pack(*local), scope, true, LocalRole::Pack, None);
                }
                nir::Stmt::Eval { value } => self.pack_expr(value, scope),
                nir::Stmt::OpenCell { cell, value, .. } => {
                    self.expr(value, scope);
                    self.touch(
                        BindingKey::Cell(*cell),
                        scope,
                        true,
                        LocalRole::Cell,
                        Some(value),
                    );
                }
                nir::Stmt::SetList { table, values, .. } => {
                    self.expr(table, scope);
                    self.pack_expr(values, scope);
                }
            }
        }
    }

    /// Visits one writable place.
    fn place(&mut self, place: &'a nir::Place, scope: usize) {
        if let nir::Place::Table { table, key } = place {
            self.expr(table, scope);
            self.expr(key, scope);
        }
    }

    /// Visits one scalar expression.
    fn expr(&mut self, expr: &'a nir::Expr, scope: usize) {
        match &expr.kind {
            nir::ExprKind::Local(local) => self.touch(
                BindingKey::Local(*local),
                scope,
                false,
                LocalRole::Value,
                None,
            ),
            nir::ExprKind::Closure { captures, .. } => {
                for capture in captures {
                    match capture {
                        nir::Capture::Copy(local) => self.touch(
                            BindingKey::Local(*local),
                            scope,
                            false,
                            LocalRole::Value,
                            None,
                        ),
                        nir::Capture::Share(cell) => {
                            self.touch(BindingKey::Cell(*cell), scope, false, LocalRole::Cell, None)
                        }
                    }
                }
            }
            nir::ExprKind::GetTable { table, key } => {
                self.expr(table, scope);
                self.expr(key, scope);
            }
            nir::ExprKind::Binary { lhs, rhs, .. } => {
                self.expr(lhs, scope);
                self.expr(rhs, scope);
            }
            nir::ExprKind::Unary { value, .. } => self.expr(value, scope),
            nir::ExprKind::Concat(values) => {
                for value in values {
                    self.expr(value, scope);
                }
            }
            nir::ExprKind::Select {
                condition,
                then_value,
                else_value,
            } => {
                self.expr(condition, scope);
                self.expr(then_value, scope);
                self.expr(else_value, scope);
            }
            nir::ExprKind::Project { pack, .. } => self.pack_expr(pack, scope),
            nir::ExprKind::LoadCell(cell) => {
                self.touch(BindingKey::Cell(*cell), scope, false, LocalRole::Cell, None)
            }
            nir::ExprKind::Constant(_) | nir::ExprKind::GetGlobal(_) | nir::ExprKind::NewTable => {}
        }
    }

    /// Visits one pack expression.
    fn pack_expr(&mut self, pack: &'a nir::PackExpr, scope: usize) {
        match &pack.kind {
            nir::PackExprKind::Local(local) => self.touch(
                BindingKey::Pack(*local),
                scope,
                false,
                LocalRole::Pack,
                None,
            ),
            nir::PackExprKind::Values { head, tail } => {
                for value in head {
                    self.expr(value, scope);
                }
                if let Some(tail) = tail {
                    self.pack_expr(tail, scope);
                }
            }
            nir::PackExprKind::Call { function, args } => {
                self.expr(function, scope);
                self.pack_expr(args, scope);
            }
            nir::PackExprKind::MethodCall { object, args, .. } => {
                self.expr(object, scope);
                self.pack_expr(args, scope);
            }
            nir::PackExprKind::VarArgs => {}
        }
    }
}

/// Returns the nearest source scope containing both inputs.
fn common_scope(scopes: &[ScopeFacts<'_>], mut lhs: usize, mut rhs: usize) -> usize {
    let mut lhs_ancestors = HashSet::new();
    loop {
        lhs_ancestors.insert(lhs);
        let Some(parent) = scopes[lhs].parent else {
            break;
        };
        lhs = parent;
    }
    loop {
        if lhs_ancestors.contains(&rhs) {
            return rhs;
        }
        rhs = scopes[rhs]
            .parent
            .expect("the root scope contains every binding");
    }
}

/// Collects global names that generated locals must not shadow.
fn collect_globals(function: &nir::Function) -> HashSet<SmolStr> {
    #[derive(Default)]
    struct GlobalCollector {
        names: HashSet<SmolStr>,
    }

    impl Visitor for GlobalCollector {
        fn visit_global(&mut self, name: &str) {
            self.names.insert(SmolStr::new(name));
        }
    }

    let mut collector = GlobalCollector::default();
    collector.visit_function(function);
    collector.names
}

#[cfg(test)]
mod tests {
    use id_arena::Arena;

    use super::*;
    use crate::ir::{Constant, Value};
    use crate::nir::{Expr, ExprKind, Function, Local, Place, Region, Stmt};

    /// Builds one flat function with the requested local count.
    fn flat_function(count: usize) -> Function {
        let mut values = Arena::<Value>::new();
        let mut locals = Arena::<Local>::new();
        let mut stmts = Vec::new();
        for _ in 0..count {
            let source = values.alloc(Value);
            let local = locals.alloc(Local { source });
            stmts.push(Stmt::Bind {
                origin: None,
                target: Place::Local(local),
                value: Expr {
                    origin: None,
                    kind: ExprKind::Constant(Constant::Nil),
                },
            });
        }
        Function {
            id: crate::il::ProtoId(0),
            locals,
            packs: Arena::new(),
            params: Vec::new(),
            is_vararg: false,
            upvalues: Vec::new(),
            prologue: Vec::new(),
            body: Region::Block { origin: 0, stmts },
        }
    }

    /// Scope planning leaves room for its spill table at the local limit.
    #[test]
    fn spills_excess_bindings_in_their_scope() {
        let function = flat_function(201);
        let mut namer = crate::emitter::name::PlainNamer;
        let plan = FunctionPlan::build(&function, &HashMap::new(), true, &mut namer).unwrap();

        assert!(plan.scope(0).unwrap().spill_table.is_some());
        let named = function
            .locals
            .iter()
            .filter(|(local, _)| plan.local(*local).unwrap().name().is_some())
            .count();
        assert_eq!(named, 199);
    }
}
