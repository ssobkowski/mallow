use std::collections::HashMap;

use smallvec::SmallVec;

use crate::ir::fir::ValueId;
use crate::ir::nir::visitor::{
    VisitorMut, walk_expr_mut, walk_pack_expr_mut, walk_region_mut, walk_stmts_mut,
};
use crate::ir::nir::{
    Capture, Expr, Function, LocalId, PackExpr, PackLocalId, Place, Region, Stmt, TableItem,
};
use crate::operator::BinOp;

/// Inlines scalar and pack locals in one function.
pub(super) fn run(function: &mut Function) -> bool {
    let replacements = {
        let def_use = DefUse::collect(function);
        def_use.replacements(function)
    };
    if replacements.is_empty() {
        return false;
    }

    let mut inliner = Inliner {
        changed: false,
        replacements,
    };
    inliner.visit_function(function);
    inliner.changed
}

/// One definition of a scalar symbol.
#[derive(Debug, Clone, Copy)]
enum LocalDefinition<'nir> {
    /// A scalar binding can be removed by this pass.
    Bind {
        /// Statement which owns the definition.
        statement: &'nir Stmt,
        /// Expression assigned to the symbol.
        value: &'nir Expr,
    },
    /// A definition which this pass cannot remove.
    Other,
}

/// One possible location for a moved expression.
#[derive(Debug, Clone, Copy)]
struct InlineSite<'nir> {
    /// Statement evaluated immediately before the use.
    previous: Option<&'nir Stmt>,
    /// Safety of the evaluation path before the use.
    safety: MoveSafety,
}

impl InlineSite<'_> {
    /// Returns whether the definition immediately precedes this site.
    #[inline]
    fn is_adjacent_to(&self, definition: &Stmt) -> bool {
        self.previous
            .is_some_and(|previous| std::ptr::eq(definition, previous))
    }

    /// Returns whether this site preserves a definition's evaluation point.
    #[inline]
    fn preserves(&self, definition: &Stmt) -> bool {
        self.safety == MoveSafety::Preserved && self.is_adjacent_to(definition)
    }
}

/// One use of a scalar symbol.
#[derive(Debug, Clone, Copy)]
enum LocalUse<'nir> {
    /// A scalar expression reads the symbol.
    Expression(InlineSite<'nir>),
    /// A closure captures the symbol.
    Capture,
}

/// Definitions and uses for one scalar symbol.
#[derive(Debug, Default)]
struct LocalChain<'nir> {
    /// Every definition of the symbol.
    definitions: SmallVec<[LocalDefinition<'nir>; 1]>,
    /// Every use of the symbol.
    uses: SmallVec<[LocalUse<'nir>; 2]>,
}

/// One definition of a pack symbol.
#[derive(Debug, Clone, Copy)]
struct PackDefinition<'nir> {
    /// Statement which owns the definition.
    statement: &'nir Stmt,
    /// Pack assigned to the symbol.
    value: &'nir PackExpr,
}

/// Definitions and uses for one pack symbol.
#[derive(Debug, Default)]
struct PackChain<'nir> {
    /// Every definition of the symbol.
    definitions: SmallVec<[PackDefinition<'nir>; 1]>,
    /// Every use of the symbol.
    uses: SmallVec<[InlineSite<'nir>; 2]>,
}

/// Safety of moving an expression through an evaluation prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MoveSafety {
    /// The use has no unstable or conditional prefix.
    Preserved,
    /// The use follows an unstable or conditional prefix.
    Changed,
}

impl MoveSafety {
    /// Accounts for an expression evaluated before the use.
    #[inline]
    fn after_expr(self, expr: &Expr) -> Self {
        if self == Self::Preserved && expr_is_stable_prefix(expr) {
            Self::Preserved
        } else {
            Self::Changed
        }
    }

    /// Accounts for a writable place evaluated before the use.
    #[inline]
    fn after_place(self, place: &Place) -> Self {
        if self == Self::Preserved && place_is_stable_prefix(place) {
            Self::Preserved
        } else {
            Self::Changed
        }
    }
}

/// Evaluation context shared by uses in one expression tree.
#[derive(Debug, Clone, Copy)]
struct UseContext<'nir> {
    /// Predecessor accepted for scalar uses.
    local_previous: Option<&'nir Stmt>,
    /// Predecessor accepted for pack uses.
    pack_previous: Option<&'nir Stmt>,
    /// Safety of expressions evaluated before the current node.
    safety: MoveSafety,
}

impl<'nir> UseContext<'nir> {
    /// Creates a context for a statement or `if` condition.
    #[inline]
    fn adjacent(previous: Option<&'nir Stmt>) -> Self {
        Self {
            local_previous: previous,
            pack_previous: previous,
            safety: MoveSafety::Preserved,
        }
    }

    /// Creates a context for return values.
    #[inline]
    fn return_values(previous: Option<&'nir Stmt>) -> Self {
        Self {
            local_previous: None,
            pack_previous: previous,
            safety: MoveSafety::Preserved,
        }
    }

    /// Creates a context which rejects moved effectful expressions.
    #[inline]
    const fn detached() -> Self {
        Self {
            local_previous: None,
            pack_previous: None,
            safety: MoveSafety::Preserved,
        }
    }

    /// Returns the inline site for a scalar use.
    #[inline]
    const fn local_site(self) -> InlineSite<'nir> {
        InlineSite {
            previous: self.local_previous,
            safety: self.safety,
        }
    }

    /// Returns the inline site for a pack use.
    #[inline]
    const fn pack_site(self) -> InlineSite<'nir> {
        InlineSite {
            previous: self.pack_previous,
            safety: self.safety,
        }
    }

    /// Accounts for an expression evaluated before the current node.
    #[inline]
    fn after_expr(mut self, expr: &Expr) -> Self {
        self.safety = self.safety.after_expr(expr);
        self
    }

    /// Accounts for a writable place evaluated before the current node.
    #[inline]
    fn after_place(mut self, place: &Place) -> Self {
        self.safety = self.safety.after_place(place);
        self
    }

    /// Marks the current node as conditionally evaluated.
    #[inline]
    fn conditional(mut self) -> Self {
        self.safety = MoveSafety::Changed;
        self
    }
}

/// Scalar and pack replacements owned by one rewrite.
#[derive(Debug, Default)]
struct Replacements {
    /// Scalar replacements indexed by local identity.
    locals: HashMap<LocalId, Expr>,
    /// Pack replacements indexed by pack-local identity.
    packs: HashMap<PackLocalId, PackExpr>,
}

impl Replacements {
    /// Returns whether no symbol can be replaced.
    #[inline]
    fn is_empty(&self) -> bool {
        self.locals.is_empty() && self.packs.is_empty()
    }
}

/// Def-use chains for one complete NIR function.
#[derive(Debug, Default)]
struct DefUse<'nir> {
    /// Chains indexed by scalar symbol identity.
    locals: HashMap<LocalId, LocalChain<'nir>>,
    /// Chains indexed by pack symbol identity.
    packs: HashMap<PackLocalId, PackChain<'nir>>,
    /// Number of scalar symbols for each underlying storage value.
    storage_symbol_counts: HashMap<ValueId, usize>,
}

impl<'nir> DefUse<'nir> {
    /// Collects def-use chains from one complete function.
    fn collect(function: &'nir Function) -> Self {
        let mut def_use = Self::default();

        for (local, data) in function.locals.iter() {
            def_use.locals.insert(local, LocalChain::default());
            *def_use
                .storage_symbol_counts
                .entry(data.source)
                .or_default() += 1;
        }
        for (pack, _) in function.packs.iter() {
            def_use.packs.insert(pack, PackChain::default());
        }
        for local in function.params.iter().copied() {
            def_use.def_local(local, LocalDefinition::Other);
        }

        def_use.collect_statements(&function.prologue);
        def_use.collect_region(&function.body);
        def_use
    }

    /// Builds conservative replacements without changing the function.
    ///
    /// Shared storage is excluded because it carries assignments which are not
    /// explicit symbol uses. Constants may move to any single expression use.
    /// Other scalar values and packs must have one adjacent use reached after
    /// only stable local or constant expressions.
    fn replacements(&self, function: &Function) -> Replacements {
        let mut replacements = Replacements::default();

        for (local, data) in function.locals.iter() {
            if self.storage_symbol_counts[&data.source] != 1 {
                continue;
            }

            let chain = &self.locals[&local];
            let [LocalDefinition::Bind { statement, value }] = chain.definitions.as_slice() else {
                continue;
            };
            let [LocalUse::Expression(site)] = chain.uses.as_slice() else {
                continue;
            };
            let can_move = match value {
                Expr::Constant(_) => true,
                Expr::Local(_) => site.is_adjacent_to(statement),
                _ => site.preserves(statement),
            };
            if !can_move {
                continue;
            }

            replacements.locals.insert(local, (*value).clone());
        }

        for (local, _) in function.packs.iter() {
            let chain = &self.packs[&local];
            let [definition] = chain.definitions.as_slice() else {
                continue;
            };
            let [site] = chain.uses.as_slice() else {
                continue;
            };
            if !site.preserves(definition.statement) {
                continue;
            }

            replacements.packs.insert(local, definition.value.clone());
        }

        replacements
    }

    /// Records one scalar symbol definition.
    #[inline]
    fn def_local(&mut self, local: LocalId, definition: LocalDefinition<'nir>) {
        self.locals
            .entry(local)
            .or_default()
            .definitions
            .push(definition);
    }

    /// Records one scalar symbol use.
    #[inline]
    fn use_local(&mut self, local: LocalId, symbol_use: LocalUse<'nir>) {
        self.locals.entry(local).or_default().uses.push(symbol_use);
    }

    /// Records one pack symbol definition.
    #[inline]
    fn def_pack(&mut self, pack: PackLocalId, definition: PackDefinition<'nir>) {
        self.packs
            .entry(pack)
            .or_default()
            .definitions
            .push(definition);
    }

    /// Records one pack symbol use.
    #[inline]
    fn use_pack(&mut self, pack: PackLocalId, site: InlineSite<'nir>) {
        self.packs.entry(pack).or_default().uses.push(site);
    }

    /// Collects definitions and uses from one region.
    #[inline]
    fn collect_region(&mut self, region: &'nir Region) {
        self.collect_region_after(region, None);
    }

    /// Collects one region with its immediate lexical predecessor.
    fn collect_region_after(&mut self, region: &'nir Region, previous: Option<&'nir Region>) {
        let previous_statement = match previous {
            Some(Region::Block { stmts, .. }) => stmts.last(),
            _ => None,
        };

        match region {
            Region::Block { stmts, .. } => self.collect_statements(stmts),
            Region::Sequence(nodes) => {
                let mut previous = None;
                for node in nodes {
                    self.collect_region_after(node, previous);
                    previous = Some(node);
                }
            }
            Region::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.collect_expr(condition, UseContext::adjacent(previous_statement));
                self.collect_region(then_branch);
                if let Some(else_branch) = else_branch {
                    self.collect_region(else_branch);
                }
            }
            Region::While { condition, body } => {
                self.collect_expr(condition, UseContext::detached());
                self.collect_region(body);
            }
            Region::RepeatUntil { condition, body } => {
                self.collect_region(body);
                self.collect_expr(condition, UseContext::detached());
            }
            Region::NumericFor {
                variable,
                start,
                end,
                step,
                body,
            } => {
                let context = UseContext::detached();
                self.collect_expr(start, context);
                self.collect_expr(end, context);
                self.collect_expr(step, context);
                self.def_local(*variable, LocalDefinition::Other);
                self.collect_region(body);
            }
            Region::GenericFor {
                variables,
                values,
                body,
            } => {
                for value in values {
                    self.collect_expr(value, UseContext::detached());
                }
                for variable in variables {
                    self.def_local(*variable, LocalDefinition::Other);
                }
                self.collect_region(body);
            }
            Region::Continue | Region::Break => {}
            Region::Return(values) => {
                self.collect_pack_expr(values, UseContext::return_values(previous_statement));
            }
        }
    }

    /// Collects definitions and uses from one statement list.
    fn collect_statements(&mut self, statements: &'nir [Stmt]) {
        let mut previous = None;
        for statement in statements {
            self.collect_statement(statement, previous);
            previous = Some(statement);
        }
    }

    /// Collects definitions and uses from one statement.
    fn collect_statement(&mut self, statement: &'nir Stmt, previous: Option<&'nir Stmt>) {
        let mut context = UseContext::adjacent(previous);
        match statement {
            Stmt::Bind { target, value, .. } => {
                self.collect_place(target, context);
                context = context.after_place(target);
                self.collect_expr(value, context);
                if let Place::Local(local) = target {
                    self.def_local(*local, LocalDefinition::Bind { statement, value });
                }
            }
            Stmt::BindMany { targets, values } => {
                for target in targets {
                    self.collect_place(target, context);
                    context = context.after_place(target);
                }
                self.collect_pack_expr(values, context);
                for target in targets {
                    if let Place::Local(local) = target {
                        self.def_local(*local, LocalDefinition::Other);
                    }
                }
            }
            Stmt::BindPack { local, value } => {
                self.collect_pack_expr(value, context);
                self.def_pack(*local, PackDefinition { statement, value });
            }
            Stmt::Eval { value } => self.collect_pack_expr(value, context),
            Stmt::OpenCell { value, .. } => self.collect_expr(value, context),
            Stmt::SetList { table, values, .. } => {
                self.collect_expr(table, context);
                self.collect_pack_expr(values, context.after_expr(table));
            }
        }
    }

    /// Collects scalar uses from one writable place.
    fn collect_place(&mut self, place: &'nir Place, context: UseContext<'nir>) {
        if let Place::Table { table, key } = place {
            self.collect_expr(table, context);
            self.collect_expr(key, context.after_expr(table));
        }
    }

    /// Collects scalar and pack uses from one scalar expression.
    fn collect_expr(&mut self, expr: &'nir Expr, context: UseContext<'nir>) {
        match expr {
            Expr::Local(local) => {
                self.use_local(*local, LocalUse::Expression(context.local_site()));
            }
            Expr::Constant(_) | Expr::GetGlobal(_) => {}
            Expr::Closure { captures, .. } => {
                for capture in captures {
                    if let Capture::Copy(local) = capture {
                        self.use_local(*local, LocalUse::Capture);
                    }
                }
            }
            Expr::GetTable { table, key } => {
                self.collect_expr(table, context);
                self.collect_expr(key, context.after_expr(table));
            }
            Expr::Binary { lhs, op, rhs } => {
                self.collect_expr(lhs, context);
                let rhs_context = if matches!(op, BinOp::And | BinOp::Or) {
                    context.conditional()
                } else {
                    context.after_expr(lhs)
                };
                self.collect_expr(rhs, rhs_context);
            }
            Expr::Unary { value, .. } => self.collect_expr(value, context),
            Expr::Concat(values) => {
                let mut context = context;
                for value in values {
                    self.collect_expr(value, context);
                    context = context.after_expr(value);
                }
            }
            Expr::Select {
                condition,
                then_value,
                else_value,
            } => {
                self.collect_expr(condition, context);
                let branch_context = context.conditional();
                self.collect_expr(then_value, branch_context);
                self.collect_expr(else_value, branch_context);
            }
            Expr::Table { items } => {
                for item in items {
                    match item {
                        TableItem::List(pack) => self.collect_pack_expr(pack, context),
                        TableItem::Index(key, value) => {
                            self.collect_expr(key, context);
                            self.collect_expr(value, context);
                        }
                    }
                }
            }
            Expr::Project { pack, .. } => self.collect_pack_expr(pack, context),
            Expr::LoadCell(_) => {}
        }
    }

    /// Collects scalar and pack uses from one pack expression.
    fn collect_pack_expr(&mut self, pack: &'nir PackExpr, context: UseContext<'nir>) {
        match pack {
            PackExpr::Local(local) => self.use_pack(*local, context.pack_site()),
            PackExpr::Values { head, tail } => {
                let mut context = context;
                for value in head {
                    self.collect_expr(value, context);
                    context = context.after_expr(value);
                }
                if let Some(tail) = tail {
                    self.collect_pack_expr(tail, context);
                }
            }
            PackExpr::Call { function, args } => {
                self.collect_expr(function, context);
                self.collect_pack_expr(args, context.after_expr(function));
            }
            PackExpr::MethodCall { object, args, .. } => {
                self.collect_expr(object, context);
                self.collect_pack_expr(args, context.after_expr(object));
            }
            PackExpr::VarArgs => {}
        }
    }
}

/// Returns whether evaluating a place before a replacement is always stable.
#[inline]
fn place_is_stable_prefix(place: &Place) -> bool {
    match place {
        Place::Local(_) | Place::Cell(_) | Place::Global(_) => true,
        Place::Table { table, key } => expr_is_stable_prefix(table) && expr_is_stable_prefix(key),
        Place::Discard => unreachable!("discards are never read"),
    }
}

/// Returns whether an expression is safe to evaluate before a moved value.
#[inline]
const fn expr_is_stable_prefix(expr: &Expr) -> bool {
    matches!(expr, Expr::Local(_) | Expr::Constant(_))
}

/// Applies scalar and pack replacements selected by one analysis.
struct Inliner {
    /// Whether this rewrite changed the function.
    changed: bool,
    /// Replacements selected before the rewrite.
    replacements: Replacements,
}

impl VisitorMut for Inliner {
    fn visit_region(&mut self, region: &mut Region) {
        // Run inlining first
        walk_region_mut(self, region);

        if let Region::Sequence(nodes) = region {
            nodes.retain(|node| !node.is_empty());
            if nodes.len() == 1 {
                *region = nodes.pop().expect("nodes is not empty");
            }
        }
    }

    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        let prev_len = stmts.len();
        stmts.retain(|stmt| match stmt {
            Stmt::Bind {
                target: Place::Local(local),
                ..
            } => !self.replacements.locals.contains_key(local),
            Stmt::BindPack { local, .. } => !self.replacements.packs.contains_key(local),
            _ => true,
        });
        self.changed |= stmts.len() != prev_len;

        walk_stmts_mut(self, stmts);
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        while let Expr::Local(local) = expr {
            let Some(replacement) = self.replacements.locals.get(local) else {
                break;
            };
            *expr = replacement.clone();
            self.changed = true;
        }

        walk_expr_mut(self, expr);
    }

    fn visit_pack_expr(&mut self, pack: &mut PackExpr) {
        while let PackExpr::Local(local) = pack {
            let Some(replacement) = self.replacements.packs.get(local) else {
                break;
            };
            *pack = replacement.clone();
            self.changed = true;
        }

        walk_pack_expr_mut(self, pack);
    }
}
