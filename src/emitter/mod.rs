mod collectors;
mod declarations;
mod locals;
mod name;
mod plan;
mod storage;

use std::collections::HashSet;

use smol_str::SmolStr;

use crate::{
    DecompileOptions, ast,
    common::is_valid_luau_identifier,
    emitter::{
        collectors::ReadCollector, declarations::DeclarationState, plan::FunctionPlan,
        storage::SymbolStorage,
    },
    hil::{
        StructuredFunction,
        cflow::region::RegionNode,
        ir as hil,
        lifter::ssa::SymbolId,
        ty::{FunctionTypeParam, FunctionTypeReturn, Type},
        visitor::Visitor,
    },
    il::ProtoId,
    logging::{Diagnostics, LogLevel, LogTarget},
    operator::{CompoundBinOp, UnOp},
};

const MAX_LOCAL_COUNT: usize = 199;

/// Extracts the return annotation expected by `local function` syntax.
///
/// Symbol facts for a local function name may contain the full structural
/// function type inferred for the closure. The AST node stores only the return
/// annotation, so multi-return or unknown signatures are left unannotated here
/// instead of printing the whole function type in return position.
fn local_function_return_type(ty: &Type) -> Option<Type> {
    let Type::Function { return_type, .. } = ty else {
        return (ty.is_meaningful() && !ty.contains_unknown()).then(|| ty.clone());
    };

    let [return_ty] = return_type.as_slice() else {
        return None;
    };

    let ty = match return_ty {
        FunctionTypeReturn::Type(ty) | FunctionTypeReturn::Vararg(ty) => ty,
    };

    (ty.is_meaningful() && !ty.contains_unknown()).then(|| ty.clone())
}

/// Collects generic names referenced by one emitted type annotation.
fn collect_generic_names(ty: &Type, names: &mut HashSet<SmolStr>) {
    match ty {
        Type::Generic(name) => {
            names.insert(name.clone());
        }
        Type::Table { fields, array } => {
            for field in fields.values() {
                collect_generic_names(field, names);
            }
            if let Some(array) = array {
                collect_generic_names(&array.0, names);
                collect_generic_names(&array.1, names);
            }
        }
        Type::Function {
            params,
            return_type,
            ..
        } => {
            for param in params {
                match param {
                    FunctionTypeParam::Type(ty) | FunctionTypeParam::Vararg(ty) => {
                        collect_generic_names(ty, names);
                    }
                }
            }
            for returned in return_type {
                match returned {
                    FunctionTypeReturn::Type(ty) | FunctionTypeReturn::Vararg(ty) => {
                        collect_generic_names(ty, names);
                    }
                }
            }
        }
        Type::Union(types) | Type::Intersection(types) => {
            for ty in types {
                collect_generic_names(ty, names);
            }
        }
        Type::WithMetatable { base, metatable } => {
            collect_generic_names(base, names);
            for (_, method) in metatable.iter() {
                collect_generic_names(method, names);
            }
        }
        _ => {}
    }
}

#[derive(Default)]
struct AssignCollector {
    symbols: HashSet<SymbolId>,
}

impl AssignCollector {
    fn collect_assigned_symbols(node: &RegionNode) -> HashSet<SymbolId> {
        let mut collector = AssignCollector::default();
        collector.visit_region(node);
        collector.symbols
    }
}

impl Visitor for AssignCollector {
    fn visit_stmt(&mut self, stmt: &hil::Stmt) {
        match stmt {
            hil::Stmt::Assign {
                left: hil::Expr::Symbol(sym),
                ..
            } => {
                self.symbols.insert(*sym);
            }
            hil::Stmt::AssignMany { left, .. } => {
                self.symbols.extend(left.iter().filter_map(|lv| {
                    if let hil::Expr::Symbol(s) = lv {
                        Some(*s)
                    } else {
                        None
                    }
                }));
            }
            _ => {}
        }
    }
}

struct FunctionContext {
    proto_idx: usize,
    plan: FunctionPlan,
    anomalies: Vec<String>,
}

struct AssignManyTarget {
    storage: SymbolStorage,
    slot_was_declared: bool,
}

struct Emitter<'a> {
    functions: Vec<StructuredFunction>,
    entry: usize,
    options: DecompileOptions,
    diagnostics: &'a Diagnostics,

    declarations: DeclarationState,
    contexts: Vec<FunctionContext>,
    current_ctx: usize,
}

impl Emitter<'_> {
    fn visit_entry(&mut self) -> ast::Block {
        let entry_ctx = self.create_context(self.entry);
        self.visit_function(entry_ctx)
    }

    fn create_context(&mut self, proto_idx: usize) -> usize {
        let ctx = FunctionContext {
            proto_idx,
            plan: FunctionPlan::new(&self.functions[proto_idx]),
            anomalies: Vec::new(),
        };
        self.contexts.push(ctx);
        self.contexts.len() - 1
    }

    fn current_proto_idx(&self) -> usize {
        self.contexts[self.current_ctx].proto_idx
    }

    fn visit_function(&mut self, ctx_idx: usize) -> ast::Block {
        let old_ctx = self.current_ctx;
        self.current_ctx = ctx_idx;

        let proto_idx = self.current_proto_idx();
        let fun = self.functions[proto_idx].clone();

        self.declarations.push_scope();
        for &sym in &fun.symbols.params {
            let slot = self.declare_symbol(sym);
            self.bind_slot_to_symbol_name(slot, sym);
            self.declare_slot(slot);
        }
        for &sym in &fun.symbols.upvalues {
            let slot = self.declare_symbol(sym);
            self.bind_slot_to_symbol_name(slot, sym);
            self.declare_slot(slot);
        }

        let upvalue_str = fun
            .symbols
            .upvalues
            .iter()
            .map(|u| self.get_symbol_name(u).0)
            .collect::<Vec<_>>()
            .join(", ");
        let mut block = if self.entry != proto_idx {
            ast::Block::with_stmts(vec![ast::Stmt::Comment {
                text: format!("proto {}: upvalues = [{}]", proto_idx, upvalue_str),
            }])
        } else {
            ast::Block::with_stmts(Vec::new())
        };
        block.stmts.extend(self.visit_region(&fun.root).stmts);
        for (idx, anomaly) in self.contexts[self.current_ctx].anomalies.iter().enumerate() {
            block.stmts.insert(
                idx + 1,
                ast::Stmt::Comment {
                    text: format!("anomaly: {anomaly}"),
                },
            );
        }
        if let Some(table) = self.contexts[self.current_ctx].plan.spill_table() {
            block.stmts.insert(
                1 + self.contexts[self.current_ctx].anomalies.len(),
                ast::Stmt::LocalDeclaration {
                    names: vec![ast::Typed::untyped(table)],
                    values: vec![ast::Expr::Table { items: Vec::new() }],
                },
            );
        }
        self.dump_symbol_names(ctx_idx, proto_idx);

        self.declarations.pop_scope();

        self.current_ctx = old_ctx;
        block
    }

    fn get_symbol_name(&mut self, sym: &SymbolId) -> ast::Identifier {
        self.get_symbol_name_for(self.current_ctx, *sym)
    }

    fn get_symbol_name_for(&mut self, ctx_idx: usize, sym: SymbolId) -> ast::Identifier {
        let proto_idx = self.contexts[ctx_idx].proto_idx;
        let is_param = self.functions[proto_idx].symbols.params.contains(&sym);
        self.contexts[ctx_idx].plan.get_symbol_name(sym, is_param)
    }

    fn typed_identifier_for(
        &self,
        proto_idx: usize,
        sym: SymbolId,
        name: ast::Identifier,
    ) -> ast::Typed<ast::Identifier> {
        if let Some(ty) = self.functions[proto_idx]
            .symbol_type(sym)
            .filter(|ty| ty.is_meaningful() && !ty.contains_unknown())
            .cloned()
        {
            ast::Typed::new(name, ty)
        } else {
            ast::Typed::untyped(name)
        }
    }

    fn typed_identifier(
        &self,
        sym: SymbolId,
        name: ast::Identifier,
    ) -> ast::Typed<ast::Identifier> {
        self.typed_identifier_for(self.current_proto_idx(), sym, name)
    }

    fn typed_parameter_for(
        &self,
        proto_idx: usize,
        sym: SymbolId,
        parameter: ast::Parameter,
    ) -> ast::Typed<ast::Parameter> {
        if let Some(ty) = self.functions[proto_idx]
            .symbol_type(sym)
            .filter(|ty| ty.is_meaningful() && !ty.contains_unknown())
            .cloned()
        {
            ast::Typed::new(parameter, ty)
        } else {
            ast::Typed::untyped(parameter)
        }
    }

    fn bind_slot_to_symbol_name(&mut self, slot: usize, sym: SymbolId) {
        let proto_idx = self.current_context().proto_idx;
        let is_param = self.functions[proto_idx].symbols.params.contains(&sym);
        self.current_context_mut()
            .plan
            .bind_slot_to_symbol_name(slot, sym, is_param);
    }

    fn current_context(&self) -> &FunctionContext {
        &self.contexts[self.current_ctx]
    }

    fn current_context_mut(&mut self) -> &mut FunctionContext {
        &mut self.contexts[self.current_ctx]
    }

    /// Dumps the final SymbolId-to-emitted-name map for one function context.
    fn dump_symbol_names(&self, ctx_idx: usize, proto_idx: usize) {
        let diagnostics = self.diagnostics.for_proto(proto_idx as u16);
        let sink = diagnostics.at(LogLevel::Debug, LogTarget::Emitter);
        sink.block("symbol names:", |sink| {
            for (sym, name) in self.contexts[ctx_idx].plan.emitted_name_map() {
                sink.line(
                    1,
                    format_args!("SymbolId({}) -> {}", sym.index(), name.as_str()),
                );
            }
        });
    }

    fn fresh_temp_local(&mut self) -> ast::Identifier {
        self.current_context_mut().plan.fresh_temp_local()
    }

    fn declare_symbol_slot(&mut self, sym: SymbolId) -> usize {
        self.current_context_mut().plan.symbol_slot(sym)
    }

    fn declare_symbol(&mut self, sym: SymbolId) -> usize {
        let slot = self.declare_symbol_slot(sym);
        self.declarations.declare_symbol(sym, slot);
        slot
    }

    fn declare_slot(&mut self, slot: usize) {
        self.declarations.declare_slot(slot);
    }

    fn prepare_assign_many_targets(&mut self, symbols: Vec<SymbolId>) -> Vec<AssignManyTarget> {
        for &sym in &symbols {
            if !self.declarations.contains_symbol(&sym) {
                self.declare_symbol(sym);
            }
        }

        let mut targets = Vec::with_capacity(symbols.len());
        for symbol in symbols {
            let storage = self
                .symbol_storage(symbol)
                .expect("assign-many symbols must exist in scope");
            let slot = self
                .declarations
                .symbol_slot(&symbol)
                .expect("assign-many symbols must exist in scope");
            let slot_was_declared = self.declarations.contains_slot(slot);
            if !slot_was_declared {
                self.declare_slot(slot);
            }

            targets.push(AssignManyTarget {
                storage,
                slot_was_declared,
            });
        }

        targets
    }

    fn symbol_storage(&mut self, sym: SymbolId) -> Option<SymbolStorage> {
        if let Some(storage) = self.current_context().plan.inherited_storage(sym) {
            return Some(storage);
        }

        let idx = self.declarations.symbol_slot(&sym)?;
        let spill_locals = self.options.spill_locals;
        Some(
            self.current_context_mut()
                .plan
                .storage_for(sym, idx, spill_locals, MAX_LOCAL_COUNT),
        )
    }

    fn symbol_expr(&mut self, sym: SymbolId) -> ast::Expr {
        match self.symbol_storage(sym) {
            Some(storage) => storage.into_expr(),
            None => {
                let name = self.get_symbol_name(&sym);
                let proto_idx = self.current_proto_idx();
                self.record_anomaly(format!(
                    "undeclared symbol read during structuring: proto={}, symbol={}, emitted as {}",
                    proto_idx,
                    sym.index(),
                    name.as_str()
                ));
                ast::Expr::Named(name)
            }
        }
    }

    fn record_anomaly(&mut self, message: String) {
        let anomalies = &mut self.contexts[self.current_ctx].anomalies;
        if !anomalies.contains(&message) {
            anomalies.push(message);
        }
    }

    fn visit_region(&mut self, region: &RegionNode) -> ast::Block {
        let mut stmts = Vec::new();
        self.visit_node(region, &mut stmts);
        ast::Block::with_stmts(stmts)
    }

    /// Visits a flat sequence of region nodes, giving each `If` node access to its
    /// continuation so that only symbols genuinely needed after the branch are hoisted.
    fn visit_sequence(&mut self, nodes: &[RegionNode], buf: &mut Vec<ast::Stmt>) {
        for (i, node) in nodes.iter().enumerate() {
            if let RegionNode::If {
                condition,
                then_branch,
                else_branch,
                ..
            } = node
            {
                let continuation = &nodes[i + 1..];
                self.visit_if_node(
                    condition,
                    then_branch,
                    else_branch.as_deref(),
                    continuation,
                    buf,
                );
            } else {
                self.visit_node(node, buf);
            }
        }
    }

    /// Emits an `if`/`else` statement, hoisting symbols that are assigned in both
    /// branches *and* actually read in `continuation` (the remaining nodes that follow
    /// this `if` in the enclosing sequence).
    fn visit_if_node(
        &mut self,
        condition: &hil::Expr,
        then_branch: &RegionNode,
        else_branch: Option<&RegionNode>,
        continuation: &[RegionNode],
        buf: &mut Vec<ast::Stmt>,
    ) {
        let then_assigned = AssignCollector::collect_assigned_symbols(then_branch);

        let else_assigned = else_branch
            .map(AssignCollector::collect_assigned_symbols)
            .unwrap_or_default();

        // A symbol needs to be hoisted only when it is assigned in *both* branches
        // (so it is live on all paths after the if) *and* is actually read somewhere
        // in the continuation.  Symbols that are dead after the if stay local to their
        // branch, which gives downstream HIL passes more room to fold them.
        let continuation_reads = ReadCollector::in_region(continuation);

        let mut hoisted: Vec<_> = then_assigned
            .intersection(&else_assigned)
            .copied()
            .filter(|sym| !self.declarations.contains_symbol(sym))
            .filter(|sym| continuation.is_empty() || continuation_reads.contains(sym))
            .collect();
        hoisted.sort_by_key(|sym| sym.index());

        if !hoisted.is_empty() {
            for sym in &hoisted {
                let slot = self.declare_symbol(*sym);
                self.declare_slot(slot);
            }

            let names: Vec<_> = hoisted
                .iter()
                .filter_map(|sym| match self.symbol_storage(*sym) {
                    Some(SymbolStorage::Named(name)) => Some(self.typed_identifier(*sym, name)),
                    Some(SymbolStorage::Spilled(_)) | None => None,
                })
                .collect();
            if !names.is_empty() {
                buf.push(ast::Stmt::LocalDeclaration {
                    names,
                    values: Vec::new(),
                });
            }
        }

        self.declarations.push_scope();
        let then_body = self.visit_region(then_branch);
        self.declarations.pop_scope();

        let else_clause = else_branch.map(|e| {
            self.declarations.push_scope();
            let region = self.visit_region(e);
            self.declarations.pop_scope();

            // if the region is only one If statement we can fold into an elseif
            if let [ast::Stmt::If(elseif)] = region.stmts.as_slice() {
                return ast::ElseClause::If(Box::new(elseif.clone()));
            }

            ast::ElseClause::Else(region)
        });

        buf.push(ast::Stmt::If(ast::If {
            condition: self.visit_expr(condition),
            then_body,
            else_clause,
        }));
    }

    fn visit_node(&mut self, node: &RegionNode, buf: &mut Vec<ast::Stmt>) {
        match node {
            RegionNode::BasicBlock { stmts } => self.visit_block(stmts, buf),
            RegionNode::Sequence { nodes } => self.visit_sequence(nodes, buf),
            RegionNode::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                // No continuation is known when visiting a bare If node outside of a
                // Sequence. Pass an empty slice so the hoist filter falls back to the
                // conservative behaviour of hoisting anything assigned in both branches.
                self.visit_if_node(condition, then_branch, else_branch.as_deref(), &[], buf);
            }
            RegionNode::While {
                condition, body, ..
            } => {
                self.declarations.push_scope();

                let body = self.visit_region(body);
                buf.push(ast::Stmt::While {
                    condition: self.visit_expr(condition),
                    body,
                });

                self.declarations.pop_scope();
            }
            RegionNode::RepeatUntil { condition, body } => {
                self.declarations.push_scope();

                let body = self.visit_region(body);
                buf.push(ast::Stmt::RepeatUntil {
                    condition: self.visit_expr(condition),
                    body,
                });

                self.declarations.pop_scope();
            }
            RegionNode::NumericFor {
                body,
                var,
                start,
                end,
                step,
                ..
            } => {
                self.declarations.push_scope();

                let slot = self.declare_symbol(*var);
                self.bind_slot_to_symbol_name(slot, *var);
                self.declare_slot(slot);
                self.current_context_mut().plan.force_named_symbol(*var);
                let var = match self.symbol_storage(*var).unwrap().into_expr() {
                    ast::Expr::Named(name) => name,
                    _ => unreachable!("numeric-for variables cannot be spilled"),
                };
                let start = self.visit_expr(start);
                let end = self.visit_expr(end);
                let step = Some(self.visit_expr(step));

                let body = self.visit_region(body);
                buf.push(ast::Stmt::NumericFor {
                    var,
                    start,
                    end,
                    step,
                    body,
                });

                self.declarations.pop_scope();
            }
            RegionNode::GenericFor {
                vars, exprs, body, ..
            } => {
                self.declarations.push_scope();

                for &var in vars {
                    let slot = self.declare_symbol(var);
                    self.bind_slot_to_symbol_name(slot, var);
                    self.declare_slot(slot);
                    self.current_context_mut().plan.force_named_symbol(var);
                }
                let vars = vars
                    .iter()
                    .map(|s| match self.symbol_storage(*s).unwrap().into_expr() {
                        ast::Expr::Named(name) => name,
                        _ => unreachable!("generic-for variables cannot be spilled"),
                    })
                    .collect();
                let exprs = exprs.iter().map(|expr| self.visit_expr(expr)).collect();
                let body = self.visit_region(body);
                buf.push(ast::Stmt::GenericFor { vars, exprs, body });

                self.declarations.pop_scope();
            }
            RegionNode::Continue => buf.push(ast::Stmt::Continue),
            RegionNode::Break => buf.push(ast::Stmt::Break),
            RegionNode::Return { values } => {
                buf.push(ast::Stmt::Return {
                    values: values.iter().map(|expr| self.visit_expr(expr)).collect(),
                });
            }
        }
    }

    fn visit_block(&mut self, stmts: &[hil::Stmt], buf: &mut Vec<ast::Stmt>) {
        for stmt in stmts {
            self.maybe_predeclare_recursive_local(stmt, buf);
            self.visit_stmt(stmt, buf);
        }
    }

    fn maybe_predeclare_recursive_local(&mut self, stmt: &hil::Stmt, buf: &mut Vec<ast::Stmt>) {
        let hil::Stmt::Assign {
            left: hil::Expr::Symbol(sym),
            value: hil::Expr::Closure { proto, captures },
        } = stmt
        else {
            return;
        };

        if self.declarations.contains_symbol(sym) || !captures.iter().any(|capture| capture == sym)
        {
            return;
        }

        // If the closure has a debug_name, visit_stmt will emit a LocalFunction
        // which natively handles recursion in Luau.
        if self.functions[proto.0 as usize].debug_name.is_some() {
            return;
        }

        let slot = self.declare_symbol(*sym);
        self.declare_slot(slot);
        if let Some(SymbolStorage::Named(name)) = self.symbol_storage(*sym) {
            buf.push(ast::Stmt::LocalDeclaration {
                names: vec![self.typed_identifier(*sym, name)],
                values: Vec::new(),
            });
        }
    }

    fn visit_stmt(&mut self, stmt: &hil::Stmt, buf: &mut Vec<ast::Stmt>) {
        match stmt {
            hil::Stmt::Assign { left, value } => {
                let mut needs_declaration = false;
                let mut named_closure = false;

                let left_expr = match left {
                    hil::Expr::Symbol(sym) => {
                        if !self.declarations.contains_symbol(sym) {
                            // If value is a named closure, reserve its debug_name
                            // as the symbol name before declaring/symbol_expr.
                            if let hil::Expr::Closure { proto, .. } = value {
                                let debug_name =
                                    self.functions[proto.0 as usize].debug_name.clone();
                                if let Some(name) = debug_name {
                                    self.current_context_mut()
                                        .plan
                                        .reserve_symbol_name_exact(*sym, name.into());
                                    named_closure = true;
                                }
                            }
                            let slot = self.declare_symbol(*sym);
                            needs_declaration = !self.declarations.contains_slot(slot);
                            if needs_declaration {
                                self.declare_slot(slot);
                            }
                        }
                        self.symbol_expr(*sym)
                    }
                    _ => self.visit_expr(left),
                };
                let right = match value {
                    hil::Expr::Closure { proto, captures } => self.visit_closure(*proto, captures),
                    _ => self.visit_expr(value),
                };

                if needs_declaration {
                    let hil::Expr::Symbol(sym) = left else {
                        unreachable!("non-symbol lvalues are never declarations");
                    };

                    if named_closure
                        && let Some(SymbolStorage::Named(name)) = self.symbol_storage(*sym)
                        && let ast::Expr::AnonymousFunction {
                            generics,
                            params,
                            body,
                        } = right
                    {
                        buf.push(ast::Stmt::LocalFunction {
                            name,
                            generics,
                            params,
                            body,
                            ty: self.functions[self.current_proto_idx()]
                                .symbol_type(*sym)
                                .and_then(local_function_return_type),
                        });
                        return;
                    }

                    match self
                        .symbol_storage(*sym)
                        .expect("symbol was just declared in scope")
                    {
                        SymbolStorage::Named(name) => {
                            buf.push(ast::Stmt::LocalDeclaration {
                                names: vec![ast::Typed::untyped(name)],
                                values: vec![right],
                            });
                        }
                        SymbolStorage::Spilled(_) => buf.push(ast::Stmt::Assignment {
                            lhs: vec![left_expr],
                            rhs: vec![right],
                        }),
                    }
                } else {
                    if let ast::Expr::Binary { lhs, op, rhs } = &right
                        && left.is_pure()
                        && lhs.as_ref() == &left_expr
                        && let Ok(compound_op) = CompoundBinOp::try_from(*op)
                    {
                        buf.push(ast::Stmt::CompoundAssignment {
                            lhs: left_expr,
                            op: compound_op,
                            rhs: rhs.as_ref().clone(),
                        });
                        return;
                    }

                    buf.push(ast::Stmt::Assignment {
                        lhs: vec![left_expr],
                        rhs: vec![right],
                    });
                }
            }
            hil::Stmt::AssignMany { left, value } => {
                let right = self.visit_expr(value);
                if left
                    .iter()
                    .any(|lvalue| !matches!(lvalue, hil::Expr::Symbol(_)))
                {
                    let lhs = left.iter().map(|lvalue| self.visit_expr(lvalue)).collect();
                    buf.push(ast::Stmt::Assignment {
                        lhs,
                        rhs: vec![right],
                    });
                    return;
                }

                let symbols: Vec<_> = left
                    .iter()
                    .map(|lvalue| {
                        let hil::Expr::Symbol(sym) = lvalue else {
                            unreachable!("guarded by symbol-only branch")
                        };
                        *sym
                    })
                    .collect();

                let targets = self.prepare_assign_many_targets(symbols);

                let all_declared = targets.iter().all(|target| target.slot_was_declared);
                if all_declared {
                    buf.push(ast::Stmt::Assignment {
                        lhs: targets
                            .into_iter()
                            .map(|target| target.storage.into_expr())
                            .collect(),
                        rhs: vec![right],
                    });
                    return;
                }

                let all_named = targets
                    .iter()
                    .all(|target| matches!(target.storage, SymbolStorage::Named(_)));
                if all_named {
                    let names = targets
                        .into_iter()
                        .map(|target| match target.storage {
                            SymbolStorage::Named(name) => ast::Typed::untyped(name),
                            SymbolStorage::Spilled(_) => unreachable!("guarded by all_named"),
                        })
                        .collect();
                    buf.push(ast::Stmt::LocalDeclaration {
                        names,
                        values: vec![right],
                    });
                    return;
                }

                let temps: Vec<_> = (0..targets.len())
                    .map(|_| ast::Typed::untyped(self.fresh_temp_local()))
                    .collect();
                buf.push(ast::Stmt::LocalDeclaration {
                    names: temps.clone(),
                    values: vec![right],
                });

                for (target, temp) in targets.into_iter().zip(temps) {
                    let rhs = vec![ast::Expr::Named(temp.as_ref().clone())];
                    match (target.storage, target.slot_was_declared) {
                        (SymbolStorage::Named(name), false) => {
                            buf.push(ast::Stmt::LocalDeclaration {
                                names: vec![ast::Typed::untyped(name)],
                                values: rhs,
                            });
                        }
                        (storage, true) | (storage @ SymbolStorage::Spilled(_), false) => {
                            buf.push(ast::Stmt::Assignment {
                                lhs: vec![storage.into_expr()],
                                rhs,
                            });
                        }
                    }
                }
            }
            hil::Stmt::SetList {
                table,
                index,
                values,
                has_variadic_tail,
            } => {
                let table_expr = self.visit_expr(&hil::Expr::Symbol(*table));
                if *has_variadic_tail {
                    // The idea is that if we have a variadic tail, we can't simply assign
                    // a tuple to a single index (t[k] = a, b)
                    //
                    // We create a temporary table and then copy the contents of it into the
                    // true table with `table.move`
                    //
                    // This should run only if the 'fold_tables' pass did not fold this SetList
                    // into table constructor.

                    let temp_table_ident = ast::Identifier::new("__t");
                    buf.push(ast::Stmt::Do {
                        body: ast::Block::with_stmts(vec![
                            ast::Stmt::LocalDeclaration {
                                names: vec![ast::Typed::untyped(temp_table_ident.clone())],
                                values: vec![ast::Expr::Table {
                                    items: values
                                        .iter()
                                        .map(|v| ast::TableItem::Implicit {
                                            value: self.visit_expr(v),
                                        })
                                        .collect(),
                                }],
                            },
                            ast::Stmt::Expression {
                                expr: ast::Expr::FunctionCall {
                                    func: Box::new(ast::Expr::Field {
                                        base: Box::new(ast::Expr::Named(ast::Identifier::new(
                                            "table",
                                        ))),
                                        field: ast::Identifier::new("move"),
                                    }),
                                    args: vec![
                                        ast::Expr::Named(temp_table_ident.clone()),
                                        ast::Expr::Literal(ast::Literal::Float(1.0)),
                                        ast::Expr::Unary {
                                            op: UnOp::Length,
                                            expr: Box::new(ast::Expr::Named(temp_table_ident)),
                                        },
                                        ast::Expr::Literal(ast::Literal::Float(*index as f64)),
                                        table_expr,
                                    ],
                                },
                            },
                        ]),
                    });
                } else {
                    let base = *index as usize;
                    let lhs = (base..base + values.len())
                        .map(|i| ast::Expr::Index {
                            base: Box::new(table_expr.clone()),
                            index: Box::new(ast::Expr::Literal(ast::Literal::Float(i as f64))),
                        })
                        .collect();
                    let rhs = values.iter().map(|v| self.visit_expr(v)).collect();

                    buf.push(ast::Stmt::Assignment { lhs, rhs });
                }
            }
            hil::Stmt::Call(expr) => buf.push(ast::Stmt::Expression {
                expr: self.visit_expr(expr),
            }),
            hil::Stmt::Phi(node) => {
                panic!(
                    "encountered unfolded phi node during structuring: target={}, operands={:?}",
                    node.target.index(),
                    node.operands
                )
            }
        }
    }

    fn visit_expr(&mut self, expr: &hil::Expr) -> ast::Expr {
        match expr {
            hil::Expr::Nil => ast::Expr::Literal(ast::Literal::Nil),
            hil::Expr::Number(num) => match num {
                hil::Number::Integer(i) => ast::Expr::Literal(ast::Literal::Integer(*i)),
                hil::Number::Float(f) => ast::Expr::Literal(ast::Literal::Float(*f)),
            },
            hil::Expr::String(s) => ast::Expr::Literal(ast::Literal::String(s.into())),
            hil::Expr::Bool(b) => ast::Expr::Literal(ast::Literal::Bool(*b)),
            hil::Expr::Symbol(sym) => self.symbol_expr(*sym),
            hil::Expr::Closure { proto, captures } => self.visit_closure(*proto, captures),
            hil::Expr::Binary { lhs, op, rhs } => ast::Expr::Binary {
                lhs: Box::new(self.visit_expr(lhs)),
                op: *op,
                rhs: Box::new(self.visit_expr(rhs)),
            },
            hil::Expr::Unary { op, expr } => ast::Expr::Unary {
                op: *op,
                expr: Box::new(self.visit_expr(expr)),
            },
            hil::Expr::Global(name) => ast::Expr::Named(ast::Identifier::new(name.clone())),
            hil::Expr::GetField { obj, field } => {
                let base = Box::new(self.visit_expr(obj));

                if is_valid_luau_identifier(field) {
                    ast::Expr::Field {
                        base,
                        field: ast::Identifier::new(field.clone()),
                    }
                } else {
                    ast::Expr::Index {
                        base,
                        index: Box::new(ast::Expr::Literal(ast::Literal::String(field.clone()))),
                    }
                }
            }
            hil::Expr::GetIndex { obj, index } => ast::Expr::Index {
                base: Box::new(self.visit_expr(obj)),
                index: Box::new(self.visit_expr(index)),
            },
            hil::Expr::Call { fun, args } => ast::Expr::FunctionCall {
                func: Box::new(self.visit_expr(fun)),
                args: args.iter().map(|expr| self.visit_expr(expr)).collect(),
            },
            hil::Expr::MethodCall {
                object,
                method,
                args,
            } => ast::Expr::MethodCall {
                object: Box::new(self.visit_expr(object)),
                method: ast::Identifier::new(method.clone()),
                args: args.iter().map(|expr| self.visit_expr(expr)).collect(),
            },
            hil::Expr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => ast::Expr::IfElse {
                condition: Box::new(self.visit_expr(condition)),
                then_expr: Box::new(self.visit_expr(then_expr)),
                else_expr: Box::new(self.visit_expr(else_expr)),
            },
            hil::Expr::Table { items } => ast::Expr::Table {
                items: self.visit_table_items(items),
            },
            hil::Expr::VarArgs => ast::Expr::Vararg,
        }
    }

    fn visit_table_items(&mut self, items: &[hil::TableItem]) -> Vec<ast::TableItem> {
        items
            .iter()
            .map(|item| match item {
                hil::TableItem::List(expr) => ast::TableItem::Implicit {
                    value: self.visit_expr(expr),
                },
                hil::TableItem::Index(key, value) => {
                    let value = self.visit_expr(value);
                    if let hil::Expr::String(s) = key
                        && is_valid_luau_identifier(s)
                    {
                        ast::TableItem::Named {
                            name: ast::Identifier::new(s.clone()),
                            value,
                        }
                    } else {
                        ast::TableItem::Indexed {
                            index: self.visit_expr(key),
                            value,
                        }
                    }
                }
            })
            .collect()
    }

    /// Emits one closure with the best inferred parameter annotations available.
    fn visit_closure(&mut self, proto_idx: ProtoId, captures: &[SymbolId]) -> ast::Expr {
        let proto_idx = proto_idx.0 as usize;
        let mut generic_names = HashSet::new();
        for symbol in &self.functions[proto_idx].symbols.params {
            if let Some(ty) = self.functions[proto_idx].symbol_type(*symbol) {
                collect_generic_names(ty, &mut generic_names);
            }
        }
        let mut generics = generic_names.into_iter().collect::<Vec<_>>();
        generics.sort();
        let parent_bindings: Vec<_> = captures
            .iter()
            .map(|sym| {
                self.symbol_storage(*sym)
                    .unwrap_or_else(|| SymbolStorage::Named(self.get_symbol_name(sym)))
            })
            .collect();

        let child_ctx = self.create_context(proto_idx);
        let child_upvalues = self.functions[proto_idx].symbols.upvalues.clone();
        for (i, binding) in parent_bindings.into_iter().enumerate() {
            if let Some(&child_upval_sym) = child_upvalues.get(i) {
                match binding {
                    SymbolStorage::Named(name) => {
                        self.contexts[child_ctx]
                            .plan
                            .inherit_named_upvalue(child_upval_sym, name);
                    }
                    SymbolStorage::Spilled(spill) => {
                        self.contexts[child_ctx]
                            .plan
                            .inherit_spilled_upvalue(child_upval_sym, spill);
                    }
                }
            }
        }

        let old_declarations = std::mem::take(&mut self.declarations);

        let param_symbols = self.functions[proto_idx].symbols.params.clone();
        let is_vararg = self.functions[proto_idx].is_vararg;
        let mut params: Vec<_> = param_symbols
            .into_iter()
            .map(|sym| {
                let name = self.get_symbol_name_for(child_ctx, sym);
                self.typed_parameter_for(proto_idx, sym, ast::Parameter::Regular(name))
            })
            .collect();
        if is_vararg {
            params.push(ast::Typed::untyped(ast::Parameter::Vararg));
        }

        let body = self.visit_function(child_ctx);

        self.declarations = old_declarations;

        ast::Expr::AnonymousFunction {
            generics,
            params,
            body,
        }
    }
}

pub fn emit_ast(
    functions: Vec<StructuredFunction>,
    entry: usize,
    options: DecompileOptions,
    diagnostics: &Diagnostics,
) -> ast::Block {
    let mut st = Emitter {
        functions,
        entry,
        options,
        diagnostics,
        declarations: DeclarationState::new(),
        contexts: Vec::new(),
        current_ctx: 0,
    };

    st.visit_entry()
}
