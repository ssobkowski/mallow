mod collectors;
mod declarations;
mod locals;
mod name;
pub mod options;
mod plan;
mod storage;

use std::collections::HashSet;

use crate::{
    ast::{
        Block, CompoundBinOp, ElseClause, Expr, Identifier, If, Literal, Parameter, Stmt,
        TableItem, UnOp,
    },
    common::is_valid_luau_identifier,
    emitter::{
        collectors::ReadCollector, declarations::DeclarationState, options::EmitterOptions,
        plan::FunctionPlan, storage::SymbolStorage,
    },
    hil::{
        StructuredFunction,
        cflow::region::RegionNode,
        ir::{HilExpr, HilNumber, HilStmt, HilTableItem},
        lifter::ssa::SymbolId,
        visitor::Visitor,
    },
    il::ProtoId,
};

const MAX_LOCAL_COUNT: usize = 199;

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
    fn visit_stmt(&mut self, stmt: &HilStmt) {
        match stmt {
            HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                ..
            } => {
                self.symbols.insert(*sym);
            }
            HilStmt::AssignMany { left, .. } => {
                self.symbols.extend(left.iter().filter_map(|lv| {
                    if let HilExpr::Symbol(s) = lv {
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

struct Emitter {
    functions: Vec<StructuredFunction>,
    entry: usize,
    options: EmitterOptions,

    declarations: DeclarationState,
    contexts: Vec<FunctionContext>,
    current_ctx: usize,
}

impl Emitter {
    fn visit_entry(&mut self) -> Block {
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

    fn visit_function(&mut self, ctx_idx: usize) -> Block {
        let old_ctx = self.current_ctx;
        self.current_ctx = ctx_idx;

        let proto_idx = self.current_proto_idx();
        let fun = self.functions[proto_idx].clone();

        self.declarations.push_scope();
        for &sym in fun.cfg.params() {
            let slot = self.declare_symbol(sym);
            self.bind_slot_to_symbol_name(slot, sym);
            self.declare_slot(slot);
        }
        for &sym in fun.cfg.upvalues() {
            let slot = self.declare_symbol(sym);
            self.bind_slot_to_symbol_name(slot, sym);
            self.declare_slot(slot);
        }

        let upvalue_str = fun
            .upvalues
            .iter()
            .map(|u| self.get_symbol_name(u).0)
            .collect::<Vec<_>>()
            .join(", ");
        let mut block = if self.entry != proto_idx {
            Block::with_stmts(vec![Stmt::Comment {
                text: format!("proto {}: upvalues = [{}]", proto_idx, upvalue_str),
            }])
        } else {
            Block::with_stmts(Vec::new())
        };
        block.stmts.extend(self.visit_region(&fun.root).stmts);
        for (idx, anomaly) in self.contexts[self.current_ctx].anomalies.iter().enumerate() {
            block.stmts.insert(
                idx + 1,
                Stmt::Comment {
                    text: format!("anomaly: {anomaly}"),
                },
            );
        }
        if let Some(table) = self.contexts[self.current_ctx].plan.spill_table() {
            block.stmts.insert(
                1 + self.contexts[self.current_ctx].anomalies.len(),
                Stmt::LocalDeclaration {
                    names: vec![table],
                    values: vec![Expr::Table { items: Vec::new() }],
                },
            );
        }
        self.declarations.pop_scope();

        self.current_ctx = old_ctx;
        block
    }

    fn get_symbol_name(&mut self, sym: &SymbolId) -> Identifier {
        self.get_symbol_name_for(self.current_ctx, *sym)
    }

    fn get_symbol_name_for(&mut self, ctx_idx: usize, sym: SymbolId) -> Identifier {
        let proto_idx = self.contexts[ctx_idx].proto_idx;
        let is_param = self.functions[proto_idx].params.contains(&sym);
        self.contexts[ctx_idx].plan.get_symbol_name(sym, is_param)
    }

    fn bind_slot_to_symbol_name(&mut self, slot: usize, sym: SymbolId) {
        let proto_idx = self.current_context().proto_idx;
        let is_param = self.functions[proto_idx].params.contains(&sym);
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

    fn fresh_temp_local(&mut self) -> Identifier {
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

    fn symbol_expr(&mut self, sym: SymbolId) -> Expr {
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
                Expr::Named(name)
            }
        }
    }

    fn record_anomaly(&mut self, message: String) {
        let anomalies = &mut self.contexts[self.current_ctx].anomalies;
        if !anomalies.contains(&message) {
            anomalies.push(message);
        }
    }

    fn visit_region(&mut self, region: &RegionNode) -> Block {
        let mut stmts = Vec::new();
        self.visit_node(region, &mut stmts);
        Block::with_stmts(stmts)
    }

    /// Visits a flat sequence of region nodes, giving each `If` node access to its
    /// continuation so that only symbols genuinely needed after the branch are hoisted.
    fn visit_sequence(&mut self, nodes: &[RegionNode], buf: &mut Vec<Stmt>) {
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
        condition: &HilExpr,
        then_branch: &RegionNode,
        else_branch: Option<&RegionNode>,
        continuation: &[RegionNode],
        buf: &mut Vec<Stmt>,
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
                    Some(SymbolStorage::Named(name)) => Some(name),
                    Some(SymbolStorage::Spilled(_)) | None => None,
                })
                .collect();
            if !names.is_empty() {
                buf.push(Stmt::LocalDeclaration {
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
            if let [Stmt::If(elseif)] = region.stmts.as_slice() {
                return ElseClause::If(Box::new(elseif.clone()));
            }

            ElseClause::Else(region)
        });

        buf.push(Stmt::If(If {
            condition: self.visit_expr(condition),
            then_body,
            else_clause,
        }));
    }

    fn visit_node(&mut self, node: &RegionNode, buf: &mut Vec<Stmt>) {
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
                buf.push(Stmt::While {
                    condition: self.visit_expr(condition),
                    body,
                });

                self.declarations.pop_scope();
            }
            RegionNode::RepeatUntil { condition, body } => {
                self.declarations.push_scope();

                let body = self.visit_region(body);
                buf.push(Stmt::RepeatUntil {
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
                    Expr::Named(name) => name,
                    _ => unreachable!("numeric-for variables cannot be spilled"),
                };
                let start = self.visit_expr(start);
                let end = self.visit_expr(end);
                let step = Some(self.visit_expr(step));

                let body = self.visit_region(body);
                buf.push(Stmt::NumericFor {
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
                        Expr::Named(name) => name,
                        _ => unreachable!("generic-for variables cannot be spilled"),
                    })
                    .collect();
                let exprs = exprs.iter().map(|expr| self.visit_expr(expr)).collect();
                let body = self.visit_region(body);
                buf.push(Stmt::GenericFor { vars, exprs, body });

                self.declarations.pop_scope();
            }
            RegionNode::Continue => buf.push(Stmt::Continue),
            RegionNode::Break => buf.push(Stmt::Break),
            RegionNode::Return { values } => {
                buf.push(Stmt::Return {
                    values: values.iter().map(|expr| self.visit_expr(expr)).collect(),
                });
            }
        }
    }

    fn visit_block(&mut self, stmts: &[HilStmt], buf: &mut Vec<Stmt>) {
        for stmt in stmts {
            self.maybe_predeclare_recursive_local(stmt, buf);
            self.visit_stmt(stmt, buf);
        }
    }

    fn maybe_predeclare_recursive_local(&mut self, stmt: &HilStmt, buf: &mut Vec<Stmt>) {
        let HilStmt::Assign {
            left: HilExpr::Symbol(sym),
            value: HilExpr::Closure { proto, captures },
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
            buf.push(Stmt::LocalDeclaration {
                names: vec![name],
                values: Vec::new(),
            });
        }
    }

    fn visit_stmt(&mut self, stmt: &HilStmt, buf: &mut Vec<Stmt>) {
        match stmt {
            HilStmt::Assign { left, value } => {
                let mut needs_declaration = false;
                let mut named_closure = false;

                let left_expr = match left {
                    HilExpr::Symbol(sym) => {
                        if !self.declarations.contains_symbol(sym) {
                            // If value is a named closure, reserve its debug_name
                            // as the symbol name before declaring/symbol_expr.
                            if let HilExpr::Closure { proto, .. } = value {
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
                let right = self.visit_expr(value);

                if needs_declaration {
                    let HilExpr::Symbol(sym) = left else {
                        unreachable!("non-symbol lvalues are never declarations");
                    };

                    if named_closure
                        && let Some(SymbolStorage::Named(name)) = self.symbol_storage(*sym)
                        && let Expr::AnonymousFunction { params, body } = right
                    {
                        buf.push(Stmt::LocalFunction { name, params, body });
                        return;
                    }

                    match self
                        .symbol_storage(*sym)
                        .expect("symbol was just declared in scope")
                    {
                        SymbolStorage::Named(name) => buf.push(Stmt::LocalDeclaration {
                            names: vec![name],
                            values: vec![right],
                        }),
                        SymbolStorage::Spilled(_) => buf.push(Stmt::Assignment {
                            lhs: vec![left_expr],
                            rhs: vec![right],
                        }),
                    }
                } else {
                    if let Expr::Binary { lhs, op, rhs } = &right
                        && left.is_pure()
                        && lhs.as_ref() == &left_expr
                        && let Ok(compound_op) = CompoundBinOp::try_from(*op)
                    {
                        buf.push(Stmt::CompoundAssignment {
                            lhs: left_expr,
                            op: compound_op,
                            rhs: rhs.as_ref().clone(),
                        });
                        return;
                    }

                    buf.push(Stmt::Assignment {
                        lhs: vec![left_expr],
                        rhs: vec![right],
                    });
                }
            }
            HilStmt::AssignMany { left, value } => {
                let right = self.visit_expr(value);
                if left
                    .iter()
                    .any(|lvalue| !matches!(lvalue, HilExpr::Symbol(_)))
                {
                    let lhs = left.iter().map(|lvalue| self.visit_expr(lvalue)).collect();
                    buf.push(Stmt::Assignment {
                        lhs,
                        rhs: vec![right],
                    });
                    return;
                }

                let symbols: Vec<_> = left
                    .iter()
                    .map(|lvalue| {
                        let HilExpr::Symbol(sym) = lvalue else {
                            unreachable!("guarded by symbol-only branch")
                        };
                        *sym
                    })
                    .collect();

                let was_declared: Vec<_> = symbols
                    .iter()
                    .map(|sym| self.declarations.contains_symbol(sym))
                    .collect();

                for (sym, declared) in symbols.iter().zip(&was_declared) {
                    if !declared {
                        self.declare_symbol(*sym);
                    }
                }

                let storages: Vec<_> = symbols
                    .iter()
                    .map(|sym| {
                        self.symbol_storage(*sym)
                            .expect("assign-many symbols must exist in scope")
                    })
                    .collect();

                let slot_was_declared: Vec<_> = symbols
                    .iter()
                    .map(|sym| {
                        let slot = self
                            .declarations
                            .symbol_slot(sym)
                            .expect("assign-many symbols must exist in scope");
                        self.declarations.contains_slot(slot)
                    })
                    .collect();
                for (sym, declared) in symbols.iter().zip(&slot_was_declared) {
                    if !declared {
                        let slot = self
                            .declarations
                            .symbol_slot(sym)
                            .expect("assign-many symbols must exist in scope");
                        self.declare_slot(slot);
                    }
                }

                let all_declared = slot_was_declared.iter().all(|declared| *declared);
                if all_declared {
                    buf.push(Stmt::Assignment {
                        lhs: storages.into_iter().map(|s| s.into_expr()).collect(),
                        rhs: vec![right],
                    });
                    return;
                }

                let all_named = storages
                    .iter()
                    .all(|storage| matches!(storage, SymbolStorage::Named(_)));
                if all_named {
                    let names = storages
                        .into_iter()
                        .map(|storage| match storage {
                            SymbolStorage::Named(name) => name,
                            SymbolStorage::Spilled(_) => unreachable!("guarded by all_named"),
                        })
                        .collect();
                    buf.push(Stmt::LocalDeclaration {
                        names,
                        values: vec![right],
                    });
                    return;
                }

                let temps: Vec<_> = (0..symbols.len())
                    .map(|_| self.fresh_temp_local())
                    .collect();
                buf.push(Stmt::LocalDeclaration {
                    names: temps.clone(),
                    values: vec![right],
                });

                for ((storage, was_declared), temp) in
                    storages.into_iter().zip(slot_was_declared).zip(temps)
                {
                    let rhs = vec![Expr::Named(temp)];
                    match (storage, was_declared) {
                        (SymbolStorage::Named(name), false) => buf.push(Stmt::LocalDeclaration {
                            names: vec![name],
                            values: rhs,
                        }),
                        (storage, true) | (storage @ SymbolStorage::Spilled(_), false) => {
                            buf.push(Stmt::Assignment {
                                lhs: vec![storage.into_expr()],
                                rhs,
                            });
                        }
                    }
                }
            }
            HilStmt::SetList {
                table,
                index,
                values,
                has_variadic_tail,
            } => {
                let table_expr = self.visit_expr(&HilExpr::Symbol(*table));
                if *has_variadic_tail {
                    // The idea is that if we have a variadic tail, we can't simply assign
                    // a tuple to a single index (t[k] = a, b)
                    //
                    // We create a temporary table and then copy the contents of it into the
                    // true table with `table.move`
                    //
                    // This should run only if the 'fold_tables' pass did not fold this SetList
                    // into table constructor.

                    let temp_table_ident = Identifier::new("__t");
                    buf.push(Stmt::Do {
                        body: Block::with_stmts(vec![
                            Stmt::LocalDeclaration {
                                names: vec![temp_table_ident.clone()],
                                values: vec![Expr::Table {
                                    items: values
                                        .iter()
                                        .map(|v| TableItem::Implicit {
                                            value: self.visit_expr(v),
                                        })
                                        .collect(),
                                }],
                            },
                            Stmt::Expression {
                                expr: Expr::FunctionCall {
                                    func: Box::new(Expr::Field {
                                        base: Box::new(Expr::Named(Identifier::new("table"))),
                                        field: Identifier::new("move"),
                                    }),
                                    args: vec![
                                        Expr::Named(temp_table_ident.clone()),
                                        Expr::Literal(Literal::Float(1.0)),
                                        Expr::Unary {
                                            op: UnOp::Length,
                                            expr: Box::new(Expr::Named(temp_table_ident)),
                                        },
                                        Expr::Literal(Literal::Float(*index as f64)),
                                        table_expr,
                                    ],
                                },
                            },
                        ]),
                    });
                } else {
                    let base = *index as usize;
                    let lhs = (base..base + values.len())
                        .map(|i| Expr::Index {
                            base: Box::new(table_expr.clone()),
                            index: Box::new(Expr::Literal(Literal::Float(i as f64))),
                        })
                        .collect();
                    let rhs = values.iter().map(|v| self.visit_expr(v)).collect();

                    buf.push(Stmt::Assignment { lhs, rhs });
                }
            }
            HilStmt::Call(expr) => buf.push(Stmt::Expression {
                expr: self.visit_expr(expr),
            }),
            HilStmt::Phi(node) => {
                panic!(
                    "encountered unfolded phi node during structuring: target={}, operands={:?}",
                    node.target.index(),
                    node.operands
                )
            }
        }
    }

    fn visit_expr(&mut self, expr: &HilExpr) -> Expr {
        match expr {
            HilExpr::Nil => Expr::Literal(Literal::Nil),
            HilExpr::Number(num) => match num {
                HilNumber::Integer(i) => Expr::Literal(Literal::Integer(*i)),
                HilNumber::Float(f) => Expr::Literal(Literal::Float(*f)),
            },
            HilExpr::String(s) => Expr::Literal(Literal::String(s.into())),
            HilExpr::Bool(b) => Expr::Literal(Literal::Bool(*b)),
            HilExpr::Symbol(sym) => self.symbol_expr(*sym),
            HilExpr::Closure { proto, captures } => self.visit_closure(*proto, captures),
            HilExpr::Binary { lhs, op, rhs } => Expr::Binary {
                lhs: Box::new(self.visit_expr(lhs)),
                op: *op,
                rhs: Box::new(self.visit_expr(rhs)),
            },
            HilExpr::Unary { op, expr } => Expr::Unary {
                op: *op,
                expr: Box::new(self.visit_expr(expr)),
            },
            HilExpr::Global(name) => Expr::Named(Identifier::new(name.clone())),
            HilExpr::GetField { obj, field } => {
                let base = Box::new(self.visit_expr(obj));

                if is_valid_luau_identifier(field) {
                    Expr::Field {
                        base,
                        field: Identifier::new(field.clone()),
                    }
                } else {
                    Expr::Index {
                        base,
                        index: Box::new(Expr::Literal(Literal::String(field.clone()))),
                    }
                }
            }
            HilExpr::GetIndex { obj, index } => Expr::Index {
                base: Box::new(self.visit_expr(obj)),
                index: Box::new(self.visit_expr(index)),
            },
            HilExpr::Call { fun, args } => Expr::FunctionCall {
                func: Box::new(self.visit_expr(fun)),
                args: args.iter().map(|expr| self.visit_expr(expr)).collect(),
            },
            HilExpr::MethodCall {
                object,
                method,
                args,
            } => Expr::MethodCall {
                object: Box::new(self.visit_expr(object)),
                method: Identifier::new(method.clone()),
                args: args.iter().map(|expr| self.visit_expr(expr)).collect(),
            },
            HilExpr::IfElse {
                condition,
                then_expr,
                else_expr,
            } => Expr::IfElse {
                condition: Box::new(self.visit_expr(condition)),
                then_expr: Box::new(self.visit_expr(then_expr)),
                else_expr: Box::new(self.visit_expr(else_expr)),
            },
            HilExpr::Table { items } => Expr::Table {
                items: self.visit_table_items(items),
            },
            HilExpr::VarArgs => Expr::Vararg,
        }
    }

    fn visit_table_items(&mut self, items: &[HilTableItem]) -> Vec<TableItem> {
        items
            .iter()
            .map(|item| match item {
                HilTableItem::List(expr) => TableItem::Implicit {
                    value: self.visit_expr(expr),
                },
                HilTableItem::Index(key, value) => {
                    let value = self.visit_expr(value);
                    if let HilExpr::String(s) = key
                        && is_valid_luau_identifier(s)
                    {
                        TableItem::Named {
                            name: Identifier::new(s.clone()),
                            value,
                        }
                    } else {
                        TableItem::Indexed {
                            index: self.visit_expr(key),
                            value,
                        }
                    }
                }
            })
            .collect()
    }

    fn visit_closure(&mut self, proto_idx: ProtoId, captures: &[SymbolId]) -> Expr {
        let proto_idx = proto_idx.0 as usize;
        let parent_bindings: Vec<_> = captures
            .iter()
            .map(|sym| {
                self.symbol_storage(*sym)
                    .unwrap_or_else(|| SymbolStorage::Named(self.get_symbol_name(sym)))
            })
            .collect();

        let child_ctx = self.create_context(proto_idx);
        let child_upvalues = self.functions[proto_idx].upvalues.clone();
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

        let param_symbols = self.functions[proto_idx].params.clone();
        let is_vararg = self.functions[proto_idx].is_vararg;
        let mut params: Vec<_> = param_symbols
            .into_iter()
            .map(|sym| Parameter::Regular(self.get_symbol_name_for(child_ctx, sym)))
            .collect();
        if is_vararg {
            params.push(Parameter::Vararg);
        }

        let body = self.visit_function(child_ctx);

        self.declarations = old_declarations;

        Expr::AnonymousFunction { params, body }
    }
}

pub fn emit_ast(
    functions: Vec<StructuredFunction>,
    entry: usize,
    options: EmitterOptions,
) -> Block {
    let mut st = Emitter {
        functions,
        entry,
        options,
        declarations: DeclarationState::new(),
        contexts: Vec::new(),
        current_ctx: 0,
    };

    st.visit_entry()
}
