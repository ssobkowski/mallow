mod name;
pub mod options;

use std::collections::{HashMap, HashSet};

use smol_str::SmolStr;

use crate::{
    ast::{
        BinOp, Block, ElseClause, Expr, Identifier, If, Literal, Parameter, Stmt, TableItem, UnOp,
    },
    common::is_valid_luau_identifier,
    emitter::{name::NameAllocator, options::EmitterOptions},
    hil::{
        StructuredFunction,
        cflow::region::RegionNode,
        ir::{HilExpr, HilStmt, HilTableItem},
        lifter::ssa::SymbolId,
        visitor::Visitor,
    },
    scopes::Scopes,
};

const MAX_LOCAL_COUNT: usize = 199;

#[derive(Default)]
struct Collector {
    symbols: HashSet<SymbolId>,
}

impl Collector {
    fn collect_assigned_symbols(node: &RegionNode) -> HashSet<SymbolId> {
        let mut collector = Collector::default();
        collector.visit_region(node);
        collector.symbols
    }
}

impl Visitor for Collector {
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

#[derive(Clone)]
struct SpillSlot {
    table: Identifier,
    slot: usize,
}

enum SymbolStorage {
    Named(Identifier),
    Spilled(SpillSlot),
}

impl SymbolStorage {
    fn into_expr(self) -> Expr {
        match self {
            SymbolStorage::Named(name) => Expr::Named(name),
            SymbolStorage::Spilled(SpillSlot { table, slot }) => Expr::Index {
                base: Box::new(Expr::Named(table)),
                index: Box::new(Expr::Literal(Literal::Number(slot as f64))),
            },
        }
    }
}

struct FunctionContext {
    proto_idx: usize,
    allocator: NameAllocator,
    names: HashMap<SymbolId, Identifier>,

    next_local_slot: usize,
    forced_named_symbols: HashSet<SymbolId>,
    inherited_spills: HashMap<SymbolId, SpillSlot>,
    spill_table: Option<Identifier>,

    anomalies: Vec<String>,
}

struct Emitter {
    functions: Vec<StructuredFunction>,
    entry: usize,
    options: EmitterOptions,

    // symbol -> index of the local in the scope
    scopes: Scopes<SymbolId, usize>,
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
            allocator: NameAllocator::default(),
            names: HashMap::new(),
            next_local_slot: 0,
            forced_named_symbols: HashSet::new(),
            inherited_spills: HashMap::new(),
            spill_table: None,
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

        let scope = self.scopes.push_scope();
        for &sym in fun.cfg.params() {
            let slot = self.contexts[self.current_ctx].next_local_slot;
            self.contexts[self.current_ctx].next_local_slot += 1;
            scope.declare(sym, slot);
        }
        for &sym in fun.cfg.upvalues() {
            let slot = self.contexts[self.current_ctx].next_local_slot;
            self.contexts[self.current_ctx].next_local_slot += 1;
            scope.declare(sym, slot);
        }

        let upvalue_str = fun
            .upvalues
            .iter()
            .map(|u| self.get_symbol_name(u).0)
            .collect::<Vec<_>>()
            .join(", ");
        let mut block = Block::with_stmts(vec![Stmt::Comment {
            text: format!("proto {}: upvalues = [{}]", proto_idx, upvalue_str),
        }]);
        block.stmts.extend(self.visit_region(&fun.root).stmts);
        for (idx, anomaly) in self.contexts[self.current_ctx].anomalies.iter().enumerate() {
            block.stmts.insert(
                idx + 1,
                Stmt::Comment {
                    text: format!("anomaly: {anomaly}"),
                },
            );
        }
        if let Some(table) = self.contexts[self.current_ctx].spill_table.clone() {
            block.stmts.insert(
                1 + self.contexts[self.current_ctx].anomalies.len(),
                Stmt::LocalDeclaration {
                    names: vec![table],
                    values: vec![Expr::Table { items: Vec::new() }],
                },
            );
        }
        self.scopes.pop_scope();

        self.current_ctx = old_ctx;
        block
    }

    fn reserve_symbol_name_exact(
        &mut self,
        ctx_idx: usize,
        sym: SymbolId,
        preferred: SmolStr,
    ) -> Identifier {
        if let Some(name) = self.contexts[ctx_idx].names.get(&sym) {
            return name.clone();
        }

        let name = self.contexts[ctx_idx].allocator.reserve_exact(preferred);
        self.contexts[ctx_idx].names.insert(sym, name.clone());
        name
    }

    fn reserve_symbol_name_fresh(
        &mut self,
        ctx_idx: usize,
        sym: SymbolId,
        is_param: bool,
    ) -> Identifier {
        if let Some(name) = self.contexts[ctx_idx].names.get(&sym) {
            return name.clone();
        }

        let name = if is_param {
            self.contexts[ctx_idx].allocator.fresh_param()
        } else {
            self.contexts[ctx_idx].allocator.fresh_local()
        };
        self.contexts[ctx_idx].names.insert(sym, name.clone());
        name
    }

    fn get_symbol_name(&mut self, sym: &SymbolId) -> Identifier {
        self.get_symbol_name_for(self.current_ctx, *sym)
    }

    fn get_symbol_name_for(&mut self, ctx_idx: usize, sym: SymbolId) -> Identifier {
        if let Some(name) = self.contexts[ctx_idx].names.get(&sym) {
            return name.clone();
        }

        let proto_idx = self.contexts[ctx_idx].proto_idx;
        let is_param = self.functions[proto_idx].params.contains(&sym);
        self.reserve_symbol_name_fresh(ctx_idx, sym, is_param)
    }

    fn current_context(&self) -> &FunctionContext {
        &self.contexts[self.current_ctx]
    }

    fn current_context_mut(&mut self) -> &mut FunctionContext {
        &mut self.contexts[self.current_ctx]
    }

    fn fresh_temp_local(&mut self) -> Identifier {
        self.current_context_mut().allocator.fresh_local()
    }

    fn declare_symbol(&mut self, sym: SymbolId) -> usize {
        let slot = self.current_context().next_local_slot;
        self.current_context_mut().next_local_slot += 1;
        self.scopes.declare(sym, slot);
        slot
    }

    fn reserve_spill_table(&mut self, ctx_idx: usize) -> Identifier {
        if let Some(name) = self.contexts[ctx_idx].spill_table.clone() {
            return name;
        }

        let name = self.contexts[ctx_idx].allocator.reserve_exact("_ms".into());
        self.contexts[ctx_idx].spill_table = Some(name.clone());
        name
    }

    fn symbol_storage(&mut self, sym: SymbolId) -> Option<SymbolStorage> {
        if let Some(spill) = self.current_context().inherited_spills.get(&sym) {
            return Some(SymbolStorage::Spilled(spill.clone()));
        }

        let proto_idx = self.current_context().proto_idx;
        let fun = &self.functions[proto_idx];
        if fun.params.contains(&sym)
            || fun.upvalues.contains(&sym)
            || self.current_context().forced_named_symbols.contains(&sym)
        {
            return Some(SymbolStorage::Named(self.get_symbol_name(&sym)));
        }

        let idx = *self.scopes.get(&sym)?;
        if self.options.spill_locals && idx >= MAX_LOCAL_COUNT {
            return Some(SymbolStorage::Spilled(SpillSlot {
                table: self.reserve_spill_table(self.current_ctx),
                slot: idx,
            }));
        }

        Some(SymbolStorage::Named(self.get_symbol_name(&sym)))
    }

    fn symbol_expr(&mut self, sym: SymbolId) -> Expr {
        let name = self.get_symbol_name(&sym);
        let Some(storage) = self.symbol_storage(sym) else {
            let proto_idx = self.current_proto_idx();
            self.record_anomaly(format!(
                "undeclared symbol read during structuring: proto={}, symbol={}, emitted as {}",
                proto_idx,
                sym.index(),
                name.as_str()
            ));
            return Expr::Named(name);
        };

        storage.into_expr()
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

    fn visit_node(&mut self, node: &RegionNode, buf: &mut Vec<Stmt>) {
        match node {
            RegionNode::BasicBlock { stmts } => self.visit_block(stmts, buf),
            RegionNode::Sequence { nodes } => {
                for n in nodes {
                    self.visit_node(n, buf);
                }
            }
            RegionNode::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let then_assigned = Collector::collect_assigned_symbols(then_branch);

                let else_assigned = else_branch
                    .as_ref()
                    .map(|node| Collector::collect_assigned_symbols(node))
                    .unwrap_or_default();

                let mut hoisted: Vec<_> = then_assigned
                    .intersection(&else_assigned)
                    .copied()
                    .filter(|sym| !self.scopes.contains(sym))
                    .collect();
                hoisted.sort_by_key(|sym| sym.index());

                // Luau: if this `If` follows the structure of:
                //
                // hoisted = [var]
                // if <cond> then var = var_if_true else var = var_if_false end
                //
                // we can emit it as a Luau `if` expression
                if let Some(else_branch) = else_branch.as_ref()
                    && let [sym] = hoisted.as_slice()
                    && let Some((then_value, else_value)) =
                        Self::match_if_assign(*sym, then_branch, else_branch)
                {
                    let value =
                        match Self::try_simplify_bool_ifelse(condition, then_value, else_value) {
                            Some(e) => self.visit_expr(&e),
                            None => Expr::IfElse {
                                condition: Box::new(self.visit_expr(condition)),
                                then_expr: Box::new(self.visit_expr(then_value)),
                                else_expr: Box::new(self.visit_expr(else_value)),
                            },
                        };

                    self.declare_symbol(*sym);
                    buf.push(
                        match self
                            .symbol_storage(*sym)
                            .expect("if-expression target was just declared")
                        {
                            SymbolStorage::Named(name) => Stmt::LocalDeclaration {
                                names: vec![name],
                                values: vec![value],
                            },
                            SymbolStorage::Spilled(_) => Stmt::Assignment {
                                lhs: vec![self.symbol_expr(*sym)],
                                rhs: vec![value],
                            },
                        },
                    );
                    return;
                }

                if !hoisted.is_empty() {
                    for sym in &hoisted {
                        self.declare_symbol(*sym);
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

                self.scopes.push_scope();

                let then_body = self.visit_region(then_branch);
                let else_clause = else_branch.as_ref().map(|e| {
                    let region = self.visit_region(e);

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

                self.scopes.pop_scope();
            }
            RegionNode::While {
                condition, body, ..
            } => {
                self.scopes.push_scope();

                let body = self.visit_region(body);
                buf.push(Stmt::While {
                    condition: self.visit_expr(condition),
                    body,
                });

                self.scopes.pop_scope();
            }
            RegionNode::RepeatUntil { condition, body } => {
                self.scopes.push_scope();

                let body = self.visit_region(body);
                buf.push(Stmt::RepeatUntil {
                    condition: self.visit_expr(condition),
                    body,
                });

                self.scopes.pop_scope();
            }
            RegionNode::NumericFor {
                body,
                var,
                start,
                end,
                step,
                ..
            } => {
                self.scopes.push_scope();

                self.declare_symbol(*var);
                self.current_context_mut().forced_named_symbols.insert(*var);
                let var = self.get_symbol_name(var);
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

                self.scopes.pop_scope();
            }
            RegionNode::GenericFor {
                vars, exprs, body, ..
            } => {
                self.scopes.push_scope();

                for &var in vars {
                    self.declare_symbol(var);
                    self.current_context_mut().forced_named_symbols.insert(var);
                }
                let vars = vars.iter().map(|s| self.get_symbol_name(s)).collect();
                let exprs = exprs.iter().map(|expr| self.visit_expr(expr)).collect();
                let body = self.visit_region(body);
                buf.push(Stmt::GenericFor { vars, exprs, body });

                self.scopes.pop_scope();
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
            value: HilExpr::Closure { captures, .. },
        } = stmt
        else {
            return;
        };

        if self.scopes.contains(sym) || !captures.iter().any(|capture| capture == sym) {
            return;
        }

        self.declare_symbol(*sym);
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
                let left_expr = match left {
                    HilExpr::Symbol(sym) => {
                        if !self.scopes.contains(sym) {
                            self.declare_symbol(*sym);
                            needs_declaration = true;
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
                        && op.is_compound()
                    {
                        buf.push(Stmt::CompoundAssignment {
                            lhs: left_expr,
                            op: (*op).into(),
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
                    .map(|sym| self.scopes.contains(sym))
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

                let all_declared = was_declared.iter().all(|declared| *declared);
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
                    storages.into_iter().zip(was_declared).zip(temps)
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
                                        Expr::Literal(Literal::Number(1.0)),
                                        Expr::Unary {
                                            op: UnOp::Length,
                                            expr: Box::new(Expr::Named(temp_table_ident)),
                                        },
                                        Expr::Literal(Literal::Number(*index as f64)),
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
                            index: Box::new(Expr::Literal(Literal::Number(i as f64))),
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
            HilExpr::Number(num) => Expr::Literal(Literal::Number(*num)),
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
            HilExpr::Import(import) => Expr::Named(Identifier::new(import.clone())),
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

    fn visit_closure(&mut self, proto_idx: usize, captures: &[SymbolId]) -> Expr {
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
                        self.reserve_symbol_name_exact(child_ctx, child_upval_sym, name.0);
                    }
                    SymbolStorage::Spilled(spill) => {
                        self.contexts[child_ctx]
                            .inherited_spills
                            .insert(child_upval_sym, spill.clone());
                        self.contexts[child_ctx]
                            .allocator
                            .reserve_exact(spill.table.0.clone());
                    }
                }
            }
        }

        let old_scopes = std::mem::take(&mut self.scopes);

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

        self.scopes = old_scopes;

        Expr::AnonymousFunction { params, body }
    }

    /// Returns the values assigned to `sym` in the then/else branches, if both branches
    /// consist of exactly one assignment to `sym` in a basic block.
    ///
    /// Returns `None` if either branch is not a basic block, contains more than one statement,
    /// or does not assign to `sym`.
    fn match_if_assign<'a>(
        sym: SymbolId,
        then_branch: &'a RegionNode,
        else_branch: &'a RegionNode,
    ) -> Option<(&'a HilExpr, &'a HilExpr)> {
        let single_value = |node: &'a RegionNode| {
            let RegionNode::BasicBlock { stmts } = node else {
                return None;
            };
            let [HilStmt::Assign { left, value }] = stmts.as_slice() else {
                return None;
            };
            (left == &HilExpr::Symbol(sym)).then_some(value)
        };

        Some((single_value(then_branch)?, single_value(else_branch)?))
    }

    /// Attempts to build a boolean-like expression from an if/else branch pair.
    fn try_simplify_bool_ifelse(
        condition: &HilExpr,
        then_value: &HilExpr,
        else_value: &HilExpr,
    ) -> Option<HilExpr> {
        match (then_value, else_value) {
            (HilExpr::Bool(true), HilExpr::Bool(false)) => match condition {
                HilExpr::Binary {
                    op: BinOp::Eq | BinOp::Ne,
                    ..
                } => Some(condition.clone()),
                _ => None,
            },
            (HilExpr::Bool(false), HilExpr::Bool(true)) => match condition {
                HilExpr::Binary {
                    op: BinOp::Eq | BinOp::Ne,
                    ..
                } => Some(condition.clone().invert()),
                // not (x < y) != x >= y when x or y is NaN, so only use comparison
                // inversion for equality operators and otherwise keep the if-expression.
                _ => None,
            },
            _ => None,
        }
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
        scopes: Scopes::new(),
        contexts: Vec::new(),
        current_ctx: 0,
    };

    st.visit_entry()
}
