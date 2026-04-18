use std::collections::{HashMap, HashSet};

use smol_str::{SmolStr, format_smolstr};

use crate::{
    ast::{Block, Expr, Identifier, Literal, Parameter, Stmt, TableItem, UnOp},
    hil::{
        StructuredFunction,
        cflow::region::RegionNode,
        ir::{HilExpr, HilStmt, HilTableItem},
        lifter::ssa::SymbolId,
    },
    scopes::Scopes,
};

#[derive(Default)]
struct NameAllocator {
    used: HashSet<SmolStr>,
    next_param: usize,
    next_local: usize,
}

impl NameAllocator {
    fn reserve_exact(&mut self, preferred: SmolStr) -> Identifier {
        if self.used.insert(preferred.clone()) {
            return Identifier::new(preferred);
        }

        let mut counter = 0usize;
        loop {
            let candidate = format_smolstr!("{preferred}__{counter}");
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
            counter += 1;
        }
    }

    fn fresh_param(&mut self) -> Identifier {
        loop {
            let candidate = format_smolstr!("p{}", self.next_param);
            self.next_param += 1;
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
        }
    }

    fn fresh_local(&mut self) -> Identifier {
        loop {
            let candidate = format_smolstr!("v{}", self.next_local);
            self.next_local += 1;
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
        }
    }
}

struct FunctionContext {
    proto_idx: usize,
    allocator: NameAllocator,
    names: HashMap<SymbolId, Identifier>,
}

struct Structurer {
    functions: Vec<StructuredFunction>,
    entry: usize,

    scopes: Scopes<SymbolId, ()>,
    contexts: Vec<FunctionContext>,
    current_ctx: usize,
}

impl Structurer {
    fn visit_entry(&mut self) -> Block {
        let entry_ctx = self.create_context(self.entry);
        self.visit_function(entry_ctx)
    }

    fn create_context(&mut self, proto_idx: usize) -> usize {
        let ctx = FunctionContext {
            proto_idx,
            allocator: NameAllocator::default(),
            names: HashMap::new(),
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
        let fun = &self.functions[proto_idx].clone();

        self.scopes.push_scope();
        for &sym in &fun.cfg.params {
            self.scopes.declare(sym, ());
        }
        for &sym in &fun.cfg.upvalues {
            self.scopes.declare(sym, ());
        }

        let mut block = Block::with_stmts(vec![Stmt::Comment {
            text: format!("proto {}", proto_idx),
        }]);
        block.stmts.extend(self.visit_region(&fun.root).stmts);
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
        let is_param = self.functions[proto_idx].cfg.params.contains(&sym);
        self.reserve_symbol_name_fresh(ctx_idx, sym, is_param)
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
                let mut then_assigned = HashSet::new();
                self.collect_assigned_symbols_in_region(then_branch, &mut then_assigned);

                let mut else_assigned = HashSet::new();
                if let Some(else_branch) = else_branch {
                    self.collect_assigned_symbols_in_region(else_branch, &mut else_assigned);
                }

                let mut hoisted: Vec<_> = then_assigned
                    .intersection(&else_assigned)
                    .copied()
                    .filter(|sym| !self.scopes.contains(sym))
                    .collect();
                hoisted.sort_by_key(|sym| sym.index());

                if !hoisted.is_empty() {
                    for sym in &hoisted {
                        self.scopes.declare(*sym, ());
                    }

                    let names = hoisted
                        .iter()
                        .map(|sym| self.get_symbol_name(sym))
                        .collect();
                    buf.push(Stmt::LocalDeclaration {
                        names,
                        values: Vec::new(),
                    });
                }

                let then_body = self.visit_region(then_branch);
                let else_body = else_branch.as_ref().map(|e| self.visit_region(e));

                buf.push(Stmt::If {
                    condition: self.visit_expr(condition),
                    then_body,
                    else_body,
                });
            }
            RegionNode::While {
                condition, body, ..
            } => {
                let body = self.visit_region(body);
                buf.push(Stmt::While {
                    condition: self.visit_expr(condition),
                    body,
                });
            }
            RegionNode::NumericFor {
                body,
                var,
                start,
                end,
                step,
                ..
            } => {
                self.scopes.declare(*var, ());
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
                })
            }
            RegionNode::GenericFor {
                vars, exprs, body, ..
            } => {
                for &var in vars {
                    self.scopes.declare(var, ());
                }
                let vars = vars.iter().map(|s| self.get_symbol_name(s)).collect();
                let exprs = exprs.iter().map(|expr| self.visit_expr(expr)).collect();
                let body = self.visit_region(body);
                buf.push(Stmt::GenericFor { vars, exprs, body });
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
            buf.push(self.visit_stmt(stmt));
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

        self.scopes.declare(*sym, ());
        let name = self.get_symbol_name(sym);
        buf.push(Stmt::LocalDeclaration {
            names: vec![name],
            values: Vec::new(),
        });
    }

    fn collect_assigned_symbols_in_region(&self, node: &RegionNode, out: &mut HashSet<SymbolId>) {
        match node {
            RegionNode::BasicBlock { stmts } => {
                for stmt in stmts {
                    self.collect_assigned_symbols_in_stmt(stmt, out);
                }
            }
            RegionNode::Sequence { nodes } => {
                for n in nodes {
                    self.collect_assigned_symbols_in_region(n, out);
                }
            }
            RegionNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_assigned_symbols_in_region(then_branch, out);
                if let Some(else_branch) = else_branch {
                    self.collect_assigned_symbols_in_region(else_branch, out);
                }
            }
            RegionNode::While { body, .. }
            | RegionNode::NumericFor { body, .. }
            | RegionNode::GenericFor { body, .. } => {
                self.collect_assigned_symbols_in_region(body, out);
            }
            RegionNode::Continue | RegionNode::Break | RegionNode::Return { .. } => {}
        }
    }

    fn collect_assigned_symbols_in_stmt(&self, stmt: &HilStmt, out: &mut HashSet<SymbolId>) {
        match stmt {
            HilStmt::Assign {
                left: HilExpr::Symbol(sym),
                ..
            } => {
                out.insert(*sym);
            }
            HilStmt::Assign { .. }
            | HilStmt::SetList { .. }
            | HilStmt::Call(_)
            | HilStmt::Phi(_) => {}
            HilStmt::AssignMany { left, .. } => {
                for lvalue in left {
                    if let HilExpr::Symbol(sym) = lvalue {
                        out.insert(*sym);
                    }
                }
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &HilStmt) -> Stmt {
        match stmt {
            HilStmt::Assign { left, value } => {
                let mut needs_declaration = false;
                let left_expr = match left {
                    HilExpr::Symbol(sym) => {
                        if !self.scopes.contains(sym) {
                            self.scopes.declare(*sym, ());
                            needs_declaration = true;
                        }
                        Expr::Named(self.get_symbol_name(sym))
                    }
                    _ => self.visit_expr(left),
                };
                let right = self.visit_expr(value);

                if needs_declaration {
                    let Expr::Named(name) = left_expr else {
                        unreachable!("Symbol was not visited as Named");
                    };
                    Stmt::LocalDeclaration {
                        names: vec![name],
                        values: vec![right],
                    }
                } else {
                    if let Expr::Binary { lhs, op, rhs } = &right
                        && lhs.as_ref() == &left_expr
                        && op.is_compound()
                    {
                        return Stmt::CompoundAssignment {
                            lhs: left_expr,
                            op: (*op).into(),
                            rhs: rhs.as_ref().clone(),
                        };
                    }

                    Stmt::Assignment {
                        lhs: vec![left_expr],
                        rhs: vec![right],
                    }
                }
            }
            HilStmt::AssignMany { left, value } => {
                let right = self.visit_expr(value);
                if left
                    .iter()
                    .any(|lvalue| !matches!(lvalue, HilExpr::Symbol(_)))
                {
                    let lhs = left.iter().map(|lvalue| self.visit_expr(lvalue)).collect();
                    return Stmt::Assignment {
                        lhs,
                        rhs: vec![right],
                    };
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

                let all_declared = symbols.iter().all(|sym| self.scopes.contains(sym));

                let names: Vec<_> = symbols
                    .iter()
                    .map(|sym| self.get_symbol_name(sym))
                    .collect();

                if all_declared {
                    Stmt::Assignment {
                        lhs: names.into_iter().map(Expr::Named).collect(),
                        rhs: vec![right],
                    }
                } else {
                    for sym in &symbols {
                        self.scopes.declare(*sym, ());
                    }
                    Stmt::LocalDeclaration {
                        names,
                        values: vec![right],
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
                    Stmt::Do {
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
                    }
                } else {
                    let base = *index as usize;
                    let lhs = (base..base + values.len())
                        .map(|i| Expr::Index {
                            base: Box::new(table_expr.clone()),
                            index: Box::new(Expr::Literal(Literal::Number(i as f64))),
                        })
                        .collect();
                    let rhs = values.iter().map(|v| self.visit_expr(v)).collect();

                    Stmt::Assignment { lhs, rhs }
                }
            }
            HilStmt::Call(expr) => Stmt::Expression {
                expr: self.visit_expr(expr),
            },
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
            HilExpr::Symbol(sym) => {
                if !self.scopes.contains(sym) {
                    panic!(
                        "encountered undeclared symbol read during structuring: proto={}, symbol={}",
                        self.current_proto_idx(),
                        sym.index()
                    );
                }
                Expr::Named(self.get_symbol_name(sym))
            }
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
                HilTableItem::Index(key, value) => TableItem::Indexed {
                    index: self.visit_expr(key),
                    value: self.visit_expr(value),
                },
            })
            .collect()
    }

    fn visit_closure(&mut self, proto_idx: usize, captures: &[SymbolId]) -> Expr {
        let parent_names: Vec<_> = captures
            .iter()
            .map(|sym| self.get_symbol_name(sym))
            .collect();

        let child_ctx = self.create_context(proto_idx);
        let child_upvalues = self.functions[proto_idx].cfg.upvalues.clone();
        for (i, name) in parent_names.into_iter().enumerate() {
            if let Some(&child_upval_sym) = child_upvalues.get(i) {
                self.reserve_symbol_name_exact(child_ctx, child_upval_sym, name.0);
            }
        }

        let old_scopes = std::mem::take(&mut self.scopes);

        let param_symbols = self.functions[proto_idx].cfg.params.clone();
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
}

fn is_valid_luau_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    let mut chars = s.chars();
    let first = chars.next().unwrap();

    // 1. Must start with a letter or underscore
    if !first.is_ascii_alphabetic() && first != '_' {
        return false;
    }

    // 2. Remaining characters must be alphanumeric or underscore
    for c in chars {
        if !c.is_ascii_alphanumeric() && c != '_' {
            return false;
        }
    }

    // 3. Must not be a strict reserved keyword
    const KEYWORDS: [&str; 21] = [
        "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in",
        "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while",
    ];
    !KEYWORDS.contains(&s)
}

pub fn structure(functions: Vec<StructuredFunction>, entry: usize) -> Block {
    let mut st = Structurer {
        functions,
        entry,
        scopes: Scopes::new(),
        contexts: Vec::new(),
        current_ctx: 0,
    };

    st.visit_entry()
}
