use std::collections::{HashMap, HashSet};

use crate::{
    ast::{Block, Expr, Identifier, Literal, Parameter, Stmt, UnOp},
    disasm::Proto,
    hil::{
        BlockExit, ControlFlowGraph, Expr as HilExpr, Stmt as HilStmt, find_if_else_join,
        resolve_generic_for_tail, resolve_numeric_for_tail,
    },
    logging::verbose_enabled,
    scopes::{ScopeManager, Var},
};

const MAX_PROTO_RECURSION_DEPTH: usize = 128;
const MAX_REGION_CALL_DEPTH: usize = 4096;

struct HilWalker<'a> {
    cfgs: &'a [ControlFlowGraph],
    protos: &'a [Proto],

    scopes: ScopeManager,
    /// A list of upvalues in the current function.
    upvals: Vec<Expr>,
    /// Per-function mapping from register -> printable local name.
    local_names: HashMap<u8, Identifier>,
    /// Names that cannot be reused (locals and referenced upvalue names).
    used_names: HashSet<Identifier>,
    /// Active proto expansion stack while structuring nested closures.
    active_proto_stack: Vec<usize>,
    /// Active structure-region calls to detect recursive region expansion.
    active_regions: HashSet<(usize, usize, Option<usize>)>,
    /// Depth of recursive `structure_region` calls.
    region_call_depth: usize,
}

impl<'a> HilWalker<'a> {
    /// When both `if` branches introduce the same synthetic local, hoist the declaration so
    /// later statements can legally reference that name after the conditional merge.
    fn hoist_matching_branch_local(
        &mut self,
        outer_stmts: &mut Vec<Stmt>,
        then_stmts: &mut [Stmt],
        else_stmts: &mut [Stmt],
    ) {
        let Some((then_name, then_value)) = Self::single_local_decl(then_stmts.first()) else {
            return;
        };
        let Some((else_name, else_value)) = Self::single_local_decl(else_stmts.first()) else {
            return;
        };
        if then_name != else_name || self.scopes.get_var(&then_name).is_some() {
            return;
        }

        let scope = self
            .scopes
            .top_scope()
            .expect("there should always be a scope");
        scope.add_var(Var::new(then_name.clone(), None));
        outer_stmts.push(Stmt::LocalDeclaration {
            names: vec![then_name.clone()],
            values: Vec::new(),
        });

        if let Some(first) = then_stmts.first_mut() {
            *first = Stmt::Assignment {
                lhs: Expr::Name(then_name.clone()),
                rhs: then_value,
            };
        }
        if let Some(first) = else_stmts.first_mut() {
            *first = Stmt::Assignment {
                lhs: Expr::Name(then_name),
                rhs: else_value,
            };
        }
    }

    #[inline]
    fn single_local_decl(stmt: Option<&Stmt>) -> Option<(Identifier, Expr)> {
        match stmt? {
            Stmt::LocalDeclaration { names, values } if names.len() == 1 && values.len() == 1 => {
                Some((names[0].clone(), values[0].clone()))
            }
            _ => None,
        }
    }

    /// Returns true when `block` dominates one of its predecessors, which we treat as a loop header.
    fn is_loop_header(&self, block: usize, cfg: &ControlFlowGraph) -> bool {
        cfg.predecessors(block)
            .iter()
            .copied()
            .any(|pred| pred != block && cfg.dominates(block, pred))
    }

    /// Returns a stable fallback identifier for an upvalue register index.
    #[inline]
    fn upvalue_ident(up: u8) -> Identifier {
        Identifier::from(format!("_up{}", up))
    }

    /// Resolves an upvalue expression in the current function context.
    #[inline]
    fn resolve_upvalue_expr(&self, up: u8) -> Expr {
        self.upvals
            .get(up as usize)
            .cloned()
            .unwrap_or_else(|| Expr::Name(Self::upvalue_ident(up)))
    }

    /// Reserves names referenced by captured upvalues so locals don't shadow them.
    fn reserve_upvalue_names(&mut self) {
        for upval in &self.upvals {
            if let Expr::Name(name) = upval {
                self.used_names.insert(name.clone());
            }
        }
    }

    /// Returns a stable printable local identifier for a register in this function.
    fn local_ident(&mut self, reg: u8) -> Identifier {
        if let Some(existing) = self.local_names.get(&reg) {
            return existing.clone();
        }

        let mut candidate = Identifier::from(format!("v{}", reg));
        if self.used_names.contains(&candidate) {
            let mut suffix = 0usize;
            loop {
                let alt = Identifier::from(format!("v{}_l{}", reg, suffix));
                if !self.used_names.contains(&alt) {
                    candidate = alt;
                    break;
                }
                suffix += 1;
            }
        }

        self.used_names.insert(candidate.clone());
        self.local_names.insert(reg, candidate.clone());
        candidate
    }

    /// Walks a HIL statement and translates it into an AST statement.
    fn walk_stmt(&mut self, stmt: HilStmt) -> Stmt {
        match stmt {
            HilStmt::Assign { left, value } => {
                // local, global, upval, getindex
                match left {
                    HilExpr::Local(reg) => {
                        let ident = self.local_ident(reg);
                        match self.scopes.get_var(&ident) {
                            Some(_) => Stmt::Assignment {
                                lhs: Expr::Name(ident),
                                rhs: self.walk_expr(value),
                            },
                            None => {
                                let scope = self
                                    .scopes
                                    .top_scope()
                                    .expect("there should always be a scope");
                                scope.add_var(Var::new(ident.clone(), None));
                                Stmt::LocalDeclaration {
                                    names: vec![ident],
                                    values: vec![self.walk_expr(value)],
                                }
                            }
                        }
                    }
                    HilExpr::Global(name) => Stmt::Assignment {
                        lhs: Expr::Name(name.into()),
                        rhs: self.walk_expr(value),
                    },
                    HilExpr::Upval(up) => Stmt::Assignment {
                        lhs: self.resolve_upvalue_expr(up),
                        rhs: self.walk_expr(value),
                    },
                    HilExpr::GetIndex(table, index) => Stmt::Assignment {
                        lhs: Expr::Index {
                            base: Box::new(self.walk_expr(*table)),
                            index: Box::new(self.walk_expr(*index)),
                        },
                        rhs: self.walk_expr(value),
                    },
                    _ => unreachable!(),
                }
            }
            HilStmt::AssignMany { left, value } => {
                let idents: Vec<_> = left
                    .into_iter()
                    .map(|expr| match expr {
                        HilExpr::Local(reg) => self.local_ident(reg),
                        _ => unreachable!(),
                    })
                    .collect();

                let scope = self
                    .scopes
                    .top_scope()
                    .expect("there should always be a scope");
                scope.add_vars(idents.iter().map(|id| Var::new(id.clone(), None)));

                Stmt::LocalDeclaration {
                    names: idents,
                    values: vec![self.walk_expr(value)],
                }
            }
            HilStmt::Call { expr, args } => {
                let expr = self.walk_expr(expr);
                let args: Vec<_> = args.into_iter().map(|arg| self.walk_expr(arg)).collect();
                debug_assert!(
                    match &expr {
                        Expr::FunctionCall {
                            args: expr_args, ..
                        }
                        | Expr::MethodCall {
                            args: expr_args, ..
                        } => expr_args == &args,
                        _ => args.is_empty(),
                    },
                    "HilStmt::Call must carry a call expression consistent with args"
                );
                Stmt::Expression { expr }
            }
            HilStmt::SetField { table, key, value } => Stmt::Assignment {
                lhs: Expr::Index {
                    base: Box::new(Expr::Name(self.local_ident(table))),
                    index: Box::new(Expr::Literal(Literal::String(key.into()))),
                },
                rhs: self.walk_expr(value),
            },
            HilStmt::Return(exprs) => Stmt::Return {
                values: exprs.into_iter().map(|arg| self.walk_expr(arg)).collect(),
            },
        }
    }

    /// Walks a HIL expression and translates it into an AST expression.
    fn walk_expr(&mut self, expr: HilExpr) -> Expr {
        match expr {
            HilExpr::Nil => Expr::Literal(Literal::Nil),
            HilExpr::Number(num) => Expr::Literal(Literal::Number(num)),
            HilExpr::String(str) => Expr::Literal(Literal::String(str.into())),
            HilExpr::Bool(b) => Expr::Literal(Literal::Bool(b)),
            HilExpr::Local(reg) => Expr::Name(self.local_ident(reg)),
            HilExpr::Global(name) => Expr::Name(name.into()),
            HilExpr::Upval(up) => self.resolve_upvalue_expr(up),
            HilExpr::Closure {
                proto: proto_idx,
                captures,
            } => {
                let Some(proto) = self.protos.get(proto_idx) else {
                    return Expr::AnonymousFunction {
                        params: Vec::new(),
                        body: Block::new(),
                    };
                };
                let mapped_captures: Vec<Expr> =
                    captures.into_iter().map(|c| self.walk_expr(c)).collect();

                if self.active_proto_stack.contains(&proto_idx) {
                    if verbose_enabled() {
                        eprintln!(
                            "[structure] recursive proto closure detected: stack={:?}, next={}",
                            self.active_proto_stack, proto_idx
                        );
                    }
                    return Expr::AnonymousFunction {
                        params: (0..proto.num_params)
                            .map(|i| Parameter::Regular(Identifier::from(format!("v{}", i))))
                            .chain(proto.is_vararg.then_some(Parameter::Vararg))
                            .collect(),
                        body: Block::new(),
                    };
                }
                if self.active_proto_stack.len() >= MAX_PROTO_RECURSION_DEPTH {
                    if verbose_enabled() {
                        eprintln!(
                            "[structure] proto recursion depth limit reached ({}), refusing to descend into proto {}",
                            MAX_PROTO_RECURSION_DEPTH, proto_idx
                        );
                    }
                    return Expr::AnonymousFunction {
                        params: (0..proto.num_params)
                            .map(|i| Parameter::Regular(Identifier::from(format!("v{}", i))))
                            .chain(proto.is_vararg.then_some(Parameter::Vararg))
                            .collect(),
                        body: Block::new(),
                    };
                }

                if verbose_enabled() {
                    eprintln!(
                        "[structure] enter closure proto {} (captures={}, parent_stack={:?})",
                        proto_idx,
                        mapped_captures.len(),
                        self.active_proto_stack
                    );
                }
                let prev_upvalues = std::mem::replace(&mut self.upvals, mapped_captures);
                let prev_local_names = std::mem::take(&mut self.local_names);
                let prev_used_names = std::mem::take(&mut self.used_names);
                let prev_scopes = self.scopes.clone();

                self.reserve_upvalue_names();

                let Some(cfg) = self.cfgs.get(proto_idx) else {
                    self.used_names = prev_used_names;
                    self.local_names = prev_local_names;
                    self.scopes = prev_scopes;
                    self.upvals = prev_upvalues;
                    return Expr::AnonymousFunction {
                        params: (0..proto.num_params)
                            .map(|i| Parameter::Regular(Identifier::from(format!("v{}", i))))
                            .chain(proto.is_vararg.then_some(Parameter::Vararg))
                            .collect(),
                        body: Block::new(),
                    };
                };

                let mut params: Vec<_> = (0..proto.num_params)
                    .map(|i| Parameter::Regular(self.local_ident(i)))
                    .collect();
                if proto.is_vararg {
                    params.push(Parameter::Vararg);
                }

                self.active_proto_stack.push(proto_idx);
                let param_scope: Vec<Var> = params
                    .iter()
                    .filter_map(|param| match param {
                        Parameter::Regular(name) => Some(Var::new(name.clone(), None)),
                        Parameter::Vararg => None,
                    })
                    .collect();
                self.scopes.push_scope_with(param_scope);

                let stmts = self.structure_region(cfg.entry_block, None, cfg);
                let body = Block::with_stmts(stmts);

                self.scopes.pop_scope();
                self.active_proto_stack.pop();
                self.used_names = prev_used_names;
                self.local_names = prev_local_names;
                self.scopes = prev_scopes;
                self.upvals = prev_upvalues;

                if verbose_enabled() {
                    eprintln!("[structure] exit closure proto {}", proto_idx);
                }

                Expr::AnonymousFunction { params, body }
            }
            // this is a hack but the import thing is just really retarded
            HilExpr::Import(im) => Expr::Name(im.into()),
            HilExpr::GetField(base, field) => Expr::Field {
                base: Box::new(self.walk_expr(*base)),
                field: Identifier::from(field),
            },
            HilExpr::GetIndex(base, index) => Expr::Index {
                base: Box::new(self.walk_expr(*base)),
                index: Box::new(self.walk_expr(*index)),
            },
            HilExpr::Call(fun, args) => Expr::FunctionCall {
                func: Box::new(self.walk_expr(*fun)),
                args: args.into_iter().map(|arg| self.walk_expr(arg)).collect(),
            },
            HilExpr::MethodCall(base, method, args) => Expr::MethodCall {
                object: Box::new(self.walk_expr(*base)),
                method: Identifier::from(method),
                args: args.into_iter().map(|arg| self.walk_expr(arg)).collect(),
            },
            HilExpr::Binary(op, left, right) => Expr::Binary {
                lhs: Box::new(self.walk_expr(*left)),
                op,
                rhs: Box::new(self.walk_expr(*right)),
            },
            HilExpr::Unary(op, expr) => Expr::Unary {
                op,
                expr: Box::new(self.walk_expr(*expr)),
            },
            HilExpr::Table(_) => Expr::Table { fields: Vec::new() },
        }
    }

    /// Structures a linear CFG region into AST statements.
    ///
    /// `stop_at` is an optional exclusive block boundary used when a parent construct has
    /// already identified the region merge point. Loop headers and back-edges are handled
    /// here so the caller can recurse on plain block ids instead of a richer region type.
    fn structure_region(
        &mut self,
        current: usize,
        stop_at: Option<usize>,
        cfg: &ControlFlowGraph,
    ) -> Vec<Stmt> {
        let current_proto = self
            .active_proto_stack
            .last()
            .copied()
            .unwrap_or(usize::MAX);
        let region_key = (current_proto, current, stop_at);
        if !self.active_regions.insert(region_key) {
            if verbose_enabled() {
                eprintln!(
                    "[structure] recursive region detected for proto={}, block={}, stop_at={:?}; skipping nested expansion",
                    current_proto, current, stop_at
                );
            }
            return Vec::new();
        }
        self.region_call_depth += 1;
        if self.region_call_depth > MAX_REGION_CALL_DEPTH {
            if verbose_enabled() {
                eprintln!(
                    "[structure] region call depth exceeded {} at proto={}, block={}, stop_at={:?}; aborting branch",
                    MAX_REGION_CALL_DEPTH, current_proto, current, stop_at
                );
            }
            self.region_call_depth -= 1;
            self.active_regions.remove(&region_key);
            return Vec::new();
        }

        let mut stmts = Vec::new();
        let mut curr_id = current;
        let mut visited_in_region = HashSet::new();
        let mut block_stmt_starts = HashMap::new();
        let is_loop_header = self.is_loop_header(current, cfg);

        self.scopes.push_scope();

        if verbose_enabled() {
            let current_proto = self.active_proto_stack.last().copied();
            eprintln!(
                "[structure] region start proto={:?} block={} stop_at={:?}",
                current_proto, current, stop_at
            );
        }

        // Keep walking until we hit the stop block, or run out of graph
        while Some(curr_id) != stop_at && curr_id < cfg.blocks.len() {
            if curr_id != current && self.is_loop_header(curr_id, cfg) {
                stmts.extend(self.structure_region(curr_id, stop_at, cfg));
                break;
            }

            if !visited_in_region.insert(curr_id) {
                if curr_id == current && !stmts.is_empty() {
                    let body = std::mem::take(&mut stmts);
                    stmts.push(Stmt::While {
                        condition: Expr::Literal(Literal::Bool(true)),
                        body: Block::with_stmts(body),
                    });
                }
                if verbose_enabled() {
                    let current_proto = self.active_proto_stack.last().copied();
                    eprintln!(
                        "[structure] region loop detected in proto={:?}, revisiting block {} (stop_at={:?}); aborting region walk",
                        current_proto, curr_id, stop_at
                    );
                }
                break;
            }

            let block = &cfg.blocks[curr_id];
            block_stmt_starts.insert(curr_id, stmts.len());

            for hil_stmt in &block.stmts {
                stmts.push(self.walk_stmt(hil_stmt.clone()));
            }

            match &block.exit {
                BlockExit::Fallthrough(next) | BlockExit::Jump(next) => {
                    if *next < current && cfg.dominates(*next, curr_id) {
                        stmts.push(Stmt::Continue);
                        break;
                    }
                    if *next < curr_id
                        && visited_in_region.contains(next)
                        && cfg.dominates(*next, curr_id)
                        && let Some(&loop_stmt_start) = block_stmt_starts.get(next)
                    {
                        let body = stmts.split_off(loop_stmt_start);
                        stmts.push(Stmt::While {
                            condition: Expr::Literal(Literal::Bool(true)),
                            body: Block::with_stmts(body),
                        });
                        break;
                    }
                    curr_id = *next;
                }

                BlockExit::CondJump {
                    cond,
                    then_block,
                    else_block,
                } => {
                    let merge_block = find_if_else_join(*then_block, *else_block, cfg);
                    if verbose_enabled() {
                        let current_proto = self.active_proto_stack.last().copied();
                        eprintln!(
                            "[structure] condjump proto={:?} block={} then={} else={} merge={:?}",
                            current_proto, curr_id, then_block, else_block, merge_block
                        );
                    }
                    let then_stmts = self.structure_region(*then_block, merge_block, cfg);
                    let else_stmts = self.structure_region(*else_block, merge_block, cfg);
                    let mut then_stmts = then_stmts;
                    let mut else_stmts = else_stmts;
                    self.hoist_matching_branch_local(&mut stmts, &mut then_stmts, &mut else_stmts);
                    if then_stmts.is_empty() && else_stmts.is_empty() {
                        if let Some(m) = merge_block {
                            curr_id = m;
                            continue;
                        }
                        break;
                    }
                    let mut condition = self.walk_expr(cond.clone());
                    if then_stmts.is_empty() && !else_stmts.is_empty() {
                        condition = Expr::Unary {
                            op: UnOp::Not,
                            expr: Box::new(condition),
                        };
                        std::mem::swap(&mut then_stmts, &mut else_stmts);
                    }
                    stmts.push(Stmt::If {
                        condition,
                        then_body: Block::with_stmts(then_stmts),
                        else_body: if else_stmts.is_empty() {
                            None
                        } else {
                            Some(Block::with_stmts(else_stmts))
                        },
                    });

                    if let Some(m) = merge_block {
                        curr_id = m;
                    } else {
                        break;
                    }
                }

                BlockExit::ForNPrep { base, loop_block } => {
                    let bounds = resolve_numeric_for_tail(curr_id, *base, *loop_block, cfg);

                    if let Some((_tail_block, body_block, exit_block)) = bounds {
                        let body_stmts = self.structure_region(body_block, Some(exit_block), cfg);

                        stmts.push(Stmt::NumericFor {
                            var: self.local_ident(*base as u8 + 2),
                            start: Expr::Name(self.local_ident(*base as u8 + 2)),
                            end: Expr::Name(self.local_ident(*base as u8)),
                            step: None,
                            body: Block::with_stmts(body_stmts),
                        });

                        curr_id = exit_block;
                    } else {
                        eprintln!("Couldn't resolve ForNPrep, block_id = {}", curr_id);
                        curr_id = *loop_block;
                    }
                }

                BlockExit::ForGPrep { base, loop_block } => {
                    let bounds = resolve_generic_for_tail(curr_id, *base, *loop_block, cfg);

                    if let Some((_tail_block, body_block, exit_block, result_count)) = bounds {
                        let mut iter_expr = Expr::Name(self.local_ident(*base as u8));

                        if let Some(HilStmt::AssignMany { left, value }) = block.stmts.last() {
                            if let Some(HilExpr::Local(reg)) = left.first() {
                                if *reg as usize == *base {
                                    iter_expr = self.walk_expr(value.clone());

                                    // CRITICAL: We already translated this statement and pushed it to `stmts`
                                    // at the start of the while loop. We must pop it so we don't emit
                                    // `local v0, v1, v2 = pairs(t)` right before the `for` loop!
                                    stmts.pop();
                                }
                            }
                        }

                        // A generic for loop's block variables start at `base + 3`.
                        let mut vars: Vec<_> = (0..result_count)
                            .map(|i| self.local_ident(*base as u8 + 3 + i as u8))
                            .collect();
                        if vars.is_empty() {
                            vars.push(Identifier::from("_"));
                        }

                        let body_stmts = self.structure_region(body_block, Some(exit_block), cfg);
                        stmts.push(Stmt::GenericFor {
                            vars,
                            exprs: vec![iter_expr],
                            body: Block::with_stmts(body_stmts),
                        });

                        // 6. Continue from the exit block
                        curr_id = exit_block;
                    } else {
                        eprintln!("Couldn't resolve ForGPrep, block_id = {}", curr_id);
                        curr_id = *loop_block;
                    }
                }

                BlockExit::Return(exprs) => {
                    stmts.push(Stmt::Return {
                        values: exprs.iter().map(|e| self.walk_expr(e.clone())).collect(),
                    });
                    break;
                }

                BlockExit::ForNLoop { .. } | BlockExit::ForGLoop { .. } => {
                    break;
                }
            }
        }

        if is_loop_header && !stmts.is_empty() && !matches!(stmts.as_slice(), [Stmt::While { .. }])
        {
            stmts = vec![Stmt::While {
                condition: Expr::Literal(Literal::Bool(true)),
                body: Block::with_stmts(stmts),
            }];
        }

        self.scopes.pop_scope();
        self.region_call_depth -= 1;
        self.active_regions.remove(&region_key);
        stmts
    }
}

/// Takes a control flow graph and produces a structured block of statements.
pub fn structure(cfgs: &[ControlFlowGraph], entry_proto: usize, protos: &[Proto]) -> Block {
    if cfgs.is_empty() {
        return Block::new();
    }

    let entry_proto = entry_proto.min(cfgs.len() - 1);
    let mut walker = HilWalker {
        cfgs,
        protos,
        scopes: ScopeManager::new(),
        upvals: Vec::new(),
        local_names: HashMap::new(),
        used_names: HashSet::new(),
        active_proto_stack: vec![entry_proto],
        active_regions: HashSet::new(),
        region_call_depth: 0,
    };
    if verbose_enabled() {
        eprintln!("[structure] start entry proto {}", entry_proto);
    }
    let cfg = &walker.cfgs[entry_proto];
    let root_stmts = walker.structure_region(cfg.entry_block, None, cfg);
    if verbose_enabled() {
        eprintln!("[structure] finished entry proto {}", entry_proto);
    }
    Block::with_stmts(root_stmts)
}

#[cfg(test)]
mod tests {
    use super::structure;
    use crate::{
        ast::{Expr as AstExpr, Stmt as AstStmt},
        disasm::Proto,
        hil::{Block as HilBlock, BlockExit, ControlFlowGraph, Expr as HilExpr, Stmt as HilStmt},
    };

    #[test]
    fn structure_call_stmt_does_not_double_wrap_function_call() {
        let cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![HilStmt::Call {
                    expr: HilExpr::Call(
                        Box::new(HilExpr::Local(4)),
                        vec![HilExpr::Local(5), HilExpr::Local(6)],
                    ),
                    args: vec![HilExpr::Local(5), HilExpr::Local(6)],
                }],
                exit: BlockExit::Return(vec![]),
            }],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        assert_eq!(ast.stmts.len(), 2);

        match &ast.stmts[0] {
            AstStmt::Expression { expr } => match expr {
                AstExpr::FunctionCall { func, args } => {
                    assert!(matches!(func.as_ref(), AstExpr::Name(name) if name.as_str() == "v4"));
                    assert_eq!(args.len(), 2);
                    assert!(matches!(&args[0], AstExpr::Name(name) if name.as_str() == "v5"));
                    assert!(matches!(&args[1], AstExpr::Name(name) if name.as_str() == "v6"));
                }
                _ => panic!("expected function-call expression"),
            },
            _ => panic!("expected expression statement"),
        }

        match &ast.stmts[1] {
            AstStmt::Return { values } => assert!(values.is_empty()),
            _ => panic!("expected empty return from block exit"),
        }
    }

    #[test]
    fn structure_upvalue_assignment_uses_fallback_upvalue_name() {
        let cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![HilStmt::Assign {
                    left: HilExpr::Upval(2),
                    value: HilExpr::Global("ipairs".to_string()),
                }],
                exit: BlockExit::Return(vec![]),
            }],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        assert_eq!(ast.stmts.len(), 2);

        match &ast.stmts[0] {
            AstStmt::Assignment { lhs, rhs } => {
                assert!(matches!(lhs, AstExpr::Name(name) if name.as_str() == "_up2"));
                assert!(matches!(rhs, AstExpr::Name(name) if name.as_str() == "ipairs"));
            }
            _ => panic!("expected assignment statement"),
        }
    }

    #[test]
    fn structure_closure_scope_isolated_and_upvalue_write_does_not_shadow_locals() {
        let parent_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![
                    HilStmt::Assign {
                        left: HilExpr::Local(2),
                        value: HilExpr::Number(0.0),
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(4),
                        value: HilExpr::Closure {
                            proto: 1,
                            captures: vec![HilExpr::Local(2)],
                        },
                    },
                ],
                exit: BlockExit::Return(vec![]),
            }],
            0,
        );

        let child_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![
                    HilStmt::Assign {
                        left: HilExpr::Local(2),
                        value: HilExpr::Global("ipairs".to_string()),
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(4),
                        value: HilExpr::Local(1),
                    },
                    HilStmt::Assign {
                        left: HilExpr::Upval(0),
                        value: HilExpr::Local(2),
                    },
                ],
                exit: BlockExit::Return(vec![]),
            }],
            0,
        );

        let mut parent_proto = Proto::default();
        parent_proto.num_params = 0;
        let mut child_proto = Proto::default();
        child_proto.num_params = 2;

        let ast = structure(&[parent_cfg, child_cfg], 0, &[parent_proto, child_proto]);
        assert_eq!(ast.stmts.len(), 3);

        let inner_body = match &ast.stmts[1] {
            AstStmt::LocalDeclaration { names, values } => {
                assert!(matches!(names.as_slice(), [name] if name.as_str() == "v4"));
                match values.as_slice() {
                    [AstExpr::AnonymousFunction { body, .. }] => body,
                    _ => panic!("expected closure assigned to v4"),
                }
            }
            _ => panic!("expected closure local declaration"),
        };

        assert_eq!(inner_body.stmts.len(), 4);
        assert!(matches!(
            &inner_body.stmts[0],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v2_l0")
                    && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "ipairs")
        ));
        assert!(matches!(
            &inner_body.stmts[1],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v4")
                    && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v1")
        ));
        assert!(matches!(
            &inner_body.stmts[2],
            AstStmt::Assignment { lhs, rhs }
                if matches!(lhs, AstExpr::Name(name) if name.as_str() == "v2")
                    && matches!(rhs, AstExpr::Name(name) if name.as_str() == "v2_l0")
        ));
    }

    #[test]
    fn structure_closure_params_do_not_shadow_captured_register_names() {
        let parent_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![
                    HilStmt::Assign {
                        left: HilExpr::Local(0),
                        value: HilExpr::Number(1.0),
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(1),
                        value: HilExpr::Closure {
                            proto: 1,
                            captures: vec![HilExpr::Local(0)],
                        },
                    },
                ],
                exit: BlockExit::Return(vec![]),
            }],
            0,
        );
        let child_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![HilStmt::Assign {
                    left: HilExpr::Local(2),
                    value: HilExpr::Upval(0),
                }],
                exit: BlockExit::Return(vec![HilExpr::Local(2)]),
            }],
            0,
        );

        let mut parent_proto = Proto::default();
        parent_proto.num_params = 0;
        let mut child_proto = Proto::default();
        child_proto.num_params = 2;

        let ast = structure(&[parent_cfg, child_cfg], 0, &[parent_proto, child_proto]);
        let (params, body) = match &ast.stmts[1] {
            AstStmt::LocalDeclaration { values, .. } => match values.as_slice() {
                [AstExpr::AnonymousFunction { params, body }] => (params, body),
                _ => panic!("expected closure value"),
            },
            _ => panic!("expected closure local declaration"),
        };

        assert!(matches!(
            params.as_slice(),
            [crate::ast::Parameter::Regular(a), crate::ast::Parameter::Regular(b)]
                if a.as_str() == "v0_l0" && b.as_str() == "v1"
        ));
        assert!(matches!(
            &body.stmts[0],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v2")
                    && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v0")
        ));
    }

    #[test]
    fn structure_hoists_branch_local_before_if_merge() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![],
                    exit: BlockExit::CondJump {
                        cond: HilExpr::Binary(
                            crate::ast::BinOp::Lt,
                            Box::new(HilExpr::Local(3)),
                            Box::new(HilExpr::Local(4)),
                        ),
                        then_block: 2,
                        else_block: 1,
                    },
                },
                HilBlock {
                    id: 1,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(2),
                        value: HilExpr::Bool(false),
                    }],
                    exit: BlockExit::Fallthrough(3),
                },
                HilBlock {
                    id: 2,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(2),
                        value: HilExpr::Bool(true),
                    }],
                    exit: BlockExit::Jump(3),
                },
                HilBlock {
                    id: 3,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![HilExpr::Local(2)]),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        assert!(matches!(
            &ast.stmts[0],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v2") && values.is_empty()
        ));

        match &ast.stmts[1] {
            AstStmt::If {
                then_body,
                else_body: Some(else_body),
                ..
            } => {
                assert!(matches!(
                    &then_body.stmts[0],
                    AstStmt::Assignment { lhs, rhs }
                        if matches!(lhs, AstExpr::Name(name) if name.as_str() == "v2")
                            && matches!(rhs, AstExpr::Literal(crate::ast::Literal::Bool(true)))
                ));
                assert!(matches!(
                    &else_body.stmts[0],
                    AstStmt::Assignment { lhs, rhs }
                        if matches!(lhs, AstExpr::Name(name) if name.as_str() == "v2")
                            && matches!(rhs, AstExpr::Literal(crate::ast::Literal::Bool(false)))
                ));
            }
            _ => panic!("expected if statement"),
        }
        assert!(matches!(
            &ast.stmts[2],
            AstStmt::Return { values }
                if matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v2")
        ));
    }

    #[test]
    fn structure_inverts_empty_then_branch_when_false_side_has_prelude() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![],
                    exit: BlockExit::CondJump {
                        cond: HilExpr::Local(0),
                        then_block: 2,
                        else_block: 1,
                    },
                },
                HilBlock {
                    id: 1,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Global("Seen".to_string()),
                        value: HilExpr::Local(1),
                    }],
                    exit: BlockExit::Fallthrough(2),
                },
                HilBlock {
                    id: 2,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![]),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        assert_eq!(ast.stmts.len(), 2);

        match &ast.stmts[0] {
            AstStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                assert!(else_body.is_none());
                assert!(matches!(
                    condition,
                    AstExpr::Unary {
                        op: crate::ast::UnOp::Not,
                        expr
                    } if matches!(expr.as_ref(), AstExpr::Name(name) if name.as_str() == "v0")
                ));
                assert!(matches!(
                    then_body.stmts.as_slice(),
                    [AstStmt::Assignment { lhs, rhs }]
                        if matches!(lhs, AstExpr::Name(name) if name.as_str() == "Seen")
                            && matches!(rhs, AstExpr::Name(name) if name.as_str() == "v1")
                ));
            }
            _ => panic!("expected inverted if statement"),
        }

        assert!(matches!(&ast.stmts[1], AstStmt::Return { values } if values.is_empty()));
    }

    #[test]
    fn structure_numeric_for_keeps_tail_block_body_and_register_order() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![
                        HilStmt::Assign {
                            left: HilExpr::Local(6),
                            value: HilExpr::Number(1.0),
                        },
                        HilStmt::Assign {
                            left: HilExpr::Local(4),
                            value: HilExpr::Local(2),
                        },
                        HilStmt::Assign {
                            left: HilExpr::Local(5),
                            value: HilExpr::Number(1.0),
                        },
                    ],
                    exit: BlockExit::ForNPrep {
                        base: 4,
                        loop_block: 1,
                    },
                },
                HilBlock {
                    id: 1,
                    stmts: vec![
                        HilStmt::Assign {
                            left: HilExpr::Local(7),
                            value: HilExpr::GetIndex(
                                Box::new(HilExpr::Local(1)),
                                Box::new(HilExpr::Local(6)),
                            ),
                        },
                        HilStmt::Assign {
                            left: HilExpr::Local(3),
                            value: HilExpr::Local(7),
                        },
                    ],
                    exit: BlockExit::ForNLoop {
                        base: 4,
                        body_block: 1,
                        exit_block: 2,
                    },
                },
                HilBlock {
                    id: 2,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![HilExpr::Local(3)]),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        match &ast.stmts[3] {
            AstStmt::NumericFor {
                var,
                start,
                end,
                body,
                ..
            } => {
                assert_eq!(var.as_str(), "v6");
                assert!(matches!(start, AstExpr::Name(name) if name.as_str() == "v6"));
                assert!(matches!(end, AstExpr::Name(name) if name.as_str() == "v4"));
                assert_eq!(body.stmts.len(), 2);
            }
            _ => panic!("expected numeric for"),
        }
    }

    #[test]
    fn structure_generic_for_keeps_linear_preheader_assignments() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![HilStmt::AssignMany {
                        left: vec![HilExpr::Local(4), HilExpr::Local(5), HilExpr::Local(6)],
                        value: HilExpr::Call(
                            Box::new(HilExpr::Global("ipairs".to_string())),
                            vec![HilExpr::Local(0)],
                        ),
                    }],
                    exit: BlockExit::ForGPrep {
                        base: 4,
                        loop_block: 3,
                    },
                },
                HilBlock {
                    id: 1,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(10),
                        value: HilExpr::Local(3),
                    }],
                    exit: BlockExit::Fallthrough(2),
                },
                HilBlock {
                    id: 2,
                    stmts: vec![HilStmt::Call {
                        expr: HilExpr::Call(
                            Box::new(HilExpr::Global("table.insert".to_string())),
                            vec![HilExpr::Local(10), HilExpr::Local(8)],
                        ),
                        args: vec![HilExpr::Local(10), HilExpr::Local(8)],
                    }],
                    exit: BlockExit::Fallthrough(3),
                },
                HilBlock {
                    id: 3,
                    stmts: vec![],
                    exit: BlockExit::ForGLoop {
                        base: 4,
                        body_block: 2,
                        exit_block: 4,
                        result_count: 2,
                    },
                },
                HilBlock {
                    id: 4,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![]),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        match &ast.stmts[0] {
            AstStmt::GenericFor { body, .. } => {
                assert_eq!(body.stmts.len(), 2);
                assert!(matches!(
                    &body.stmts[0],
                    AstStmt::LocalDeclaration { names, values }
                        if matches!(names.as_slice(), [name] if name.as_str() == "v10")
                            && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v3")
                ));
                assert!(matches!(
                    &body.stmts[1],
                    AstStmt::Expression {
                        expr: AstExpr::FunctionCall { args, .. }
                    } if matches!(args.as_slice(), [AstExpr::Name(a), AstExpr::Name(b)]
                        if a.as_str() == "v10" && b.as_str() == "v8")
                ));
            }
            _ => panic!("expected generic for"),
        }
    }

    #[test]
    fn structure_generic_for_keeps_preheader_condition_source() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![HilStmt::AssignMany {
                        left: vec![HilExpr::Local(2), HilExpr::Local(3), HilExpr::Local(4)],
                        value: HilExpr::Call(
                            Box::new(HilExpr::Global("pairs".to_string())),
                            vec![HilExpr::Global("DEFAULT_CONFIG".to_string())],
                        ),
                    }],
                    exit: BlockExit::ForGPrep {
                        base: 2,
                        loop_block: 4,
                    },
                },
                HilBlock {
                    id: 1,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(7),
                        value: HilExpr::GetIndex(
                            Box::new(HilExpr::Local(1)),
                            Box::new(HilExpr::Local(5)),
                        ),
                    }],
                    exit: BlockExit::Fallthrough(2),
                },
                HilBlock {
                    id: 2,
                    stmts: vec![],
                    exit: BlockExit::CondJump {
                        cond: HilExpr::Local(7),
                        then_block: 4,
                        else_block: 3,
                    },
                },
                HilBlock {
                    id: 3,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::GetIndex(
                            Box::new(HilExpr::Local(1)),
                            Box::new(HilExpr::Local(5)),
                        ),
                        value: HilExpr::Local(6),
                    }],
                    exit: BlockExit::Fallthrough(4),
                },
                HilBlock {
                    id: 4,
                    stmts: vec![],
                    exit: BlockExit::ForGLoop {
                        base: 2,
                        body_block: 2,
                        exit_block: 5,
                        result_count: 2,
                    },
                },
                HilBlock {
                    id: 5,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![]),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        match &ast.stmts[0] {
            AstStmt::GenericFor { body, .. } => {
                assert_eq!(body.stmts.len(), 2);
                assert!(matches!(
                    &body.stmts[0],
                    AstStmt::LocalDeclaration { names, values }
                        if matches!(names.as_slice(), [name] if name.as_str() == "v7")
                            && matches!(values.as_slice(), [AstExpr::Index { .. }])
                ));
                assert!(matches!(
                    &body.stmts[1],
                    AstStmt::If { condition, .. }
                        if matches!(condition, AstExpr::Unary { op: crate::ast::UnOp::Not, expr }
                            if matches!(expr.as_ref(), AstExpr::Name(name) if name.as_str() == "v7"))
                ));
            }
            _ => panic!("expected generic for"),
        }
    }

    #[test]
    fn structure_wraps_backedge_as_while_true() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(0),
                        value: HilExpr::Number(1.0),
                    }],
                    exit: BlockExit::Fallthrough(1),
                },
                HilBlock {
                    id: 1,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(1),
                        value: HilExpr::Number(2.0),
                    }],
                    exit: BlockExit::Jump(0),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        assert_eq!(ast.stmts.len(), 1);

        match &ast.stmts[0] {
            AstStmt::While { condition, body } => {
                assert!(matches!(
                    condition,
                    AstExpr::Literal(crate::ast::Literal::Bool(true))
                ));
                assert_eq!(body.stmts.len(), 2);
            }
            _ => panic!("expected while loop"),
        }
    }
}
