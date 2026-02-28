use std::collections::{HashMap, HashSet};

use crate::{
    ast::{Block, Expr, Identifier, Literal, Parameter, Stmt},
    disasm::Proto,
    hil::{
        Block as HilBlock, BlockExit, ControlFlowGraph, Expr as HilExpr, Stmt as HilStmt,
        find_if_else_join, resolve_generic_for_tail, resolve_numeric_for_tail,
    },
    logging::verbose_enabled,
};

const MAX_PROTO_RECURSION_DEPTH: usize = 128;
const MAX_REGION_CALL_DEPTH: usize = 4096;

#[derive(Debug)]
struct Var {
    name: Identifier,
}

#[derive(Debug)]
struct Scope {
    variables: Vec<Var>,
}

struct HilWalker<'a> {
    cfgs: &'a [ControlFlowGraph],
    protos: &'a [Proto],

    /// A stack of scopes.
    scopes: Vec<Scope>,
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

    /// Pushes a new scope onto the stack.
    #[inline]
    fn push_scope(&mut self) {
        self.scopes.push(Scope {
            variables: Vec::new(),
        });
    }

    /// Pushes a scope onto the stack with the given variables.
    #[inline]
    fn push_scope_with(&mut self, vars: Vec<Var>) {
        self.scopes.push(Scope { variables: vars });
    }

    /// Gets the current scope, if it exists.
    #[inline]
    fn top_scope(&mut self) -> Option<&mut Scope> {
        self.scopes.last_mut()
    }

    /// Pops the current scope from the stack.
    #[inline]
    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// Returns a variable from the current scope, if it exists.
    /// If one cannot be found in the current scope, it will search
    /// parent scopes until it finds one or exhausts all scopes.
    fn get_var(&self, name: &Identifier) -> Option<&Var> {
        for scope in self.scopes.iter().rev() {
            if let Some(var) = scope.variables.iter().find(|var| var.name == *name) {
                return Some(var);
            }
        }
        None
    }

    /// Walks a HIL statement and translates it into an AST statement.
    fn walk_stmt(&mut self, stmt: HilStmt) -> Stmt {
        match stmt {
            HilStmt::Assign { left, value } => {
                // local, global, upval, getindex
                match left {
                    HilExpr::Local(reg) => {
                        let ident = self.local_ident(reg);
                        match self.get_var(&ident) {
                            Some(_) => Stmt::Assignment {
                                lhs: Expr::Name(ident),
                                rhs: self.walk_expr(value),
                            },
                            None => {
                                let scope =
                                    self.top_scope().expect("there should always be a scope");
                                scope.variables.push(Var {
                                    name: ident.clone(),
                                });
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

                let scope = self.top_scope().expect("there should always be a scope");
                scope
                    .variables
                    .extend(idents.iter().map(|id| Var { name: id.clone() }));

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
                let mapped_captures: Vec<Expr> = captures
                    .into_iter()
                    .map(|c| self.walk_expr(c))
                    .collect();
                let mut params: Vec<_> = (0..proto.num_params)
                    .map(|i| Parameter::Regular(self.local_ident(i)))
                    .collect();
                if proto.is_vararg {
                    params.push(Parameter::Vararg);
                }

                if self.active_proto_stack.contains(&proto_idx) {
                    if verbose_enabled() {
                        eprintln!(
                            "[structure] recursive proto closure detected: stack={:?}, next={}",
                            self.active_proto_stack, proto_idx
                        );
                    }
                    return Expr::AnonymousFunction {
                        params,
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
                        params,
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
                let prev_scopes = std::mem::take(&mut self.scopes);
                let prev_local_names = std::mem::take(&mut self.local_names);
                let prev_used_names = std::mem::take(&mut self.used_names);

                self.reserve_upvalue_names();

                let Some(cfg) = self.cfgs.get(proto_idx) else {
                    self.used_names = prev_used_names;
                    self.local_names = prev_local_names;
                    self.scopes = prev_scopes;
                    self.upvals = prev_upvalues;
                    return Expr::AnonymousFunction {
                        params,
                        body: Block::new(),
                    };
                };

                self.active_proto_stack.push(proto_idx);
                let param_scope: Vec<Var> = params
                    .iter()
                    .filter_map(|param| match param {
                        Parameter::Regular(name) => Some(Var { name: name.clone() }),
                        Parameter::Vararg => None,
                    })
                    .collect();
                self.push_scope_with(param_scope);

                let stmts = self.structure_region(cfg.entry_block, None, cfg);
                let body = Block::with_stmts(stmts);

                self.pop_scope();
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

    /// Structures a region of the CFG, from `current` up to (but not including) `stop_at`.
    fn structure_region(
        &mut self,
        current: usize,
        stop_at: Option<usize>,
        cfg: &ControlFlowGraph,
    ) -> Vec<Stmt> {
        let current_proto = self.active_proto_stack.last().copied().unwrap_or(usize::MAX);
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

        self.push_scope();

        if verbose_enabled() {
            let current_proto = self.active_proto_stack.last().copied();
            eprintln!(
                "[structure] region start proto={:?} block={} stop_at={:?}",
                current_proto, current, stop_at
            );
        }

        // Keep walking until we hit the stop block, or run out of graph
        while Some(curr_id) != stop_at && curr_id < cfg.blocks.len() {
            if !visited_in_region.insert(curr_id) {
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

            for hil_stmt in &block.stmts {
                stmts.push(self.walk_stmt(hil_stmt.clone()));
            }

            match &block.exit {
                BlockExit::Fallthrough(next) | BlockExit::Jump(next) => {
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
                    stmts.push(Stmt::If {
                        condition: self.walk_expr(cond.clone()),
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

                    if let Some((tail_block, body_block, exit_block)) = bounds {
                        let body_stmts = self.structure_region(body_block, Some(tail_block), cfg);

                        stmts.push(Stmt::NumericFor {
                            var: self.local_ident(*base as u8 + 2),
                            start: Expr::Name(self.local_ident(*base as u8)),
                            end: Expr::Name(self.local_ident(*base as u8 + 1)),
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

                    if let Some((tail_block, body_block, exit_block, result_count)) = bounds {
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

                        let body_stmts = self.structure_region(body_block, Some(tail_block), cfg);
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

        self.pop_scope();
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
        scopes: Vec::new(),
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
}
