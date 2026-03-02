use std::collections::{HashMap, HashSet};

use crate::{
    ast::{Block, Expr, Identifier, Literal, Parameter, Stmt, TableConstructorField, UnOp},
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

/// Identifies one source-level local binding for a register.
///
/// Luau reuses registers aggressively. A single register like `R3` may hold multiple unrelated
/// locals at different bytecode PCs. `LocalBindingKey` lets the structurer distinguish those
/// lifetimes so one printed name is not incorrectly reused across separate bindings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum LocalBindingKey {
    /// Fallback when no debug lifetime information exists for the current register use.
    Synthetic { reg: u8, version: usize },
    /// A debug-described local whose lifetime covers the current bytecode PC.
    Debug {
        reg: u8,
        start_pc: usize,
        end_pc: usize,
        slot: usize,
    },
}

impl LocalBindingKey {
    #[inline]
    fn reg(self) -> u8 {
        match self {
            LocalBindingKey::Synthetic { reg, .. } | LocalBindingKey::Debug { reg, .. } => reg,
        }
    }
}

/// Metadata extracted from the synthetic iterator setup that appears right before `ForGPrep`.
///
/// Luau lowers `for k, v in pairs(t) do` into an `AssignMany` that fills iterator state registers,
/// followed immediately by `ForGPrep`. That `AssignMany` is not a real source-level local
/// declaration, so the structurer must read its RHS but avoid registering its LHS locals.
#[derive(Debug, Clone, Copy)]
struct GenericForPreheader<'a> {
    iter_source: &'a HilExpr,
    pc: usize,
}

/// Metadata extracted from the synthetic counter setup that appears right before `ForNPrep`.
///
/// Luau lowers `for i = a, b, c do` into three assignments that seed the limit, step, and
/// current-value registers, followed by `ForNPrep`. Those assignments are not source-level locals,
/// so the structurer should fold their RHS expressions into the loop header.
#[derive(Debug, Clone, Copy)]
struct NumericForPreheader<'a> {
    start_source: &'a HilExpr,
    end_source: &'a HilExpr,
    step_source: &'a HilExpr,
    start_pc: usize,
    end_pc: usize,
    step_pc: usize,
}

/// Extra statements plus remapped capture expressions needed before emitting a closure literal.
///
/// `CAPTURE VAL` needs a snapshot local in the parent scope so later parent writes do not change
/// what the child closure sees. `prologue` contains those snapshot declarations and `captures`
/// holds the expressions the child closure should receive as upvalues.
#[derive(Debug, Default)]
struct PreparedClosureCaptures {
    prologue: Vec<Stmt>,
    captures: Vec<Expr>,
}

/// Result of lowering a closure expression.
///
/// Some closure expressions need statements to appear before the expression itself, for example
/// snapshot locals created for `CAPTURE VAL`. The caller must emit `prologue` before using `expr`.
#[derive(Debug)]
struct LoweredClosureExpr {
    prologue: Vec<Stmt>,
    expr: Expr,
}

/// Extracts a single-name local declaration from `stmt`.
///
/// Several structuring passes only care about the simple `local x = value` shape, for example
/// branch-local hoisting and condition-temp folding. This helper centralizes that pattern match so
/// those passes can stay focused on control-flow logic.
///
/// Returns:
/// - `Some((name, value))` when `stmt` is exactly one local name initialized by one expression
/// - `None` for every other statement shape
#[inline]
fn single_local_decl(stmt: Option<&Stmt>) -> Option<(Identifier, Expr)> {
    match stmt? {
        Stmt::LocalDeclaration { names, values } if names.len() == 1 && values.len() == 1 => {
            Some((names[0].clone(), values[0].clone()))
        }
        _ => None,
    }
}

/// Reads the synthetic iterator setup that Luau places immediately before `ForGPrep`.
///
/// Generic `for` loops are lowered through an `AssignMany` into hidden iterator-state registers.
/// The structurer uses this helper to recover the iterator source expression without emitting those
/// internal registers as fake source-level locals.
///
/// Returns:
/// - `Some(GenericForPreheader)` when the last statement in `block` matches the expected setup for
///   `base`
/// - `None` when `block` does not look like a generic-for preheader
fn generic_for_preheader<'a>(
    block: &'a crate::hil::Block,
    base: usize,
    stmt_pcs: Option<&'a [usize]>,
) -> Option<GenericForPreheader<'a>> {
    let last_idx = block.stmts.len().checked_sub(1)?;
    let HilStmt::AssignMany { left, value } = block.stmts.get(last_idx)? else {
        return None;
    };
    let Some(HilExpr::Local(reg)) = left.first() else {
        return None;
    };
    if *reg as usize != base {
        return None;
    }

    Some(GenericForPreheader {
        iter_source: value,
        pc: stmt_pcs
            .and_then(|pcs| pcs.get(last_idx).copied())
            .unwrap_or(0),
    })
}

/// Reads the synthetic counter setup that Luau places immediately before `ForNPrep`.
///
/// Numeric `for` loops seed limit, step, and current-value registers in the preheader block. The
/// structurer folds those hidden register writes back into the printed `for i = start, finish,
/// step` header with the correct source PCs for local lifetime lookup.
///
/// Returns:
/// - `Some(NumericForPreheader)` when the tail of `block` matches the expected three-register setup
///   for `base`
/// - `None` when `block` does not encode a recoverable numeric-for preheader
fn numeric_for_preheader<'a>(
    block: &'a crate::hil::Block,
    base: usize,
    stmt_pcs: Option<&'a [usize]>,
) -> Option<NumericForPreheader<'a>> {
    let mut start = None;
    let mut end = None;
    let mut step = None;

    for stmt_idx in block.stmts.len().saturating_sub(3)..block.stmts.len() {
        let Some(HilStmt::Assign {
            left: HilExpr::Local(reg),
            value,
        }) = block.stmts.get(stmt_idx)
        else {
            return None;
        };

        let pc = stmt_pcs
            .and_then(|pcs| pcs.get(stmt_idx).copied())
            .unwrap_or(0);

        match usize::from(*reg) {
            r if r == base => end = Some((value, pc)),
            r if r == base + 1 => step = Some((value, pc)),
            r if r == base + 2 => start = Some((value, pc)),
            _ => return None,
        }
    }

    let (start_source, start_pc) = start?;
    let (end_source, end_pc) = end?;
    let (step_source, step_pc) = step?;

    Some(NumericForPreheader {
        start_source,
        end_source,
        step_source,
        start_pc,
        end_pc,
        step_pc,
    })
}

/// Returns a stable fallback identifier for an upvalue register index.
#[inline]
fn upvalue_ident(up: u8) -> Identifier {
    Identifier::from(format!("_up{}", up))
}

/// Returns whether `expr` is a closure that captures local register `reg`.
///
/// Register reuse needs this guard before assigning a fresh synthetic local name. If the incoming
/// closure still captures the current register, renaming the binding would sever the intended
/// closure/upvalue relationship.
///
/// Returns:
/// - `true` when `expr` is a closure whose capture list references `reg`
/// - `false` for every non-closure expression or closures that do not capture `reg`
fn closure_captures_local_reg(expr: &HilExpr, reg: u8) -> bool {
    match expr {
        HilExpr::Closure { captures, .. } => captures.iter().any(|capture| match capture {
            HilExpr::Local(captured) => *captured == reg,
            HilExpr::CaptureValue(inner) => {
                matches!(inner.as_ref(), HilExpr::Local(captured) if *captured == reg)
            }
            _ => false,
        }),
        _ => false,
    }
}

/// Returns whether `expr` references `name` anywhere inside its tree.
///
/// Condition folding uses this to decide whether a trailing temporary assignment can be inlined
/// into the condition or must remain as a standalone statement. Without this check we would remove
/// assignments that still provide values used by later code.
///
/// Returns:
/// - `true` when `expr` contains at least one `Expr::Name` equal to `name`
/// - `false` when `name` does not appear anywhere inside `expr`
fn expr_mentions_name(expr: &Expr, name: &Identifier) -> bool {
    match expr {
        Expr::Name(candidate) => candidate == name,
        Expr::Binary { lhs, rhs, .. } => {
            expr_mentions_name(lhs, name) || expr_mentions_name(rhs, name)
        }
        Expr::Unary { expr, .. } => expr_mentions_name(expr, name),
        _ => false,
    }
}

/// Replaces every textual use of `name` inside `expr` with `replacement`.
///
/// This is used immediately after `expr_mentions_name` says a temporary condition variable is safe
/// to fold away. The helper keeps the resulting condition equivalent while letting the structurer
/// delete the now-redundant assignment statement.
///
/// Returns:
/// - a cloned expression tree where each matching `Expr::Name(name)` node became `replacement`
/// - the original structure for subtrees that do not mention `name`
fn replace_name_in_expr(expr: Expr, name: &Identifier, replacement: &Expr) -> Expr {
    match expr {
        Expr::Name(candidate) if &candidate == name => replacement.clone(),
        Expr::Binary { lhs, op, rhs } => Expr::Binary {
            lhs: Box::new(replace_name_in_expr(*lhs, name, replacement)),
            op,
            rhs: Box::new(replace_name_in_expr(*rhs, name, replacement)),
        },
        Expr::Unary { op, expr } => Expr::Unary {
            op,
            expr: Box::new(replace_name_in_expr(*expr, name, replacement)),
        },
        other => other,
    }
}

/// Produces the logical negation of a structured condition expression.
///
/// Loop and branch recovery frequently need to swap which CFG successor is treated as the "exit"
/// side. We prefer to flip simple equality tests directly so the printed Luau stays readable, and
/// fall back to wrapping the expression in `not` for everything else.
///
/// Returns:
/// - a simplified inverted comparison for `==` and `~=`
/// - `not <expr>` for every other condition shape
fn invert_condition(expr: Expr) -> Expr {
    match expr {
        Expr::Binary { lhs, op, rhs } => match op {
            crate::ast::BinOp::Eq => Expr::Binary {
                lhs,
                op: crate::ast::BinOp::Ne,
                rhs,
            },
            crate::ast::BinOp::Ne => Expr::Binary {
                lhs,
                op: crate::ast::BinOp::Eq,
                rhs,
            },
            _ => Expr::Unary {
                op: UnOp::Not,
                expr: Box::new(Expr::Binary { lhs, op, rhs }),
            },
        },
        other => Expr::Unary {
            op: UnOp::Not,
            expr: Box::new(other),
        },
    }
}

/// Removes a trailing `continue` emitted while structuring a loop body region.
///
/// Region walking naturally emits an explicit `continue` when it sees a backedge. Once that region
/// becomes the body of a recovered `while`, the final `continue` is redundant and would add noise
/// or change formatting without changing semantics.
///
/// Returns:
/// - nothing; `stmts` is updated in place and may lose its last statement when it is `continue`
fn strip_terminal_continue(stmts: &mut Vec<Stmt>) {
    if matches!(stmts.last(), Some(Stmt::Continue)) {
        stmts.pop();
    }
}

/// Returns whether `stmt` already stops control flow for the current block.
///
/// Branch-merging helpers use this before appending a synthetic `break`. We only want to add that
/// `break` when the branch would otherwise fall through, not when it already returns or continues.
///
/// Returns:
/// - `true` for `break`, `continue`, and `return`
/// - `false` for every non-terminal statement
fn stmt_is_terminal(stmt: &Stmt) -> bool {
    matches!(stmt, Stmt::Break | Stmt::Continue | Stmt::Return { .. })
}

/// Appends `break` when a structured branch body would otherwise fall through.
///
/// Some loop-exit reconstructions build a branch body out of a CFG slice that originally reached
/// the loop latch. In structured Luau that slice must end with an explicit `break` so execution
/// leaves the recovered loop at the same point as the source CFG.
///
/// Returns:
/// - nothing; `stmts` is updated in place and gains a trailing `break` only when needed
fn ensure_terminal_break(stmts: &mut Vec<Stmt>) {
    if !matches!(stmts.last(), Some(stmt) if stmt_is_terminal(stmt)) {
        stmts.push(Stmt::Break);
    }
}

/// Returns whether `stmts` is only a conditional break guard.
///
/// Nested loop recovery sometimes structures a post-body latch block as `if cond then break`.
/// Wrapping that guard in another `while true` would create a spurious inner loop even though
/// the guard is meant to remain inside an already-recovered enclosing loop body.
///
/// Returns:
/// - `true` when `stmts` is exactly one `if` whose then-body is a single `break`
/// - `false` for every other statement shape
fn stmts_are_break_guard_only(stmts: &[Stmt]) -> bool {
    matches!(
        stmts,
        [Stmt::If {
            then_body,
            else_body: None,
            ..
        }] if matches!(then_body.stmts.as_slice(), [Stmt::Break])
    )
}

struct HilWalker<'a> {
    cfgs: &'a [ControlFlowGraph],
    protos: &'a [Proto],

    scopes: ScopeManager,
    /// A list of upvalues in the current function.
    upvals: Vec<Expr>,
    /// Per-function mapping from local lifetime -> printable local name.
    local_names: HashMap<LocalBindingKey, Identifier>,
    /// Names that cannot be reused (locals and referenced upvalue names).
    used_names: HashSet<Identifier>,
    /// Generation for synthetic register bindings without debug lifetime info.
    synthetic_versions: HashMap<u8, usize>,
    /// Locals captured by child closures in the current function.
    captured_names: HashSet<Identifier>,
    /// Active proto expansion stack while structuring nested closures.
    active_proto_stack: Vec<usize>,
    /// Active structure-region calls to detect recursive region expansion.
    active_regions: HashSet<(usize, usize, Option<usize>)>,
    /// Depth of recursive `structure_region` calls.
    region_call_depth: usize,
    /// Bytecode word pc currently being structured.
    current_pc: usize,
}

impl<'a> HilWalker<'a> {
    #[inline]
    fn current_proto(&self) -> Option<&Proto> {
        self.active_proto_stack
            .last()
            .and_then(|idx| self.protos.get(*idx))
    }

    /// When both `if` branches introduce the same synthetic local, hoist the declaration so
    /// later statements can legally reference that name after the conditional merge.
    fn hoist_matching_branch_locals(
        &mut self,
        outer_stmts: &mut Vec<Stmt>,
        then_stmts: &mut [Stmt],
        else_stmts: &mut [Stmt],
    ) {
        let else_locals: HashSet<_> = else_stmts
            .iter()
            .filter_map(|stmt| single_local_decl(Some(stmt)).map(|(name, _)| name))
            .collect();
        let hoisted: Vec<_> = then_stmts
            .iter()
            .filter_map(|stmt| single_local_decl(Some(stmt)).map(|(name, _)| name))
            .filter(|name| else_locals.contains(name) && self.scopes.get_var(name).is_none())
            .collect();

        if hoisted.is_empty() {
            return;
        }

        let hoisted_set: HashSet<_> = hoisted.iter().cloned().collect();
        let scope = self
            .scopes
            .top_scope()
            .expect("there should always be a scope");
        for name in &hoisted {
            scope.add_var(Var::new(name.clone(), None));
            outer_stmts.push(Stmt::LocalDeclaration {
                names: vec![name.clone()],
                values: Vec::new(),
            });
        }

        for stmts in [&mut *then_stmts, &mut *else_stmts] {
            for stmt in stmts.iter_mut() {
                let Some((name, value)) = single_local_decl(Some(stmt)) else {
                    continue;
                };
                if !hoisted_set.contains(&name) {
                    continue;
                }
                *stmt = Stmt::Assignment {
                    lhs: Expr::Name(name),
                    rhs: value,
                };
            }
        }
    }

    /// Returns true when `block` dominates one of its predecessors, which we treat as a loop header.
    fn is_loop_header(&self, block: usize, cfg: &ControlFlowGraph) -> bool {
        cfg.predecessors(block)
            .iter()
            .copied()
            .any(|pred| pred != block && cfg.dominates(block, pred))
    }

    /// Returns whether `start` can reach `target` through a non-`for` backedge.
    ///
    /// This is used to decide whether one side of a conditional is the body of a source-level
    /// `while` loop. We intentionally ignore `FORNLOOP`/`FORGLOOP` edges here so an enclosing
    /// numeric or generic `for` does not make an unrelated exit branch look like the loop body.
    ///
    /// Returns:
    /// - `true` when some block reachable from `start` jumps directly back to `target` without
    ///   that jump being emitted by a Luau `for` loop tail
    /// - `false` when no such plain backedge exists
    fn branch_has_plain_backedge(
        &self,
        start: usize,
        target: usize,
        cfg: &ControlFlowGraph,
    ) -> bool {
        let mut stack = vec![start];
        let mut seen = HashSet::new();

        while let Some(block) = stack.pop() {
            if !seen.insert(block) {
                continue;
            }

            if cfg.successors(block).contains(&target)
                && !matches!(
                    cfg.blocks.get(block).map(|b| &b.exit),
                    Some(BlockExit::ForNLoop { .. } | BlockExit::ForGLoop { .. })
                )
            {
                return true;
            }

            for &succ in cfg.successors(block) {
                if succ != target && cfg.dominates(target, succ) {
                    stack.push(succ);
                }
            }
        }

        false
    }

    /// Collects forward-reachable blocks from `start` without stepping onto `target`.
    ///
    /// Loop exit detection compares the blocks reachable from the exit side and the backedge side
    /// of a candidate loop header. Their overlap approximates the rejoin point where both sides
    /// converge after the loop terminates.
    ///
    /// Returns:
    /// - the set of blocks reachable from `start` while staying inside the region dominated by
    ///   `target` and never visiting `target` itself
    fn forward_reachable_without_target(
        &self,
        start: usize,
        target: usize,
        cfg: &ControlFlowGraph,
    ) -> HashSet<usize> {
        let mut stack = vec![start];
        let mut seen = HashSet::new();

        while let Some(block) = stack.pop() {
            if block == target || !seen.insert(block) {
                continue;
            }

            for &succ in cfg.successors(block) {
                if succ != target && cfg.dominates(target, succ) {
                    stack.push(succ);
                }
            }
        }

        seen
    }

    /// Chooses the first block where a candidate loop exit and loop body can both reach.
    ///
    /// After identifying which conditional successor behaves like the backedge, we still need to
    /// know where structured emission should continue once the loop ends. The earliest shared
    /// reachable block is a practical approximation of that post-loop join.
    ///
    /// Returns:
    /// - the smallest shared reachable block id when both branches reconverge
    /// - `exit_branch` when no shared successor exists inside the dominated region
    fn find_loop_exit_block(
        &self,
        header: usize,
        exit_branch: usize,
        backedge_branch: usize,
        cfg: &ControlFlowGraph,
    ) -> usize {
        let exit_reachable = self.forward_reachable_without_target(exit_branch, header, cfg);
        let backedge_reachable =
            self.forward_reachable_without_target(backedge_branch, header, cfg);

        exit_reachable
            .intersection(&backedge_reachable)
            .copied()
            .min()
            .unwrap_or(exit_branch)
    }

    /// Finds the structured exit block for a CFG block that acts like a loop header.
    ///
    /// This is the entry point used when region walking encounters a later block that should be
    /// emitted as a recovered loop before continuing with the surrounding function body.
    ///
    /// Returns:
    /// - `Some(exit_block)` when exactly one conditional successor behaves like the loop backedge
    /// - `None` when the header does not have a recoverable while-loop shape
    fn loop_header_exit_block(&self, header: usize, cfg: &ControlFlowGraph) -> Option<usize> {
        let block = cfg.blocks.get(header)?;
        match &block.exit {
            BlockExit::CondJump {
                then_block,
                else_block,
                ..
            } => {
                let then_backedges = self.branch_has_plain_backedge(*then_block, header, cfg);
                let else_backedges = self.branch_has_plain_backedge(*else_block, header, cfg);
                if then_backedges == else_backedges {
                    return None;
                }
                let (loop_block, exit_branch) = if then_backedges {
                    (*then_block, *else_block)
                } else {
                    (*else_block, *then_block)
                };
                Some(self.find_loop_exit_block(header, exit_branch, loop_block, cfg))
            }
            _ => None,
        }
    }

    /// Finds the innermost loop header that dominates `block`.
    ///
    /// Nested loop recovery needs to know which surrounding loop a conditional belongs to. Using
    /// the nearest dominating header lets us distinguish exits from the current inner region from
    /// branches that merely continue an enclosing loop.
    ///
    /// Returns:
    /// - `Some(header)` for the closest dominating loop header
    /// - `None` when `block` is not nested inside any recoverable loop header
    fn nearest_dominating_loop_header(
        &self,
        block: usize,
        cfg: &ControlFlowGraph,
    ) -> Option<usize> {
        let mut best = None;

        for candidate in 0..cfg.blocks.len() {
            if candidate == block || !self.is_loop_header(candidate, cfg) {
                continue;
            }
            if !cfg.dominates(candidate, block) {
                continue;
            }
            match best {
                Some(current_best) if !cfg.dominates(current_best, candidate) => {}
                _ => best = Some(candidate),
            }
        }

        best
    }

    /// Returns whether `start` is just an empty jump chain back to `target`.
    ///
    /// The nested-loop exit heuristic uses this to distinguish a real loop-body tail from a
    /// synthetic `continue` edge. If the branch contains assignments, calls, or another
    /// conditional split before re-entering the loop header, we must keep structuring that
    /// branch as part of the loop body instead of collapsing the current condition into
    /// `if cond then break end`.
    ///
    /// Returns:
    /// - `true` when every block reachable from `start` before `target` is empty and advances
    ///   through a single unconditional edge toward `target`
    /// - `false` when the branch has executable statements, another conditional, or exits
    ///   somewhere other than `target`
    fn branch_is_trivial_continue(
        &self,
        start: usize,
        target: usize,
        cfg: &ControlFlowGraph,
    ) -> bool {
        let mut stack = vec![start];
        let mut seen = HashSet::new();

        while let Some(block) = stack.pop() {
            if block == target || !seen.insert(block) {
                continue;
            }

            let Some(branch_block) = cfg.blocks.get(block) else {
                return false;
            };
            if !branch_block.stmts.is_empty() {
                return false;
            }

            match branch_block.exit {
                BlockExit::Jump(next) | BlockExit::Fallthrough(next) => {
                    if next != target && cfg.dominates(target, next) {
                        stack.push(next);
                    } else if next != target {
                        return false;
                    }
                }
                _ => return false,
            }
        }

        true
    }

    /// Inlines a trailing temporary assignment into `condition` when it is only used there.
    ///
    /// Luau often materializes a boolean or comparison result into a temporary register just before
    /// a branch. Keeping that assignment in the structured output produces noisy patterns like
    /// `local t = a < b; if t then`. Folding it back into the condition recovers the more natural
    /// source form.
    ///
    /// Returns:
    /// - the original `condition` when the last statement does not define a usable temporary
    /// - a rewritten condition with the temporary substituted, after removing the trailing
    ///   assignment or local declaration from `stmts`
    fn fold_trailing_condition_temp(&mut self, stmts: &mut Vec<Stmt>, condition: Expr) -> Expr {
        let Some((name, value, was_local_decl)) = stmts.last().and_then(|stmt| match stmt {
            Stmt::LocalDeclaration { names, values } if names.len() == 1 && values.len() == 1 => {
                Some((names[0].clone(), values[0].clone(), true))
            }
            Stmt::Assignment {
                lhs: Expr::Name(name),
                rhs,
            } => Some((name.clone(), rhs.clone(), false)),
            _ => None,
        }) else {
            return condition;
        };

        if !expr_mentions_name(&condition, &name) {
            return condition;
        }

        stmts.pop();
        if was_local_decl {
            self.scopes.remove_var(&name);
        }
        replace_name_in_expr(condition, &name, &value)
    }

    /// Resolves an upvalue expression in the current function context.
    #[inline]
    fn resolve_upvalue_expr(&self, up: u8) -> Expr {
        self.upvals
            .get(up as usize)
            .cloned()
            .unwrap_or_else(|| Expr::Name(upvalue_ident(up)))
    }

    /// Reserves names referenced by captured upvalues so locals don't shadow them.
    fn reserve_upvalue_names(&mut self) {
        for upval in &self.upvals {
            if let Expr::Name(name) = upval {
                self.used_names.insert(name.clone());
            }
        }
    }

    /// Reserves additional names in the current function so generated locals fall back to `_l`.
    fn reserve_local_names<'b>(&mut self, names: impl IntoIterator<Item = &'b Identifier>) {
        self.used_names.extend(names.into_iter().cloned());
    }

    /// Chooses the source-level local binding for `reg` at the current bytecode PC.
    ///
    /// When local debug info exists, we key by `(register, lifetime)` instead of only by register.
    /// That prevents output like `v3 = v9` from reusing the printed name of an older `R3` binding.
    fn local_binding_key(&self, reg: u8) -> LocalBindingKey {
        let Some(proto) = self.current_proto() else {
            return LocalBindingKey::Synthetic {
                reg,
                version: self.synthetic_versions.get(&reg).copied().unwrap_or(0),
            };
        };

        proto
            .locals
            .iter()
            .enumerate()
            .filter(|(_, local)| {
                local.register == reg
                    && local.start_pc <= self.current_pc
                    && self.current_pc < local.end_pc
            })
            .max_by_key(|(_, local)| (local.start_pc, local.end_pc))
            .map(|(slot, local)| LocalBindingKey::Debug {
                reg,
                start_pc: local.start_pc,
                end_pc: local.end_pc,
                slot,
            })
            .unwrap_or(LocalBindingKey::Synthetic {
                reg,
                version: self.synthetic_versions.get(&reg).copied().unwrap_or(0),
            })
    }

    /// Advances the synthetic lifetime version for `reg`.
    ///
    /// When a register is reused after a captured local is still visible, the printer needs a fresh
    /// synthetic name so the new binding does not alias the old captured one. Bumping the version
    /// changes the `LocalBindingKey` used by `local_ident`.
    ///
    /// Returns:
    /// - nothing; the synthetic version map is updated in place for `reg`
    fn fresh_synthetic_binding(&mut self, reg: u8) {
        let version = self.synthetic_versions.entry(reg).or_insert(0);
        *version += 1;
    }

    /// Returns a stable printable local identifier for a register in this function.
    fn local_ident(&mut self, reg: u8) -> Identifier {
        let key = self.local_binding_key(reg);
        if let Some(existing) = self.local_names.get(&key) {
            return existing.clone();
        }

        if matches!(key, LocalBindingKey::Synthetic { version: 0, .. })
            && let Some((_, existing)) = self.local_names.iter().find(|(existing_key, name)| {
                existing_key.reg() == reg && self.scopes.get_var(name).is_some()
            })
        {
            let existing = existing.clone();
            self.local_names.insert(key, existing.clone());
            return existing;
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
        self.local_names.insert(key, candidate.clone());
        candidate
    }

    /// Chooses a fresh local name for a captured-by-value snapshot.
    ///
    /// Snapshot locals are emitted in the parent scope immediately before closure creation. They
    /// must avoid colliding with already-used names and with any names reserved by the destination
    /// closure binding so the generated source stays readable and unambiguous.
    ///
    /// Returns:
    /// - a unique identifier derived from the captured value when possible
    /// - a fallback `_cap...`-style identifier when the captured value has no obvious base name
    fn fresh_capture_ident(&mut self, value: &Expr, reserved_names: &[Identifier]) -> Identifier {
        let base = match value {
            Expr::Name(name) => format!("{}_l0", name.as_str()),
            _ => "_cap".to_string(),
        };
        let mut candidate = Identifier::from(base);
        if self.used_names.contains(&candidate)
            || reserved_names.iter().any(|name| name == &candidate)
        {
            let stem = candidate.as_str().to_string();
            let mut suffix = 1usize;
            loop {
                let alt = Identifier::from(format!("{stem}_{suffix}"));
                if !self.used_names.contains(&alt)
                    && !reserved_names.iter().any(|name| name == &alt)
                {
                    candidate = alt;
                    break;
                }
                suffix += 1;
            }
        }

        self.used_names.insert(candidate.clone());
        candidate
    }

    /// Prepares parent-scope statements and upvalue expressions for a closure literal.
    ///
    /// For ordinary `CAPTURE VAL`, we emit `local snapshot = current_value` before the closure
    /// and pass `snapshot` into the child so the nested function sees the pre-closure value.
    /// When Luau captures the destination local of the closure being assigned, however, the
    /// capture is the closure's own binding, not the register's previous value, so we reuse the
    /// final local name directly instead of snapshotting stale data like an overwritten callee.
    fn prepare_closure_captures(
        &mut self,
        captures: Vec<HilExpr>,
        reserved_names: &[Identifier],
        closure_target: Option<(u8, Identifier)>,
    ) -> PreparedClosureCaptures {
        let mut prepared = PreparedClosureCaptures {
            prologue: Vec::new(),
            captures: Vec::with_capacity(captures.len()),
        };

        for capture in captures {
            match capture {
                HilExpr::CaptureValue(expr) => {
                    if let Some((target_reg, target_ident)) = closure_target.as_ref()
                        && matches!(expr.as_ref(), HilExpr::Local(reg) if reg == target_reg)
                    {
                        self.captured_names.insert(target_ident.clone());
                        prepared.captures.push(Expr::Name(target_ident.clone()));
                        continue;
                    }

                    let value = self.walk_expr(*expr);
                    let ident = self.fresh_capture_ident(&value, reserved_names);
                    let scope = self
                        .scopes
                        .top_scope()
                        .expect("there should always be a scope");
                    scope.add_var(Var::new(ident.clone(), None));
                    prepared.prologue.push(Stmt::LocalDeclaration {
                        names: vec![ident.clone()],
                        values: vec![value],
                    });
                    self.captured_names.insert(ident.clone());
                    prepared.captures.push(Expr::Name(ident));
                }
                other => {
                    let capture = self.walk_expr(other);
                    if let Expr::Name(name) = &capture {
                        self.captured_names.insert(name.clone());
                    }
                    prepared.captures.push(capture);
                }
            }
        }

        prepared
    }

    /// Walks a HIL statement and translates it into an AST statement.
    fn walk_stmt(&mut self, stmt: HilStmt) -> Vec<Stmt> {
        match stmt {
            HilStmt::Assign { left, value } => {
                // local, global, upval, getindex
                match left {
                    HilExpr::Local(reg) => {
                        let mut ident = self.local_ident(reg);
                        if matches!(
                            self.local_binding_key(reg),
                            LocalBindingKey::Synthetic { .. }
                        ) && self.scopes.get_var(&ident).is_some()
                            && self.captured_names.contains(&ident)
                            && !closure_captures_local_reg(&value, reg)
                        {
                            self.fresh_synthetic_binding(reg);
                            ident = self.local_ident(reg);
                        }
                        let LoweredClosureExpr {
                            mut prologue,
                            expr: rhs,
                        } = match value {
                            HilExpr::Closure { proto, captures } => self.walk_closure_expr(
                                proto,
                                captures,
                                std::slice::from_ref(&ident),
                                Some((reg, ident.clone())),
                            ),
                            other => LoweredClosureExpr {
                                prologue: Vec::new(),
                                expr: self.walk_expr(other),
                            },
                        };
                        let stmt = if self.scopes.get_var(&ident).is_some() {
                            Stmt::Assignment {
                                lhs: Expr::Name(ident),
                                rhs,
                            }
                        } else {
                            let scope = self
                                .scopes
                                .top_scope()
                                .expect("there should always be a scope");
                            scope.add_var(Var::new(ident.clone(), None));
                            Stmt::LocalDeclaration {
                                names: vec![ident],
                                values: vec![rhs],
                            }
                        };
                        prologue.push(stmt);
                        prologue
                    }
                    HilExpr::Global(name) => vec![Stmt::Assignment {
                        lhs: Expr::Name(name.into()),
                        rhs: self.walk_expr(value),
                    }],
                    HilExpr::Upval(up) => vec![Stmt::Assignment {
                        lhs: self.resolve_upvalue_expr(up),
                        rhs: self.walk_expr(value),
                    }],
                    HilExpr::GetIndex(table, index) => vec![Stmt::Assignment {
                        lhs: Expr::Index {
                            base: Box::new(self.walk_expr(*table)),
                            index: Box::new(self.walk_expr(*index)),
                        },
                        rhs: self.walk_expr(value),
                    }],
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

                vec![Stmt::LocalDeclaration {
                    names: idents,
                    values: vec![self.walk_expr(value)],
                }]
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
                vec![Stmt::Expression { expr }]
            }
            HilStmt::SetField { table, key, value } => vec![Stmt::Assignment {
                lhs: Expr::Index {
                    base: Box::new(Expr::Name(self.local_ident(table))),
                    index: Box::new(Expr::Literal(Literal::String(key.into()))),
                },
                rhs: self.walk_expr(value),
            }],
            HilStmt::Return(exprs) => vec![Stmt::Return {
                values: exprs.into_iter().map(|arg| self.walk_expr(arg)).collect(),
            }],
        }
    }

    /// Lowers a HIL closure expression into parent-scope setup statements plus an AST closure.
    ///
    /// Closure lowering is more than recursively structuring the child proto: it also has to map
    /// captures into the child context, reserve names so upvalues are not shadowed, and guard
    /// against recursive proto descent when a closure references itself.
    ///
    /// Returns:
    /// - a `LoweredClosureExpr` containing parent-scope prologue statements for capture setup
    /// - an `Expr::AnonymousFunction` for the closure body, or an empty fallback closure when the
    ///   child proto cannot be safely descended into
    fn walk_closure_expr(
        &mut self,
        proto_idx: usize,
        captures: Vec<HilExpr>,
        reserved_names: &[Identifier],
        closure_target: Option<(u8, Identifier)>,
    ) -> LoweredClosureExpr {
        let Some(proto) = self.protos.get(proto_idx) else {
            return LoweredClosureExpr {
                prologue: Vec::new(),
                expr: Expr::AnonymousFunction {
                    params: Vec::new(),
                    body: Block::new(),
                },
            };
        };
        let PreparedClosureCaptures {
            prologue: capture_prologue,
            captures: mapped_captures,
        } = self.prepare_closure_captures(captures, reserved_names, closure_target);

        if self.active_proto_stack.contains(&proto_idx) {
            if verbose_enabled() {
                eprintln!(
                    "[structure] recursive proto closure detected: stack={:?}, next={}",
                    self.active_proto_stack, proto_idx
                );
            }
            return LoweredClosureExpr {
                prologue: capture_prologue,
                expr: Expr::AnonymousFunction {
                    params: (0..proto.num_params)
                        .map(|i| Parameter::Regular(Identifier::from(format!("v{}", i))))
                        .chain(proto.is_vararg.then_some(Parameter::Vararg))
                        .collect(),
                    body: Block::new(),
                },
            };
        }
        if self.active_proto_stack.len() >= MAX_PROTO_RECURSION_DEPTH {
            if verbose_enabled() {
                eprintln!(
                    "[structure] proto recursion depth limit reached ({}), refusing to descend into proto {}",
                    MAX_PROTO_RECURSION_DEPTH, proto_idx
                );
            }
            return LoweredClosureExpr {
                prologue: capture_prologue,
                expr: Expr::AnonymousFunction {
                    params: (0..proto.num_params)
                        .map(|i| Parameter::Regular(Identifier::from(format!("v{}", i))))
                        .chain(proto.is_vararg.then_some(Parameter::Vararg))
                        .collect(),
                    body: Block::new(),
                },
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
        let prev_synthetic_versions = std::mem::take(&mut self.synthetic_versions);
        let prev_captured_names = std::mem::take(&mut self.captured_names);
        let prev_scopes = std::mem::replace(&mut self.scopes, ScopeManager::new());
        let prev_current_pc = self.current_pc;

        self.reserve_upvalue_names();

        let Some(cfg) = self.cfgs.get(proto_idx) else {
            self.used_names = prev_used_names;
            self.local_names = prev_local_names;
            self.synthetic_versions = prev_synthetic_versions;
            self.captured_names = prev_captured_names;
            self.scopes = prev_scopes;
            self.upvals = prev_upvalues;
            self.current_pc = prev_current_pc;
            return LoweredClosureExpr {
                prologue: capture_prologue,
                expr: Expr::AnonymousFunction {
                    params: (0..proto.num_params)
                        .map(|i| Parameter::Regular(Identifier::from(format!("v{}", i))))
                        .chain(proto.is_vararg.then_some(Parameter::Vararg))
                        .collect(),
                    body: Block::new(),
                },
            };
        };

        self.current_pc = 0;
        let mut params: Vec<_> = (0..proto.num_params)
            .map(|i| Parameter::Regular(self.local_ident(i)))
            .collect();
        if proto.is_vararg {
            params.push(Parameter::Vararg);
        }
        self.reserve_local_names(reserved_names.iter());

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
        self.synthetic_versions = prev_synthetic_versions;
        self.captured_names = prev_captured_names;
        self.scopes = prev_scopes;
        self.upvals = prev_upvalues;
        self.current_pc = prev_current_pc;

        if verbose_enabled() {
            eprintln!("[structure] exit closure proto {}", proto_idx);
        }

        LoweredClosureExpr {
            prologue: capture_prologue,
            expr: Expr::AnonymousFunction { params, body },
        }
    }

    /// Walks a HIL expression and translates it into an AST expression.
    fn walk_expr(&mut self, expr: HilExpr) -> Expr {
        match expr {
            HilExpr::Nil => Expr::Literal(Literal::Nil),
            HilExpr::Number(num) => Expr::Literal(Literal::Number(num)),
            HilExpr::String(str) => Expr::Literal(Literal::String(str.into())),
            HilExpr::Bool(b) => Expr::Literal(Literal::Bool(b)),
            HilExpr::VarArgs => Expr::Vararg,
            HilExpr::CaptureValue(expr) => self.walk_expr(*expr),
            HilExpr::Local(reg) => Expr::Name(self.local_ident(reg)),
            HilExpr::Global(name) => Expr::Name(name.into()),
            HilExpr::Upval(up) => self.resolve_upvalue_expr(up),
            HilExpr::Closure { proto, captures } => {
                self.walk_closure_expr(proto, captures, &[], None).expr
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
            HilExpr::Table(values) => Expr::Table {
                fields: values
                    .into_iter()
                    .map(|expr| TableConstructorField::Implicit {
                        value: self.walk_expr(expr),
                    })
                    .collect(),
            },
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
        let mut emitted_explicit_loop = false;
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

            let stmt_pcs = cfg.stmt_word_pcs.get(curr_id);
            let generic_for_preheader = match &block.exit {
                BlockExit::ForGPrep { base, .. } => {
                    generic_for_preheader(block, *base, stmt_pcs.map(Vec::as_slice))
                }
                _ => None,
            };
            let numeric_for_preheader = match &block.exit {
                BlockExit::ForNPrep { base, .. } => {
                    numeric_for_preheader(block, *base, stmt_pcs.map(Vec::as_slice))
                }
                _ => None,
            };
            for (stmt_idx, hil_stmt) in block.stmts.iter().enumerate() {
                // Skip the synthetic iterator-state declaration that Luau inserts before `ForGPrep`.
                // We still read its RHS later when building the `for ... in ...` expression, but we
                // must not declare its LHS registers as normal locals in the surrounding scope.
                if generic_for_preheader.is_some() && stmt_idx + 1 == block.stmts.len() {
                    continue;
                }
                if numeric_for_preheader.is_some() && stmt_idx + 3 >= block.stmts.len() {
                    continue;
                }
                self.current_pc = stmt_pcs
                    .and_then(|pcs| pcs.get(stmt_idx).copied())
                    .unwrap_or(0);
                stmts.extend(self.walk_stmt(hil_stmt.clone()));
            }
            self.current_pc = cfg
                .exit_word_pcs
                .get(curr_id)
                .copied()
                .unwrap_or(self.current_pc);

            match &block.exit {
                BlockExit::Fallthrough(next) | BlockExit::Jump(next) => {
                    if *next < current && cfg.dominates(*next, curr_id) {
                        if is_loop_header || stop_at.is_some() {
                            stmts.push(Stmt::Continue);
                        }
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
                    if !is_loop_header && *next > curr_id && self.is_loop_header(*next, cfg) {
                        if let Some(loop_exit) = self.loop_header_exit_block(*next, cfg) {
                            stmts.extend(self.structure_region(*next, Some(loop_exit), cfg));
                            curr_id = loop_exit;
                            continue;
                        }
                        stmts.extend(self.structure_region(*next, stop_at, cfg));
                        break;
                    }
                    if *next > curr_id
                        && *next != current
                        && self.is_loop_header(*next, cfg)
                        && let Some(loop_exit) = self.loop_header_exit_block(*next, cfg)
                    {
                        stmts.extend(self.structure_region(*next, Some(loop_exit), cfg));
                        curr_id = loop_exit;
                        continue;
                    }
                    curr_id = *next;
                }

                BlockExit::CondJump {
                    cond,
                    then_block,
                    else_block,
                } => {
                    let block_stmt_start = block_stmt_starts
                        .get(&curr_id)
                        .copied()
                        .unwrap_or(stmts.len());
                    let then_backedges = self.branch_has_plain_backedge(*then_block, curr_id, cfg);
                    let else_backedges = self.branch_has_plain_backedge(*else_block, curr_id, cfg);
                    if then_backedges != else_backedges {
                        let (loop_block, exit_branch, exit_is_then) = if then_backedges {
                            (*then_block, *else_block, false)
                        } else {
                            (*else_block, *then_block, true)
                        };
                        let exit_block = if exit_is_then {
                            self.find_loop_exit_block(curr_id, exit_branch, loop_block, cfg)
                        } else {
                            self.find_loop_exit_block(curr_id, exit_branch, loop_block, cfg)
                        };
                        let mut loop_prefix = stmts.split_off(block_stmt_start);
                        let mut continue_condition = self.walk_expr(cond.clone());
                        if exit_is_then {
                            continue_condition = invert_condition(continue_condition);
                        }

                        if loop_prefix.is_empty() {
                            continue_condition = self
                                .fold_trailing_condition_temp(&mut loop_prefix, continue_condition);
                            let mut body_stmts =
                                self.structure_region(loop_block, Some(curr_id), cfg);
                            strip_terminal_continue(&mut body_stmts);
                            stmts.push(Stmt::While {
                                condition: continue_condition,
                                body: Block::with_stmts(body_stmts),
                            });
                            emitted_explicit_loop = true;
                            curr_id = exit_block;
                            continue;
                        }

                        let mut exit_condition = self.walk_expr(cond.clone());
                        if !exit_is_then {
                            exit_condition = invert_condition(exit_condition);
                        }
                        exit_condition =
                            self.fold_trailing_condition_temp(&mut loop_prefix, exit_condition);

                        let mut exit_stmts =
                            self.structure_region(exit_branch, Some(exit_block), cfg);
                        let mut body_stmts =
                            self.structure_region(loop_block, Some(curr_id), cfg);
                        ensure_terminal_break(&mut exit_stmts);
                        strip_terminal_continue(&mut body_stmts);

                        loop_prefix.push(Stmt::If {
                            condition: exit_condition,
                            then_body: Block::with_stmts(exit_stmts),
                            else_body: if body_stmts.is_empty() {
                                None
                            } else {
                                Some(Block::with_stmts(body_stmts))
                            },
                        });
                        stmts.push(Stmt::While {
                            condition: Expr::Literal(Literal::Bool(true)),
                            body: Block::with_stmts(loop_prefix),
                        });
                        emitted_explicit_loop = true;
                        curr_id = exit_block;
                        continue;
                    }

                    let then_back_to_region_start = current != curr_id
                        && self.branch_has_plain_backedge(*then_block, current, cfg);
                    let else_back_to_region_start = current != curr_id
                        && self.branch_has_plain_backedge(*else_block, current, cfg);
                    let then_continues_to_region_start =
                        current != curr_id && self.branch_is_trivial_continue(*then_block, current, cfg);
                    let else_continues_to_region_start =
                        current != curr_id && self.branch_is_trivial_continue(*else_block, current, cfg);
                    if self.is_loop_header(current, cfg)
                        && then_continues_to_region_start != else_continues_to_region_start
                    {
                        let (next_block, should_invert_condition) = if then_continues_to_region_start {
                            (*else_block, false)
                        } else {
                            (*then_block, true)
                        };

                        let mut continue_condition = self.walk_expr(cond.clone());
                        if should_invert_condition {
                            continue_condition = invert_condition(continue_condition);
                        }
                        continue_condition =
                            self.fold_trailing_condition_temp(&mut stmts, continue_condition);
                        stmts.push(Stmt::If {
                            condition: continue_condition,
                            then_body: Block::with_stmts(vec![Stmt::Continue]),
                            else_body: None,
                        });
                        curr_id = next_block;
                        continue;
                    }
                    if then_back_to_region_start != else_back_to_region_start {
                        let (exit_block, should_invert_condition) = if then_back_to_region_start {
                            (*else_block, true)
                        } else {
                            (*then_block, false)
                        };

                        let mut exit_condition = self.walk_expr(cond.clone());
                        if should_invert_condition {
                            exit_condition = invert_condition(exit_condition);
                        }
                        exit_condition =
                            self.fold_trailing_condition_temp(&mut stmts, exit_condition);
                        stmts.push(Stmt::If {
                            condition: exit_condition,
                            then_body: Block::with_stmts(vec![Stmt::Break]),
                            else_body: None,
                        });
                        stmts = vec![Stmt::While {
                            condition: Expr::Literal(Literal::Bool(true)),
                            body: Block::with_stmts(stmts),
                        }];
                        emitted_explicit_loop = true;
                        curr_id = exit_block;
                        continue;
                    }

                    if let Some(loop_header) = self.nearest_dominating_loop_header(curr_id, cfg) {
                        let then_back_to_loop =
                            self.branch_has_plain_backedge(*then_block, loop_header, cfg);
                        let else_back_to_loop =
                            self.branch_has_plain_backedge(*else_block, loop_header, cfg);
                        let then_is_trivial_continue =
                            self.branch_is_trivial_continue(*then_block, loop_header, cfg);
                        let else_is_trivial_continue =
                            self.branch_is_trivial_continue(*else_block, loop_header, cfg);
                        if curr_id != loop_header
                            && then_back_to_loop != else_back_to_loop
                            && (then_is_trivial_continue || else_is_trivial_continue)
                            && !(then_back_to_region_start != else_back_to_region_start)
                        {
                            let mut exit_condition = self.walk_expr(cond.clone());
                            if then_back_to_loop {
                                exit_condition = invert_condition(exit_condition);
                            }
                            exit_condition =
                                self.fold_trailing_condition_temp(&mut stmts, exit_condition);
                            stmts.push(Stmt::If {
                                condition: exit_condition,
                                then_body: Block::with_stmts(vec![Stmt::Break]),
                                else_body: None,
                            });
                            break;
                        }
                    }

                    if let Some(stop_block) = stop_at {
                        let then_hits_stop = *then_block == stop_block;
                        let else_hits_stop = *else_block == stop_block;
                        if then_hits_stop != else_hits_stop
                            && let Some(loop_header) =
                                self.nearest_dominating_loop_header(curr_id, cfg)
                        {
                            let loop_branch = if then_hits_stop {
                                *else_block
                            } else {
                                *then_block
                            };
                            if self.branch_has_plain_backedge(loop_branch, loop_header, cfg)
                                && self.branch_is_trivial_continue(loop_branch, loop_header, cfg)
                            {
                                let mut exit_condition = self.walk_expr(cond.clone());
                                if else_hits_stop {
                                    exit_condition = invert_condition(exit_condition);
                                }
                                exit_condition =
                                    self.fold_trailing_condition_temp(&mut stmts, exit_condition);
                                stmts.push(Stmt::If {
                                    condition: exit_condition,
                                    then_body: Block::with_stmts(vec![Stmt::Break]),
                                    else_body: None,
                                });
                                break;
                            }
                        }
                    }

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
                    if merge_block.is_some() {
                        self.hoist_matching_branch_locals(
                            &mut stmts,
                            &mut then_stmts,
                            &mut else_stmts,
                        );
                    }
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
                        let (start, end, step) = if let Some(preheader) = numeric_for_preheader {
                            self.current_pc = preheader.start_pc;
                            let start = self.walk_expr(preheader.start_source.clone());
                            self.current_pc = preheader.end_pc;
                            let end = self.walk_expr(preheader.end_source.clone());
                            self.current_pc = preheader.step_pc;
                            let step = self.walk_expr(preheader.step_source.clone());
                            (start, end, Some(step))
                        } else {
                            (
                                Expr::Name(self.local_ident(*base as u8 + 2)),
                                Expr::Name(self.local_ident(*base as u8)),
                                Some(Expr::Name(self.local_ident(*base as u8 + 1))),
                            )
                        };
                        let step = match step {
                            Some(Expr::Literal(Literal::Number(n))) if n == 1.0 => None,
                            other => other,
                        };

                        stmts.push(Stmt::NumericFor {
                            var: self.local_ident(*base as u8 + 2),
                            start,
                            end,
                            step,
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

                        if let Some(preheader) = generic_for_preheader {
                            self.current_pc = preheader.pc;
                            iter_expr = self.walk_expr(preheader.iter_source.clone());
                            self.current_pc = cfg
                                .exit_word_pcs
                                .get(curr_id)
                                .copied()
                                .unwrap_or(preheader.pc);
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

        if is_loop_header
            && !emitted_explicit_loop
            && !stmts.is_empty()
            && !stmts_are_break_guard_only(&stmts)
            && !matches!(stmts.as_slice(), [Stmt::While { .. }])
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
        synthetic_versions: HashMap::new(),
        captured_names: HashSet::new(),
        active_proto_stack: vec![entry_proto],
        active_regions: HashSet::new(),
        region_call_depth: 0,
        current_pc: 0,
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
        disasm::{LocalDebug, Proto},
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
                if matches!(names.as_slice(), [name] if name.as_str() == "v4_l0")
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
    fn structure_reuses_register_with_fresh_name_after_local_lifetime_ends() {
        let parent_cfg = ControlFlowGraph::with_pcs(
            vec![HilBlock {
                id: 0,
                stmts: vec![
                    HilStmt::Assign {
                        left: HilExpr::Local(3),
                        value: HilExpr::Closure {
                            proto: 1,
                            captures: vec![],
                        },
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(9),
                        value: HilExpr::Closure {
                            proto: 2,
                            captures: vec![HilExpr::Local(3)],
                        },
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(3),
                        value: HilExpr::Local(9),
                    },
                ],
                exit: BlockExit::Return(vec![HilExpr::Local(9)]),
            }],
            0,
            vec![vec![1, 2, 6]],
            vec![7],
        );
        let empty_child_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![],
                exit: BlockExit::Return(vec![]),
            }],
            0,
        );
        let capturing_child_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![],
                exit: BlockExit::Return(vec![HilExpr::Upval(0)]),
            }],
            0,
        );

        let parent_proto = Proto {
            locals: vec![
                LocalDebug {
                    name: "is_array".to_string(),
                    start_pc: 1,
                    end_pc: 3,
                    register: 3,
                },
                LocalDebug {
                    name: "mode_auto".to_string(),
                    start_pc: 2,
                    end_pc: 8,
                    register: 9,
                },
                LocalDebug {
                    name: "result".to_string(),
                    start_pc: 6,
                    end_pc: 8,
                    register: 3,
                },
            ],
            ..Proto::default()
        };
        let capturing_child_proto = Proto {
            num_upvals: 1,
            ..Proto::default()
        };

        let ast = structure(
            &[parent_cfg, empty_child_cfg, capturing_child_cfg],
            0,
            &[parent_proto, Proto::default(), capturing_child_proto],
        );
        assert_eq!(ast.stmts.len(), 4);

        let mode_auto_body = match &ast.stmts[1] {
            AstStmt::LocalDeclaration { names, values } => {
                assert!(matches!(names.as_slice(), [name] if name.as_str() == "v9"));
                match values.as_slice() {
                    [AstExpr::AnonymousFunction { body, .. }] => body,
                    _ => panic!("expected closure assigned to v9"),
                }
            }
            _ => panic!("expected closure local declaration"),
        };

        assert!(matches!(
            &mode_auto_body.stmts[0],
            AstStmt::Return { values }
                if matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v3")
        ));
        assert!(matches!(
            &ast.stmts[2],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v3_l0")
                    && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v9")
        ));
    }

    #[test]
    fn structure_snapshots_capture_value_before_closure_creation() {
        let parent_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![
                    HilStmt::Assign {
                        left: HilExpr::Local(3),
                        value: HilExpr::Global("ipairs".to_string()),
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(9),
                        value: HilExpr::Closure {
                            proto: 1,
                            captures: vec![HilExpr::CaptureValue(Box::new(HilExpr::Local(3)))],
                        },
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(3),
                        value: HilExpr::Local(9),
                    },
                ],
                exit: BlockExit::Return(vec![]),
            }],
            0,
        );
        let child_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![],
                exit: BlockExit::Return(vec![HilExpr::Upval(0)]),
            }],
            0,
        );

        let child_proto = Proto {
            num_upvals: 1,
            ..Proto::default()
        };
        let ast = structure(
            &[parent_cfg, child_cfg],
            0,
            &[Proto::default(), child_proto],
        );
        assert!(ast.stmts.len() >= 4);

        let snapshot_name = ast
            .stmts
            .iter()
            .find_map(|stmt| match stmt {
                AstStmt::LocalDeclaration { names, values }
                    if names.len() == 1
                        && values.len() == 1
                        && names[0].as_str() != "v3"
                        && matches!(&values[0], AstExpr::Name(name) if name.as_str() == "v3") =>
                {
                    Some(names[0].as_str().to_string())
                }
                _ => None,
            })
            .expect("expected capture-value snapshot local");

        let closure_body = ast
            .stmts
            .iter()
            .find_map(|stmt| match stmt {
                AstStmt::LocalDeclaration { names, values }
                    if matches!(names.as_slice(), [name] if name.as_str() == "v9") =>
                {
                    match values.as_slice() {
                        [AstExpr::AnonymousFunction { body, .. }] => Some(body),
                        _ => None,
                    }
                }
                _ => None,
            })
            .expect("expected closure declaration for v9");

        assert!(matches!(
            &closure_body.stmts[0],
            AstStmt::Return { values }
                if matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == snapshot_name)
        ));
    }

    #[test]
    fn structure_self_capture_value_uses_closure_binding() {
        let parent_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![
                    HilStmt::Assign {
                        left: HilExpr::Local(3),
                        value: HilExpr::Global("unpack".to_string()),
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(3),
                        value: HilExpr::Closure {
                            proto: 1,
                            captures: vec![HilExpr::CaptureValue(Box::new(HilExpr::Local(3)))],
                        },
                    },
                ],
                exit: BlockExit::Return(vec![HilExpr::Local(3)]),
            }],
            0,
        );
        let child_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![],
                exit: BlockExit::Return(vec![HilExpr::Upval(0)]),
            }],
            0,
        );

        let child_proto = Proto {
            num_upvals: 1,
            ..Proto::default()
        };
        let ast = structure(
            &[parent_cfg, child_cfg],
            0,
            &[Proto::default(), child_proto],
        );

        let closure_body = ast
            .stmts
            .iter()
            .find_map(|stmt| match stmt {
                AstStmt::Assignment { lhs, rhs }
                    if matches!(lhs, AstExpr::Name(name) if name.as_str() == "v3") =>
                {
                    match rhs {
                        AstExpr::AnonymousFunction { body, .. } => Some(body),
                        _ => None,
                    }
                }
                _ => None,
            })
            .expect("expected self-referential closure assignment for v3");

        assert!(matches!(
            &closure_body.stmts[0],
            AstStmt::Return { values }
                if matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v3")
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
        assert_eq!(ast.stmts.len(), 2);
        match &ast.stmts[0] {
            AstStmt::NumericFor {
                var,
                start,
                end,
                body,
                ..
            } => {
                assert_eq!(var.as_str(), "v6");
                assert!(matches!(
                    start,
                    AstExpr::Literal(crate::ast::Literal::Number(n)) if *n == 1.0
                ));
                assert!(matches!(end, AstExpr::Name(name) if name.as_str() == "v2"));
                assert_eq!(body.stmts.len(), 2);
            }
            _ => panic!("expected numeric for"),
        }
    }

    #[test]
    fn structure_numeric_for_preserves_explicit_step_expression() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![
                        HilStmt::Assign {
                            left: HilExpr::Local(6),
                            value: HilExpr::Local(9),
                        },
                        HilStmt::Assign {
                            left: HilExpr::Local(4),
                            value: HilExpr::Local(2),
                        },
                        HilStmt::Assign {
                            left: HilExpr::Local(5),
                            value: HilExpr::Number(-1.0),
                        },
                    ],
                    exit: BlockExit::ForNPrep {
                        base: 4,
                        loop_block: 1,
                    },
                },
                HilBlock {
                    id: 1,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(3),
                        value: HilExpr::Local(6),
                    }],
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
        assert_eq!(ast.stmts.len(), 2);

        match &ast.stmts[0] {
            AstStmt::NumericFor {
                var,
                start,
                end,
                step,
                body,
            } => {
                assert_eq!(var.as_str(), "v6");
                assert!(matches!(start, AstExpr::Name(name) if name.as_str() == "v9"));
                assert!(matches!(end, AstExpr::Name(name) if name.as_str() == "v2"));
                assert!(matches!(
                    step,
                    Some(AstExpr::Literal(crate::ast::Literal::Number(n))) if *n == -1.0
                ));
                assert_eq!(body.stmts.len(), 1);
            }
            _ => panic!("expected numeric for"),
        }
    }

    #[test]
    fn structure_captured_synthetic_local_rebind_gets_fresh_name() {
        let parent_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![
                    HilStmt::Assign {
                        left: HilExpr::Local(16),
                        value: HilExpr::Global("to_bits".to_string()),
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(8),
                        value: HilExpr::Closure {
                            proto: 1,
                            captures: vec![HilExpr::Local(16)],
                        },
                    },
                    HilStmt::Assign {
                        left: HilExpr::Local(16),
                        value: HilExpr::Global("str2lei".to_string()),
                    },
                ],
                exit: BlockExit::Return(vec![HilExpr::Local(8)]),
            }],
            0,
        );
        let child_cfg = ControlFlowGraph::new(
            vec![HilBlock {
                id: 0,
                stmts: vec![],
                exit: BlockExit::Return(vec![HilExpr::Upval(0)]),
            }],
            0,
        );

        let child_proto = Proto {
            num_upvals: 1,
            ..Proto::default()
        };

        let ast = structure(
            &[parent_cfg, child_cfg],
            0,
            &[Proto::default(), child_proto],
        );
        assert_eq!(ast.stmts.len(), 4);

        assert!(matches!(
            &ast.stmts[0],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v16")
                    && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "to_bits")
        ));
        match &ast.stmts[1] {
            AstStmt::LocalDeclaration { names, values } => {
                assert!(matches!(names.as_slice(), [name] if name.as_str() == "v8"));
                match values.as_slice() {
                    [AstExpr::AnonymousFunction { body, .. }] => {
                        assert!(matches!(
                            body.stmts.as_slice(),
                            [AstStmt::Return { values }]
                                if matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v16")
                        ));
                    }
                    _ => panic!("expected closure"),
                }
            }
            _ => panic!("expected closure declaration"),
        }
        assert!(matches!(
            &ast.stmts[2],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v16_l0")
                    && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "str2lei")
        ));
        assert!(matches!(
            &ast.stmts[3],
            AstStmt::Return { values }
                if matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v8")
        ));
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
    fn structure_generic_for_preheader_does_not_leak_branch_temp_locals() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![HilStmt::AssignMany {
                        left: vec![HilExpr::Local(2), HilExpr::Local(3), HilExpr::Local(4)],
                        value: HilExpr::Call(
                            Box::new(HilExpr::Global("pairs".to_string())),
                            vec![HilExpr::Local(0)],
                        ),
                    }],
                    exit: BlockExit::ForGPrep {
                        base: 2,
                        loop_block: 1,
                    },
                },
                HilBlock {
                    id: 1,
                    stmts: vec![],
                    exit: BlockExit::ForGLoop {
                        base: 2,
                        body_block: 1,
                        exit_block: 2,
                        result_count: 2,
                    },
                },
                HilBlock {
                    id: 2,
                    stmts: vec![],
                    exit: BlockExit::CondJump {
                        cond: HilExpr::Local(1),
                        then_block: 3,
                        else_block: 4,
                    },
                },
                HilBlock {
                    id: 3,
                    stmts: vec![
                        HilStmt::Assign {
                            left: HilExpr::Local(3),
                            value: HilExpr::Global("mode_auto".to_string()),
                        },
                        HilStmt::Assign {
                            left: HilExpr::Local(4),
                            value: HilExpr::Local(0),
                        },
                    ],
                    exit: BlockExit::Return(vec![HilExpr::Local(3), HilExpr::Local(4)]),
                },
                HilBlock {
                    id: 4,
                    stmts: vec![
                        HilStmt::Assign {
                            left: HilExpr::Local(3),
                            value: HilExpr::Global("mode_ipairs".to_string()),
                        },
                        HilStmt::Assign {
                            left: HilExpr::Local(4),
                            value: HilExpr::Local(0),
                        },
                    ],
                    exit: BlockExit::Return(vec![HilExpr::Local(3), HilExpr::Local(4)]),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        let AstStmt::GenericFor { .. } = &ast.stmts[0] else {
            panic!("expected generic for");
        };
        let AstStmt::If {
            then_body,
            else_body: Some(else_body),
            ..
        } = &ast.stmts[1]
        else {
            panic!("expected if after generic for");
        };

        assert!(matches!(
            &then_body.stmts[1],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v4")
                    && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v0")
        ));
        assert!(matches!(
            &else_body.stmts[1],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v4")
                    && matches!(values.as_slice(), [AstExpr::Name(name)] if name.as_str() == "v0")
        ));
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

    #[test]
    fn structure_conditional_backedge_as_while_without_pulling_in_preheader() {
        let cfg = ControlFlowGraph::new(
            vec![
                HilBlock {
                    id: 0,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(0),
                        value: HilExpr::Number(4.0),
                    }],
                    exit: BlockExit::Fallthrough(1),
                },
                HilBlock {
                    id: 1,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(2),
                        value: HilExpr::Local(0),
                    }],
                    exit: BlockExit::CondJump {
                        cond: HilExpr::Binary(
                            crate::ast::BinOp::Eq,
                            Box::new(HilExpr::Local(2)),
                            Box::new(HilExpr::Number(0.0)),
                        ),
                        then_block: 3,
                        else_block: 2,
                    },
                },
                HilBlock {
                    id: 2,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(0),
                        value: HilExpr::Binary(
                            crate::ast::BinOp::Sub,
                            Box::new(HilExpr::Local(0)),
                            Box::new(HilExpr::Number(1.0)),
                        ),
                    }],
                    exit: BlockExit::Jump(1),
                },
                HilBlock {
                    id: 3,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(4),
                        value: HilExpr::Local(0),
                    }],
                    exit: BlockExit::Return(vec![HilExpr::Local(4)]),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);
        assert!(matches!(
            &ast.stmts[0],
            AstStmt::LocalDeclaration { names, values }
                if matches!(names.as_slice(), [name] if name.as_str() == "v0")
                    && matches!(values.as_slice(), [AstExpr::Literal(crate::ast::Literal::Number(n))] if *n == 4.0)
        ));
        match &ast.stmts[1] {
            AstStmt::While { condition, body } => {
                let header_tested = matches!(
                    condition,
                    AstExpr::Binary { lhs, op: crate::ast::BinOp::Ne, rhs }
                        if matches!(lhs.as_ref(), AstExpr::Name(name) if name.as_str() == "v0")
                            && matches!(rhs.as_ref(), AstExpr::Literal(crate::ast::Literal::Number(n)) if *n == 0.0)
                ) || matches!(
                    condition,
                    AstExpr::Unary { op: crate::ast::UnOp::Not, expr }
                        if matches!(expr.as_ref(), AstExpr::Binary { lhs, op: crate::ast::BinOp::Eq, rhs }
                            if matches!(lhs.as_ref(), AstExpr::Name(name) if name.as_str() == "v0")
                                && matches!(rhs.as_ref(), AstExpr::Literal(crate::ast::Literal::Number(n)) if *n == 0.0))
                );
                let post_tested = matches!(
                    condition,
                    AstExpr::Literal(crate::ast::Literal::Bool(true))
                ) && matches!(
                    body.stmts.as_slice(),
                    [AstStmt::If { condition, then_body, else_body: Some(else_body) }]
                        if matches!(
                            condition,
                            AstExpr::Binary { lhs, op: crate::ast::BinOp::Eq, rhs }
                                if matches!(lhs.as_ref(), AstExpr::Name(name) if name.as_str() == "v0")
                                    && matches!(rhs.as_ref(), AstExpr::Literal(crate::ast::Literal::Number(n)) if *n == 0.0)
                        )
                            && matches!(then_body.stmts.as_slice(), [AstStmt::Break])
                            && matches!(
                                else_body.stmts.as_slice(),
                                [AstStmt::Assignment { lhs, rhs }]
                                    if matches!(lhs, AstExpr::Name(name) if name.as_str() == "v0")
                                        && matches!(rhs, AstExpr::Binary { op: crate::ast::BinOp::Sub, .. })
                            )
                );
                assert!(header_tested || post_tested);
            }
            _ => panic!("expected while loop"),
        }
    }

    #[test]
    fn structure_ignores_outer_for_backedge_when_recovering_inner_while() {
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
                            value: HilExpr::Number(3.0),
                        },
                        HilStmt::Assign {
                            left: HilExpr::Local(5),
                            value: HilExpr::Number(1.0),
                        },
                    ],
                    exit: BlockExit::ForNPrep {
                        base: 4,
                        loop_block: 5,
                    },
                },
                HilBlock {
                    id: 1,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(7),
                        value: HilExpr::Local(6),
                    }],
                    exit: BlockExit::CondJump {
                        cond: HilExpr::Local(7),
                        then_block: 4,
                        else_block: 2,
                    },
                },
                HilBlock {
                    id: 2,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(6),
                        value: HilExpr::Binary(
                            crate::ast::BinOp::Sub,
                            Box::new(HilExpr::Local(6)),
                            Box::new(HilExpr::Number(1.0)),
                        ),
                    }],
                    exit: BlockExit::Fallthrough(3),
                },
                HilBlock {
                    id: 3,
                    stmts: vec![],
                    exit: BlockExit::Jump(1),
                },
                HilBlock {
                    id: 4,
                    stmts: vec![HilStmt::Assign {
                        left: HilExpr::Local(8),
                        value: HilExpr::Local(6),
                    }],
                    exit: BlockExit::Fallthrough(5),
                },
                HilBlock {
                    id: 5,
                    stmts: vec![],
                    exit: BlockExit::ForNLoop {
                        base: 4,
                        body_block: 1,
                        exit_block: 6,
                    },
                },
                HilBlock {
                    id: 6,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![HilExpr::Local(8)]),
                },
            ],
            0,
        );

        let ast = structure(&[cfg], 0, &[Proto::default()]);

        let AstStmt::NumericFor { body, .. } = &ast.stmts[0] else {
            panic!("expected numeric for");
        };

        assert!(matches!(body.stmts.first(), Some(AstStmt::While { .. })));
    }

}
