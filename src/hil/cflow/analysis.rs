use std::collections::HashSet;

use smallvec::SmallVec;

use crate::hil::{
    cflow::graph::{BlockExit, ControlFlowGraph},
    lifter::ssa::SymbolId,
};

/// Walks a branch to locate its most likely merge successor.
///
/// # Returns
/// - `Some(block)` when a stable merge target can be followed from `start`.
/// - `None` when control flow is cyclic/ambiguous before a merge is found.
#[must_use]
fn merge_target_from(start: usize, cfg: &ControlFlowGraph) -> Option<usize> {
    let mut seen = HashSet::new();
    let mut current = start;

    while seen.insert(current) {
        let block = cfg.blocks.get(current)?;
        match block.exit {
            BlockExit::CondJump {
                then_block,
                else_block,
                ..
            } => {
                let then_target = merge_target_from(then_block, cfg);
                let else_target = merge_target_from(else_block, cfg);

                return match (then_target, else_target) {
                    (Some(a), Some(b)) if a == b && a != then_block && a != else_block => Some(a),
                    (Some(target), _) if target == else_block && then_block != else_block => {
                        Some(else_block)
                    }
                    (_, Some(target)) if target == then_block && then_block != else_block => {
                        Some(then_block)
                    }
                    _ => None,
                };
            }
            BlockExit::Fallthrough(next)
                if next == current + 1 && cfg.predecessors(next).len() <= 1 =>
            {
                current = next;
            }
            BlockExit::Fallthrough(next) | BlockExit::Jump(next) => return Some(next),
            BlockExit::FornPrep { exit_block, .. } | BlockExit::ForgPrep { exit_block, .. } => {
                current = exit_block;
            }
            _ => return (current != start).then_some(current),
        }
    }

    None
}

/// Attempts to find the merge block for a simple if/else region.
///
/// # Returns
/// - `Some(join_block)` when both sides converge in a recoverable way.
/// - `None` when no safe merge block is found.
#[must_use]
pub fn find_if_else_join(
    then_block: usize,
    else_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<usize> {
    let then_target = merge_target_from(then_block, cfg);
    let else_target = merge_target_from(else_block, cfg);

    let candidate = match (then_target, else_target) {
        (Some(a), Some(b)) if a == b && a != then_block && a != else_block => a,
        (Some(target), _) if target == else_block && then_block != else_block => else_block,
        (_, Some(target)) if target == then_block && then_block != else_block => then_block,
        _ => return None,
    };

    if (candidate != then_block && cfg.dominates(candidate, then_block))
        || (candidate != else_block && cfg.dominates(candidate, else_block))
    {
        return None;
    }

    Some(candidate)
}

/// Scored candidate from the loop-tail search.
#[derive(PartialEq, Eq, Hash)]
struct ForTailCandidate {
    tail: usize,
    body: usize,
    exit: usize,
}

impl ForTailCandidate {
    pub fn new(tail: usize, body: usize, exit: usize) -> Self {
        Self { tail, body, exit }
    }
}

/// Shared candidate-gathering and scoring logic for all `for` loop variants.
///
/// `try_extract` should match the relevant `BlockExit` variant, verify the base register,
/// and return `(body_block, exit_block)` on success.
///
/// `fallback_pool` is consumed only when no candidates are found through normal traversal.
fn select_best_for_tail(
    prep_block: usize,
    prep_target_block: usize,
    cfg: &ControlFlowGraph,
    try_extract: impl Fn(&BlockExit) -> Option<(usize, usize)>,
    fallback_pool: impl Iterator<Item = usize>,
) -> Option<ForTailCandidate> {
    if prep_block >= cfg.blocks.len() {
        return None;
    }

    let preferred_body = prep_block + 1;
    let mut candidates = HashSet::new();

    if let Some(block) = cfg.blocks.get(prep_target_block)
        && let Some((body, exit)) = try_extract(&block.exit)
    {
        candidates.insert(ForTailCandidate::new(prep_target_block, body, exit));
    }

    for &pred in cfg.predecessors(prep_target_block) {
        if let Some(block) = cfg.blocks.get(pred)
            && let Some((body, exit)) = try_extract(&block.exit)
            && exit == prep_target_block
        {
            candidates.insert(ForTailCandidate::new(pred, body, exit));
        }
    }

    if preferred_body < cfg.blocks.len() {
        for &pred in cfg.predecessors(preferred_body) {
            if let Some(block) = cfg.blocks.get(pred)
                && let Some((body, exit)) = try_extract(&block.exit)
                && body == preferred_body
            {
                candidates.insert(ForTailCandidate::new(pred, body, exit));
            }
        }
    }

    if candidates.is_empty() {
        for tail in fallback_pool {
            if let Some(block) = cfg.blocks.get(tail)
                && let Some((body, exit)) = try_extract(&block.exit)
            {
                candidates.insert(ForTailCandidate::new(tail, body, exit));
            }
        }
    }

    candidates.into_iter().max_by_key(|c| {
        let mut score = 0usize;
        if c.tail == prep_target_block {
            score += 8;
        }
        if c.exit == prep_target_block {
            score += 4;
        }
        if c.body == preferred_body {
            score += 2;
        }
        if cfg.dominates(prep_block, c.body) {
            score += 1;
        }
        score
    })
}

pub struct NumericForTail {
    pub body: usize,
    pub exit: usize,
}

/// Resolves the tail/body/exit for a numeric `for` loop preheader.
///
/// # Returns
/// - `Some((tail_block, body_block, exit_block))` for a recoverable numeric loop.
/// - `None` when no matching `FORNLOOP` shape is found.
#[must_use]
pub fn resolve_numeric_for_tail(
    prep_block: usize,
    base: u8,
    prep_target_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<NumericForTail> {
    let fallback = cfg
        .numeric_loops_by_base
        .get(&base)
        .into_iter()
        .flatten()
        .copied();

    let candidate = select_best_for_tail(
        prep_block,
        prep_target_block,
        cfg,
        |exit| match exit {
            BlockExit::FornLoop {
                base: loop_base,
                body_block,
                exit_block,
            } if *loop_base == base => Some((*body_block, *exit_block)),
            _ => None,
        },
        fallback,
    )?;
    Some(NumericForTail {
        body: candidate.body,
        exit: candidate.exit,
    })
}

pub struct GenericForTail<'cfg> {
    pub body: usize,
    pub exit: usize,
    pub vars: &'cfg SmallVec<[SymbolId; 3]>,
}

/// Resolves the tail/body/exit/result-count for a generic `for` loop preheader.
///
/// # Returns
/// - `Some((tail_block, body_block, exit_block, result_count))` for a recoverable generic loop.
/// - `None` when no matching `FORGLOOP` shape is found.
#[must_use]
pub fn resolve_generic_for_tail<'a>(
    prep_block: usize,
    base: u8,
    prep_target_block: usize,
    cfg: &'a ControlFlowGraph,
) -> Option<GenericForTail<'a>> {
    let fallback = cfg
        .generic_loops_by_base
        .get(&base)
        .into_iter()
        .flatten()
        .copied();

    let preferred_body = prep_block + 1;

    let candidate = select_best_for_tail(
        prep_block,
        prep_target_block,
        cfg,
        |exit| match exit {
            BlockExit::ForgLoop {
                base: loop_base,
                body_block,
                exit_block,
                ..
            } if *loop_base == base => Some((*body_block, *exit_block)),
            _ => None,
        },
        fallback,
    )?;

    let BlockExit::ForgLoop { ref vars, .. } = cfg.blocks[candidate.tail].exit else {
        unreachable!("tail_block was selected from a ForgLoop exit");
    };

    let body_block =
        if linear_fallthrough_reaches(preferred_body, candidate.body, candidate.exit, cfg) {
            preferred_body
        } else {
            candidate.body
        };

    Some(GenericForTail {
        body: body_block,
        exit: candidate.exit,
        vars,
    })
}

/// Returns whether `start` reaches `target` through strict linear fallthrough blocks.
///
/// # Returns
/// - `true` when a monotonic fallthrough path reaches `target` before `stop_at`.
/// - `false` otherwise.
#[must_use]
fn linear_fallthrough_reaches(
    start: usize,
    target: usize,
    stop_at: usize,
    cfg: &ControlFlowGraph,
) -> bool {
    if start == target {
        return true;
    }
    if start >= cfg.blocks.len() || target >= cfg.blocks.len() || start >= stop_at {
        return false;
    }

    let mut seen = HashSet::new();
    let mut current = start;

    while seen.insert(current) && current < stop_at {
        let Some(block) = cfg.blocks.get(current) else {
            return false;
        };

        match block.exit {
            BlockExit::Fallthrough(next) if next == target => return true,
            BlockExit::Fallthrough(next) if next > current && next < stop_at => current = next,
            _ => return false,
        }
    }

    false
}

/// Returns whether the edge 'source -> destination' is a backedge.
#[must_use]
fn is_backedge(source: usize, destination: usize, cfg: &ControlFlowGraph) -> bool {
    // In a reducible CFG, an edge is a backedge if the destination dominates the source.
    cfg.dominates(destination, source)
}

/// Returns whether `start` can reach `target` through a non-`for` backedge.
#[must_use]
pub fn branch_has_plain_backedge(start: usize, target: usize, cfg: &ControlFlowGraph) -> bool {
    if is_backedge(target, start, cfg) {
        return true;
    }

    let mut stack = vec![start];
    let mut seen = HashSet::new();

    while let Some(block) = stack.pop() {
        if !seen.insert(block) {
            continue;
        }

        if cfg.successors(block).contains(&target)
            && !matches!(
                cfg.blocks.get(block).map(|b| &b.exit),
                Some(BlockExit::FornLoop { .. } | BlockExit::ForgLoop { .. })
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
/// # Returns
/// - `HashSet<usize>`: dominated reachable blocks from `start`, excluding `target`.
#[must_use]
fn forward_reachable_without_target(
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

/// Chooses the earliest shared block reachable from both loop branches.
///
/// # Returns
/// - the smallest shared reachable block id.
/// - `exit_branch` when no dominated shared point exists.
#[must_use]
pub fn find_loop_exit_block(
    header: usize,
    exit_branch: usize,
    backedge_branch: usize,
    cfg: &ControlFlowGraph,
) -> usize {
    let exit_reachable = forward_reachable_without_target(exit_branch, header, cfg);
    let backedge_reachable = forward_reachable_without_target(backedge_branch, header, cfg);

    exit_reachable
        .intersection(&backedge_reachable)
        .copied()
        .min()
        .unwrap_or(exit_branch)
}
