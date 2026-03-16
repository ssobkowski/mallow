use std::collections::HashSet;

use super::graph::{BlockExit, ControlFlowGraph};

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
            BlockExit::ForNPrep { base, loop_block } => {
                let (_, _, exit_block) = resolve_numeric_for_tail(current, base, loop_block, cfg)?;
                current = exit_block;
            }
            BlockExit::ForGPrep { base, loop_block } => {
                let (_, _, exit_block, _) =
                    resolve_generic_for_tail(current, base, loop_block, cfg)?;
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

/// Resolves the tail/body/exit for a numeric `for` loop preheader.
///
/// # Returns
/// - `Some((tail_block, body_block, exit_block))` for a recoverable numeric loop.
/// - `None` when no matching `FORNLOOP` shape is found.
#[must_use]
pub fn resolve_numeric_for_tail(
    prep_block: usize,
    base: usize,
    prep_target_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<(usize, usize, usize)> {
    if prep_block >= cfg.blocks.len() {
        return None;
    }

    let preferred_body = prep_block + 1;
    let mut candidates: HashSet<(usize, usize, usize)> = HashSet::new();

    if let Some(block) = cfg.blocks.get(prep_target_block)
        && let BlockExit::ForNLoop {
            base: loop_base,
            body_block,
            exit_block,
        } = block.exit
        && loop_base == base
    {
        candidates.insert((prep_target_block, body_block, exit_block));
    }

    for &pred in cfg.predecessors(prep_target_block) {
        if let Some(block) = cfg.blocks.get(pred)
            && let BlockExit::ForNLoop {
                base: loop_base,
                body_block,
                exit_block,
            } = block.exit
            && loop_base == base
            && exit_block == prep_target_block
        {
            candidates.insert((pred, body_block, exit_block));
        }
    }

    if preferred_body < cfg.blocks.len() {
        for &pred in cfg.predecessors(preferred_body) {
            if let Some(block) = cfg.blocks.get(pred)
                && let BlockExit::ForNLoop {
                    base: loop_base,
                    body_block,
                    exit_block,
                } = block.exit
                && loop_base == base
                && body_block == preferred_body
            {
                candidates.insert((pred, body_block, exit_block));
            }
        }
    }

    if candidates.is_empty()
        && let Some(loop_tails) = cfg.numeric_loops_by_base.get(&base)
    {
        for &tail in loop_tails {
            if let Some(block) = cfg.blocks.get(tail)
                && let BlockExit::ForNLoop {
                    body_block,
                    exit_block,
                    ..
                } = block.exit
            {
                candidates.insert((tail, body_block, exit_block));
            }
        }
    }

    candidates.into_iter().max_by_key(|(tail, body, exit)| {
        let mut score = 0usize;
        if *tail == prep_target_block {
            score += 8;
        }
        if *exit == prep_target_block {
            score += 4;
        }
        if *body == preferred_body {
            score += 2;
        }
        if cfg.dominates(prep_block, *body) {
            score += 1;
        }
        score
    })
}

/// Resolves the tail/body/exit/result-count for a generic `for` loop preheader.
///
/// # Returns
/// - `Some((tail_block, body_block, exit_block, result_count))` for a recoverable generic loop.
/// - `None` when no matching `FORGLOOP` shape is found.
#[must_use]
pub fn resolve_generic_for_tail(
    prep_block: usize,
    base: usize,
    prep_target_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<(usize, usize, usize, usize)> {
    if prep_block >= cfg.blocks.len() {
        return None;
    }

    let preferred_body = prep_block + 1;
    let mut candidates: HashSet<(usize, usize, usize, usize)> = HashSet::new();

    if let Some(block) = cfg.blocks.get(prep_target_block)
        && let BlockExit::ForGLoop {
            base: loop_base,
            body_block,
            exit_block,
            result_count,
        } = block.exit
        && loop_base == base
    {
        candidates.insert((prep_target_block, body_block, exit_block, result_count));
    }

    for &pred in cfg.predecessors(prep_target_block) {
        if let Some(block) = cfg.blocks.get(pred)
            && let BlockExit::ForGLoop {
                base: loop_base,
                body_block,
                exit_block,
                result_count,
            } = block.exit
            && loop_base == base
            && exit_block == prep_target_block
        {
            candidates.insert((pred, body_block, exit_block, result_count));
        }
    }

    if preferred_body < cfg.blocks.len() {
        for &pred in cfg.predecessors(preferred_body) {
            if let Some(block) = cfg.blocks.get(pred)
                && let BlockExit::ForGLoop {
                    base: loop_base,
                    body_block,
                    exit_block,
                    result_count,
                } = block.exit
                && loop_base == base
                && body_block == preferred_body
            {
                candidates.insert((pred, body_block, exit_block, result_count));
            }
        }
    }

    if candidates.is_empty()
        && let Some(loop_tails) = cfg.generic_loops_by_base.get(&base)
    {
        for &tail in loop_tails {
            if let Some(block) = cfg.blocks.get(tail)
                && let BlockExit::ForGLoop {
                    body_block,
                    exit_block,
                    result_count,
                    ..
                } = block.exit
            {
                candidates.insert((tail, body_block, exit_block, result_count));
            }
        }
    }

    let best = candidates.into_iter().max_by_key(|(tail, body, exit, _)| {
        let mut score = 0usize;
        if *tail == prep_target_block {
            score += 8;
        }
        if *exit == prep_target_block {
            score += 4;
        }
        if *body == preferred_body {
            score += 2;
        }
        if cfg.dominates(prep_block, *body) {
            score += 1;
        }
        score
    })?;

    let (tail, body, exit, result_count) = best;
    let body = if linear_fallthrough_reaches(preferred_body, body, exit, cfg) {
        preferred_body
    } else {
        body
    };

    Some((tail, body, exit, result_count))
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

/// Returns whether `start` can reach `target` through a non-`for` backedge.
#[must_use]
pub fn branch_has_plain_backedge(start: usize, target: usize, cfg: &ControlFlowGraph) -> bool {
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

#[cfg(test)]
mod tests {
    use crate::hil::cflow::graph::{Block, BlockExit, ControlFlowGraph};
    use crate::hil::ir::HilExpr;

    use super::{find_if_else_join, resolve_generic_for_tail, resolve_numeric_for_tail};

    #[test]
    fn find_if_else_join_detects_diamond_merge() {
        let cfg = ControlFlowGraph::new(
            vec![
                Block::new(
                    0,
                    vec![],
                    BlockExit::CondJump {
                        cond: HilExpr::Reg(0),
                        then_block: 1,
                        else_block: 2,
                    },
                ),
                Block::new(1, vec![], BlockExit::Jump(3)),
                Block::new(2, vec![], BlockExit::Fallthrough(3)),
                Block::new(3, vec![], BlockExit::Return(vec![])),
            ],
            0,
        );

        assert_eq!(find_if_else_join(1, 2, &cfg), Some(3));
    }

    #[test]
    fn resolve_numeric_for_tail_uses_predecessor_metadata() {
        let cfg = ControlFlowGraph::new(
            vec![
                Block::new(
                    0,
                    vec![],
                    BlockExit::ForNPrep {
                        base: 0,
                        loop_block: 3,
                    },
                ),
                Block::new(1, vec![], BlockExit::Fallthrough(2)),
                Block::new(
                    2,
                    vec![],
                    BlockExit::ForNLoop {
                        base: 0,
                        body_block: 1,
                        exit_block: 3,
                    },
                ),
                Block::new(3, vec![], BlockExit::Return(vec![])),
            ],
            0,
        );

        assert_eq!(resolve_numeric_for_tail(0, 0, 3, &cfg), Some((2, 1, 3)));
    }

    #[test]
    fn resolve_generic_for_tail_includes_linear_preheader_before_body() {
        let cfg = ControlFlowGraph::new(
            vec![
                Block::new(
                    0,
                    vec![],
                    BlockExit::ForGPrep {
                        base: 4,
                        loop_block: 3,
                    },
                ),
                Block::new(1, vec![], BlockExit::Fallthrough(2)),
                Block::new(2, vec![], BlockExit::Fallthrough(3)),
                Block::new(
                    3,
                    vec![],
                    BlockExit::ForGLoop {
                        base: 4,
                        body_block: 2,
                        exit_block: 4,
                        result_count: 2,
                    },
                ),
                Block::new(4, vec![], BlockExit::Return(vec![])),
            ],
            0,
        );

        assert_eq!(resolve_generic_for_tail(0, 4, 3, &cfg), Some((3, 1, 4, 2)));
    }
}
