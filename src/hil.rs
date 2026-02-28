use std::collections::{BTreeSet, HashMap, HashSet};

use crate::ast::{BinOp, UnOp};
use crate::disasm::Proto;
use crate::il::{Constant, Instr};
use crate::logging::verbose_enabled;

#[derive(Debug, Clone)]
pub enum Expr {
    Nil,
    Number(f64),
    String(String),
    Bool(bool),
    Local(u8),
    Upval(u8),
    Closure { proto: usize, captures: Vec<Expr> },
    Global(String),
    Import(String),
    GetField(Box<Expr>, String),
    GetIndex(Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    MethodCall(Box<Expr>, String, Vec<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Table(Vec<Expr>),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Assign { left: Expr, value: Expr },
    AssignMany { left: Vec<Expr>, value: Expr },
    Call { expr: Expr, args: Vec<Expr> },
    SetField { table: u8, key: String, value: Expr },
    Return(Vec<Expr>),
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: usize,
    pub stmts: Vec<Stmt>,
    pub exit: BlockExit,
}

#[derive(Debug, Clone)]
pub enum BlockExit {
    Jump(usize), // unconditional -> block id
    CondJump {
        cond: Expr,
        then_block: usize,
        else_block: usize,
    },
    ForNPrep {
        base: usize,
        loop_block: usize,
    },
    ForNLoop {
        base: usize,
        body_block: usize,
        exit_block: usize,
    },
    ForGPrep {
        base: usize,
        loop_block: usize,
    },
    ForGLoop {
        base: usize,
        body_block: usize,
        exit_block: usize,
        result_count: usize,
    },
    Return(Vec<Expr>),
    Fallthrough(usize), // no explicit jump, just continues
}

#[derive(Debug)]
pub struct ControlFlowGraph {
    pub blocks: Vec<Block>,
    pub entry_block: usize,
    pub successors: Vec<Vec<usize>>,
    pub predecessors: Vec<Vec<usize>>,
    pub dominators: Vec<Vec<usize>>,
    pub immediate_dominators: Vec<Option<usize>>,
    numeric_loops_by_base: HashMap<usize, Vec<usize>>,
    generic_loops_by_base: HashMap<usize, Vec<usize>>,
}

impl ControlFlowGraph {
    pub fn new(blocks: Vec<Block>, entry_block: usize) -> Self {
        let successors = build_successors(&blocks);
        let predecessors = build_predecessors(successors.len(), &successors);
        let (dominators, immediate_dominators) =
            build_dominator_metadata(entry_block, &successors, &predecessors);
        let (numeric_loops_by_base, generic_loops_by_base) = build_loop_indexes(&blocks);

        ControlFlowGraph {
            blocks,
            entry_block,
            successors,
            predecessors,
            dominators,
            immediate_dominators,
            numeric_loops_by_base,
            generic_loops_by_base,
        }
    }

    pub fn successors(&self, block: usize) -> &[usize] {
        self.successors
            .get(block)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub fn predecessors(&self, block: usize) -> &[usize] {
        self.predecessors
            .get(block)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub fn dominates(&self, dom: usize, node: usize) -> bool {
        self.dominators
            .get(node)
            .is_some_and(|doms| doms.contains(&dom))
    }

    pub fn immediate_dominator(&self, block: usize) -> Option<usize> {
        self.immediate_dominators.get(block).copied().flatten()
    }
}

fn exit_targets(exit: &BlockExit) -> [Option<usize>; 2] {
    match *exit {
        BlockExit::Jump(target) | BlockExit::Fallthrough(target) => [Some(target), None],
        BlockExit::CondJump {
            then_block,
            else_block,
            ..
        } => [Some(then_block), Some(else_block)],
        BlockExit::ForNPrep { loop_block, .. } | BlockExit::ForGPrep { loop_block, .. } => {
            [Some(loop_block), None]
        }
        BlockExit::ForNLoop {
            body_block,
            exit_block,
            ..
        }
        | BlockExit::ForGLoop {
            body_block,
            exit_block,
            ..
        } => [Some(body_block), Some(exit_block)],
        BlockExit::Return(_) => [None, None],
    }
}

fn build_successors(blocks: &[Block]) -> Vec<Vec<usize>> {
    let len = blocks.len();
    let mut successors = vec![Vec::new(); len];
    for (idx, block) in blocks.iter().enumerate() {
        for target in exit_targets(&block.exit).into_iter().flatten() {
            if target < len {
                successors[idx].push(target);
            }
        }
    }
    successors
}

fn build_predecessors(len: usize, successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut predecessors = vec![Vec::new(); len];
    for (src, targets) in successors.iter().enumerate() {
        for &target in targets {
            predecessors[target].push(src);
        }
    }
    predecessors
}

fn reachable_blocks(entry_block: usize, successors: &[Vec<usize>]) -> Vec<bool> {
    let mut reachable = vec![false; successors.len()];
    let mut stack = Vec::new();
    if entry_block < successors.len() {
        stack.push(entry_block);
    }

    while let Some(block) = stack.pop() {
        if reachable[block] {
            continue;
        }
        reachable[block] = true;
        for &next in &successors[block] {
            if !reachable[next] {
                stack.push(next);
            }
        }
    }
    reachable
}

fn build_dominator_metadata(
    entry_block: usize,
    successors: &[Vec<usize>],
    predecessors: &[Vec<usize>],
) -> (Vec<Vec<usize>>, Vec<Option<usize>>) {
    let len = successors.len();
    let reachable = reachable_blocks(entry_block, successors);
    let reachable_ids: Vec<usize> = reachable
        .iter()
        .enumerate()
        .filter_map(|(idx, &is_reachable)| is_reachable.then_some(idx))
        .collect();

    let mut dom = vec![vec![false; len]; len];
    for block in 0..len {
        if !reachable[block] {
            continue;
        }
        if block == entry_block {
            dom[block][entry_block] = true;
        } else {
            for &r in &reachable_ids {
                dom[block][r] = true;
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &block in &reachable_ids {
            if block == entry_block {
                continue;
            }

            let mut next_dom = vec![false; len];
            for &r in &reachable_ids {
                next_dom[r] = true;
            }

            let mut had_pred = false;
            for &pred in &predecessors[block] {
                if !reachable[pred] {
                    continue;
                }
                had_pred = true;
                for &r in &reachable_ids {
                    next_dom[r] &= dom[pred][r];
                }
            }

            if !had_pred {
                for &r in &reachable_ids {
                    next_dom[r] = false;
                }
            }
            next_dom[block] = true;

            if next_dom != dom[block] {
                dom[block] = next_dom;
                changed = true;
            }
        }
    }

    let dominators: Vec<Vec<usize>> = dom
        .iter()
        .map(|row| {
            row.iter()
                .enumerate()
                .filter_map(|(idx, &is_dom)| is_dom.then_some(idx))
                .collect()
        })
        .collect();

    let mut immediate_dominators = vec![None; len];
    for &block in &reachable_ids {
        if block == entry_block {
            continue;
        }

        let strict_doms: Vec<usize> = dominators[block]
            .iter()
            .copied()
            .filter(|&d| d != block)
            .collect();

        let idom = strict_doms.iter().copied().find(|&candidate| {
            strict_doms
                .iter()
                .copied()
                .filter(|&other| other != candidate)
                .all(|other| !dom[other][candidate])
        });
        immediate_dominators[block] = idom;
    }

    (dominators, immediate_dominators)
}

fn build_loop_indexes(
    blocks: &[Block],
) -> (HashMap<usize, Vec<usize>>, HashMap<usize, Vec<usize>>) {
    let mut numeric_loops_by_base: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut generic_loops_by_base: HashMap<usize, Vec<usize>> = HashMap::new();

    for (idx, block) in blocks.iter().enumerate() {
        match block.exit {
            BlockExit::ForNLoop { base, .. } => {
                numeric_loops_by_base.entry(base).or_default().push(idx)
            }
            BlockExit::ForGLoop { base, .. } => {
                generic_loops_by_base.entry(base).or_default().push(idx)
            }
            _ => {}
        }
    }

    (numeric_loops_by_base, generic_loops_by_base)
}

#[derive(Debug, Clone, Copy)]
enum LinearExit {
    Jump(usize),
    Fallthrough(usize),
    Other,
}

fn linear_exit_from(start: usize, cfg: &ControlFlowGraph) -> LinearExit {
    let mut seen = HashSet::new();
    let mut current = start;

    while seen.insert(current) {
        let Some(block) = cfg.blocks.get(current) else {
            return LinearExit::Other;
        };

        match block.exit {
            BlockExit::Fallthrough(next)
                if next == current + 1 && cfg.predecessors(next).len() <= 1 =>
            {
                current = next;
            }
            BlockExit::Fallthrough(next) => return LinearExit::Fallthrough(next),
            BlockExit::Jump(target) => return LinearExit::Jump(target),
            _ => return LinearExit::Other,
        }
    }

    LinearExit::Other
}

pub fn find_if_else_join(
    then_block: usize,
    else_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<usize> {
    let then_exit = linear_exit_from(then_block, cfg);
    let else_exit = linear_exit_from(else_block, cfg);

    let candidate = match (then_exit, else_exit) {
        (LinearExit::Jump(a), LinearExit::Fallthrough(b))
        | (LinearExit::Fallthrough(a), LinearExit::Jump(b))
            if a == b && a != then_block && a != else_block =>
        {
            a
        }
        _ => return None,
    };

    if cfg.dominates(candidate, then_block) || cfg.dominates(candidate, else_block) {
        return None;
    }

    Some(candidate)
}

pub fn resolve_numeric_for_tail(
    prep_block: usize,
    base: usize,
    prep_target_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<(usize, usize, usize)> {
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

pub fn resolve_generic_for_tail(
    prep_block: usize,
    base: usize,
    prep_target_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<(usize, usize, usize, usize)> {
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

    candidates.into_iter().max_by_key(|(tail, body, exit, _)| {
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

fn rel_target(next_pc: usize, offset: i16, instr_len: usize) -> usize {
    if instr_len == 0 {
        return 0;
    }

    let target = next_pc.saturating_add_signed(offset as isize);
    if target >= instr_len {
        instr_len - 1
    } else {
        target
    }
}

fn rel_target_from_instr(
    instr_idx: usize,
    offset: i16,
    instrs: &[Instr],
    instr_word_pcs: Option<&[usize]>,
) -> usize {
    if instrs.is_empty() {
        return 0;
    }

    let Some(word_pcs) = instr_word_pcs else {
        return rel_target(instr_idx + 1, offset, instrs.len());
    };

    if instr_idx >= instrs.len() || word_pcs.len() != instrs.len() {
        return rel_target(instr_idx + 1, offset, instrs.len());
    }

    let next_word_pc = word_pcs[instr_idx].saturating_add(instrs[instr_idx].word_len());
    let raw = next_word_pc as isize + offset as isize;
    let target_word_pc = if raw < 0 { 0usize } else { raw as usize };

    match word_pcs.binary_search(&target_word_pc) {
        Ok(idx) => idx,
        Err(0) => 0,
        Err(pos) if pos >= instrs.len() => instrs.len() - 1,
        Err(pos) => pos - 1,
    }
}

fn pc_to_block_idx(entries: &[usize], pc: usize) -> usize {
    entries.partition_point(|&e| e <= pc) - 1
}

fn const_string(consts: &[Constant], index: u32) -> String {
    match consts.get(index as usize) {
        Some(Constant::String(s)) => s.clone(),
        _ => format!("k{}", index),
    }
}

fn is_lua_ident(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) if c == '_' || c.is_ascii_alphabetic() => {}
        _ => return false,
    }

    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn escape_lua_string(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn decode_import_path(consts: &[Constant], path: u32) -> Option<String> {
    let count = (path >> 30) as usize;
    if !(1..=3).contains(&count) {
        return None;
    }

    let ids = [(path >> 20) & 0x3ff, (path >> 10) & 0x3ff, path & 0x3ff];

    let first = const_string(consts, ids[0]);
    let mut out = if is_lua_ident(&first) {
        first
    } else {
        format!("_G[\"{}\"]", escape_lua_string(&first))
    };

    for id in ids.iter().skip(1).take(count - 1) {
        let key = const_string(consts, *id);
        if is_lua_ident(&key) {
            out.push('.');
            out.push_str(&key);
        } else {
            out.push_str(&format!("[\"{}\"]", escape_lua_string(&key)));
        }
    }

    Some(out)
}

fn const_expr(consts: &[Constant], index: usize) -> Expr {
    match consts.get(index) {
        Some(Constant::String(s)) => Expr::String(s.clone()),
        Some(Constant::Number(n)) => Expr::Number(*n),
        Some(Constant::Boolean(b)) => Expr::Bool(*b),
        Some(Constant::Nil) => Expr::Nil,
        Some(_) => panic!("unsupported constant kind for lifted expression at index {index}"),
        None => panic!("constant index out of bounds while lifting: {index}"),
    }
}

fn decoded_count(encoded: u8) -> Option<u8> {
    if encoded == 0 {
        None
    } else {
        Some(encoded - 1)
    }
}

fn local_range(start: u8, count: u8) -> Vec<Expr> {
    (0..count)
        .map(|i| Expr::Local(start.wrapping_add(i)))
        .collect()
}

fn return_values(base: u8, count: u8) -> Vec<Expr> {
    match decoded_count(count) {
        Some(n) => local_range(base, n),
        // Luau uses count=0 for MULTRET. We model this as returning the base register.
        None => vec![Expr::Local(base)],
    }
}

fn call_stmt(expr: Expr) -> Stmt {
    let args = match &expr {
        Expr::Call(_, args) | Expr::MethodCall(_, _, args) => args.clone(),
        _ => Vec::new(),
    };
    Stmt::Call { expr, args }
}

pub fn lift(instrs: &[Instr], consts: &[Constant]) -> Vec<Stmt> {
    lift_with_context(instrs, consts, None, &[])
}

fn resolve_newclosure_proto(parent_proto: Option<&Proto>, proto_idx: u16) -> usize {
    parent_proto
        .and_then(|proto| proto.protos.get(usize::from(proto_idx)).copied())
        .unwrap_or(usize::from(proto_idx))
}

fn resolve_dupclosure_proto(consts: &[Constant], k: u16) -> usize {
    match consts.get(usize::from(k)) {
        Some(Constant::Closure(proto_idx)) => usize::try_from(*proto_idx).unwrap_or(usize::from(k)),
        _ => usize::from(k),
    }
}

fn decode_capture(capture_type: u8, reg: u8) -> Expr {
    match capture_type {
        0 | 1 => Expr::Local(reg),
        2 => Expr::Upval(reg),
        _ => Expr::Local(reg),
    }
}

fn lift_with_context(
    instrs: &[Instr],
    consts: &[Constant],
    parent_proto: Option<&Proto>,
    all_protos: &[Proto],
) -> Vec<Stmt> {
    let mut stmts = Vec::new();

    let mut pending_namecall: Option<(u8, String)> = None; // (func reg, method)
    let mut pending_multret_call: Option<(u8, Expr)> = None; // (first result reg, call expr)
    let mut pending_closure_stmt: Option<(usize, usize)> = None; // (stmt index, remaining fixed captures)

    for (instr_idx, instr) in instrs.iter().enumerate() {
        let consumes_pending_multret = matches!(
            instr,
            Instr::Call {
                func,
                arg_count: 0,
                ..
            } if pending_multret_call
                .as_ref()
                .is_some_and(|(src_reg, _)| *src_reg == *func + 1)
        ) || matches!(
            instr,
            Instr::SetList {
                base,
                count: 0,
                ..
            } if pending_multret_call
                .as_ref()
                .is_some_and(|(src_reg, _)| *src_reg == *base)
        );

        if !consumes_pending_multret && let Some((_, expr)) = pending_multret_call.take() {
            stmts.push(call_stmt(expr));
        }

        if !matches!(instr, Instr::Call { .. } | Instr::NameCall { .. }) {
            pending_namecall = None;
        }
        if !matches!(instr, Instr::Capture { .. }) {
            pending_closure_stmt = None;
        }

        match instr {
            Instr::Nop => {}
            Instr::LoadNil { reg } => stmts.push(Stmt::Assign {
                left: Expr::Local(*reg),
                value: Expr::Nil,
            }),
            Instr::LoadB { reg, value, .. } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*reg),
                    value: Expr::Bool(*value),
                });
            }
            Instr::LoadN { reg, value } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*reg),
                    value: Expr::Number(*value as f64),
                });
            }
            Instr::LoadK { reg, index } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*reg),
                    value: const_expr(consts, usize::from(*index)),
                });
            }
            Instr::GetGlobal { dest, key, .. } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Global(const_string(consts, *key)),
                });
            }
            Instr::SetGlobal { src, key, .. } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Global(const_string(consts, *key)),
                    value: Expr::Local(*src),
                });
            }
            Instr::GetUpval { dest, upval } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Upval(*upval),
                });
            }
            Instr::SetUpval { src, upval } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Upval(*upval),
                    value: Expr::Local(*src),
                });
            }
            Instr::Move { dest, src } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Local(*src),
                });
            }
            Instr::GetImport { dest, index, path } => {
                let import = decode_import_path(consts, *path)
                    .unwrap_or_else(|| format!("import_k{}", index));
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Import(import),
                });
            }
            Instr::NameCall {
                dest,
                object,
                method,
                ..
            } => {
                pending_namecall = Some((*dest, const_string(consts, *method)));
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest + 1),
                    value: Expr::Local(*object),
                });
            }
            Instr::Call {
                func,
                arg_count,
                ret_count,
            } => {
                let mut consumed_multret = false;

                let args = match decoded_count(*arg_count) {
                    Some(argc) => {
                        if argc > 0 {
                            local_range(*func + 1, argc)
                        } else {
                            Vec::new()
                        }
                    }
                    None => {
                        if let Some((src_reg, expr)) = pending_multret_call.take() {
                            if src_reg == *func + 1 {
                                consumed_multret = true;
                                vec![expr]
                            } else {
                                pending_multret_call = Some((src_reg, expr));
                                Vec::new()
                            }
                        } else {
                            Vec::new()
                        }
                    }
                };

                if let Some((nc_reg, method)) = pending_namecall.take()
                    && nc_reg == *func
                {
                    // NAMECALL stores the receiver at R(A+1). CALL's arg_count includes this receiver.
                    let method_args = match decoded_count(*arg_count) {
                        Some(argc) if argc > 1 => local_range(*func + 2, argc - 1),
                        None if consumed_multret => args,
                        _ => Vec::new(),
                    };
                    let method_call =
                        Expr::MethodCall(Box::new(Expr::Local(*func + 1)), method, method_args);
                    match decoded_count(*ret_count) {
                        Some(0) => stmts.push(call_stmt(method_call)),
                        Some(1) => stmts.push(Stmt::Assign {
                            left: Expr::Local(*func),
                            value: method_call,
                        }),
                        Some(n) => stmts.push(Stmt::AssignMany {
                            left: local_range(*func, n),
                            value: method_call,
                        }),
                        None => {
                            pending_multret_call = Some((*func, method_call));
                        }
                    }
                    continue;
                }

                let call = Expr::Call(Box::new(Expr::Local(*func)), args);
                match decoded_count(*ret_count) {
                    Some(0) => stmts.push(call_stmt(call)),
                    Some(1) => stmts.push(Stmt::Assign {
                        left: Expr::Local(*func),
                        value: call,
                    }),
                    Some(n) => stmts.push(Stmt::AssignMany {
                        left: local_range(*func, n),
                        value: call,
                    }),
                    None => {
                        pending_multret_call = Some((*func, call));
                    }
                }
            }
            Instr::Return { base, count } => {
                let rets = return_values(*base, *count);
                stmts.push(Stmt::Return(rets));
            }
            Instr::GetTableKS {
                dest, table, key, ..
            } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::GetField(
                        Box::new(Expr::Local(*table)),
                        const_string(consts, *key),
                    ),
                });
            }
            Instr::GetTable { dest, table, key } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::GetIndex(
                        Box::new(Expr::Local(*table)),
                        Box::new(Expr::Local(*key)),
                    ),
                });
            }
            Instr::GetTableN { dest, table, index } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::GetIndex(
                        Box::new(Expr::Local(*table)),
                        Box::new(Expr::Number(*index as f64)),
                    ),
                });
            }
            Instr::SetTableKS {
                src, table, key, ..
            } => {
                stmts.push(Stmt::SetField {
                    table: *table,
                    key: const_string(consts, *key),
                    value: Expr::Local(*src),
                });
            }
            Instr::SetTableN { src, table, index } => {
                stmts.push(Stmt::Assign {
                    left: Expr::GetIndex(
                        Box::new(Expr::Local(*table)),
                        Box::new(Expr::Number(*index as f64)),
                    ),
                    value: Expr::Local(*src),
                });
            }
            Instr::Add { dest, a, b } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Add,
                        Box::new(Expr::Local(*a)),
                        Box::new(Expr::Local(*b)),
                    ),
                });
            }
            Instr::Sub { dest, a, b } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Sub,
                        Box::new(Expr::Local(*a)),
                        Box::new(Expr::Local(*b)),
                    ),
                });
            }
            Instr::Mul { dest, a, b } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Mul,
                        Box::new(Expr::Local(*a)),
                        Box::new(Expr::Local(*b)),
                    ),
                });
            }
            Instr::Div { dest, a, b } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Div,
                        Box::new(Expr::Local(*a)),
                        Box::new(Expr::Local(*b)),
                    ),
                });
            }
            Instr::Mod { dest, a, b } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Mod,
                        Box::new(Expr::Local(*a)),
                        Box::new(Expr::Local(*b)),
                    ),
                });
            }
            Instr::Pow { dest, a, b } => {
                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Pow,
                        Box::new(Expr::Local(*a)),
                        Box::new(Expr::Local(*b)),
                    ),
                });
            }
            Instr::AddK { dest, reg, k } => {
                let num = match consts[*k as usize] {
                    Constant::Number(x) => x,
                    _ => unreachable!("AddK can only be used with constant numbers"),
                };

                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Add,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Number(num)),
                    ),
                });
            }
            Instr::SubK { dest, reg, k } => {
                let num = match consts[*k as usize] {
                    Constant::Number(x) => x,
                    _ => unreachable!("SubK can only be used with constant numbers"),
                };

                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Sub,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Number(num)),
                    ),
                });
            }
            Instr::MulK { dest, reg, k } => {
                let num = match consts[*k as usize] {
                    Constant::Number(x) => x,
                    _ => unreachable!("MulK can only be used with constant numbers"),
                };

                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Mul,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Number(num)),
                    ),
                });
            }
            Instr::DivK { dest, reg, k } => {
                let num = match consts[*k as usize] {
                    Constant::Number(x) => x,
                    _ => unreachable!("DivK can only be used with constant numbers"),
                };

                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Div,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Number(num)),
                    ),
                });
            }
            Instr::ModK { dest, reg, k } => {
                let num = match consts[*k as usize] {
                    Constant::Number(x) => x,
                    _ => unreachable!("ModK can only be used with constant numbers"),
                };

                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Mod,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Number(num)),
                    ),
                });
            }
            Instr::PowK { dest, reg, k } => {
                let num = match consts[*k as usize] {
                    Constant::Number(x) => x,
                    _ => unreachable!("PowK can only be used with constant numbers"),
                };

                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Binary(
                        BinOp::Pow,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Number(num)),
                    ),
                });
            }
            Instr::And { dest, a, b } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Binary(
                    BinOp::And,
                    Box::new(Expr::Local(*a)),
                    Box::new(Expr::Local(*b)),
                ),
            }),
            Instr::Or { dest, a, b } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Binary(
                    BinOp::Or,
                    Box::new(Expr::Local(*a)),
                    Box::new(Expr::Local(*b)),
                ),
            }),
            Instr::AndK { dest, reg, k } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Binary(
                    BinOp::And,
                    Box::new(Expr::Local(*reg)),
                    Box::new(const_expr(consts, usize::from(*k))),
                ),
            }),
            Instr::OrK { dest, reg, k } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Binary(
                    BinOp::Or,
                    Box::new(Expr::Local(*reg)),
                    Box::new(const_expr(consts, usize::from(*k))),
                ),
            }),
            Instr::Concat { dest, a, b } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Binary(
                    BinOp::Concat,
                    Box::new(Expr::Local(*a)),
                    Box::new(Expr::Local(*b)),
                ),
            }),
            Instr::Not { dest, reg } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Unary(UnOp::Not, Box::new(Expr::Local(*reg))),
            }),
            Instr::Minus { dest, reg } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Unary(UnOp::Minus, Box::new(Expr::Local(*reg))),
            }),
            Instr::Length { dest, reg } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Unary(UnOp::Length, Box::new(Expr::Local(*reg))),
            }),
            Instr::NewTable {
                dest, array_size, ..
            } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Call(
                    Box::new(Expr::GetField(
                        Box::new(Expr::Global("table".to_string())),
                        "create".to_string(),
                    )),
                    vec![Expr::Number(*array_size as f64)],
                ),
            }),
            Instr::DupTable { dest, .. } => stmts.push(Stmt::Assign {
                left: Expr::Local(*dest),
                value: Expr::Table(Vec::new()),
            }),
            Instr::SetTable { src, table, key } => {
                stmts.push(Stmt::Assign {
                    left: Expr::GetIndex(
                        Box::new(Expr::Local(*table)),
                        Box::new(Expr::Local(*key)),
                    ),
                    value: Expr::Local(*src),
                });
            }
            Instr::SetList {
                table,
                base,
                count,
                index,
            } => {
                let start = *index;
                match decoded_count(*count) {
                    Some(n) => {
                        for i in 0..n {
                            stmts.push(Stmt::Assign {
                                left: Expr::GetIndex(
                                    Box::new(Expr::Local(*table)),
                                    Box::new(Expr::Number((start + u32::from(i)) as f64)),
                                ),
                                value: Expr::Local(base.wrapping_add(i)),
                            });
                        }
                    }
                    None => {
                        let value = if let Some((src_reg, expr)) = pending_multret_call.take() {
                            if src_reg == *base {
                                expr
                            } else {
                                pending_multret_call = Some((src_reg, expr));
                                Expr::Local(*base)
                            }
                        } else {
                            Expr::Local(*base)
                        };

                        stmts.push(Stmt::Assign {
                            left: Expr::GetIndex(
                                Box::new(Expr::Local(*table)),
                                Box::new(Expr::Number(start as f64)),
                            ),
                            value,
                        });
                    }
                }
            }
            Instr::NewClosure { dest, proto } => {
                let resolved_proto = resolve_newclosure_proto(parent_proto, *proto);
                let expected_captures = all_protos
                    .get(resolved_proto)
                    .map_or(0usize, |p| usize::from(p.num_upvals));

                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Closure {
                        proto: resolved_proto,
                        captures: Vec::new(),
                    },
                });
                pending_closure_stmt = Some((stmts.len() - 1, expected_captures));
            }
            Instr::DupClosure { dest, k } => {
                let resolved_proto = resolve_dupclosure_proto(consts, *k);
                let expected_captures = all_protos
                    .get(resolved_proto)
                    .map_or(0usize, |p| usize::from(p.num_upvals));

                stmts.push(Stmt::Assign {
                    left: Expr::Local(*dest),
                    value: Expr::Closure {
                        proto: resolved_proto,
                        captures: Vec::new(),
                    },
                });
                pending_closure_stmt = Some((stmts.len() - 1, expected_captures));
            }
            // None of these matter for decompilation purposes.
            Instr::FastCall1 { .. }
            | Instr::FastCall2 { .. }
            | Instr::FastCall2K { .. }
            | Instr::FastCall3 { .. }
            | Instr::FastCall { .. }
            | Instr::PrepVarArgs { .. } => {}
            Instr::Capture { capture_type, reg } => {
                if let Some((stmt_idx, remaining)) = pending_closure_stmt
                    && let Some(Stmt::Assign {
                        value: Expr::Closure { captures, .. },
                        ..
                    }) = stmts.get_mut(stmt_idx)
                {
                    captures.push(decode_capture(*capture_type, *reg));
                    if remaining > 0 {
                        pending_closure_stmt = if remaining == 1 {
                            None
                        } else {
                            Some((stmt_idx, remaining - 1))
                        };
                    }
                }
            }
            Instr::CloseUpvals { reg } => {
                if verbose_enabled() {
                    let proto = parent_proto
                        .map(|p| p.index.to_string())
                        .unwrap_or_else(|| "?".to_string());
                    eprintln!(
                        "[lift] ignored CLOSEUPVALS in proto {proto} at instr #{instr_idx}: reg={reg}"
                    );
                }
            }
            other => {
                if verbose_enabled() {
                    let proto = parent_proto
                        .map(|p| p.index.to_string())
                        .unwrap_or_else(|| "?".to_string());
                    eprintln!(
                        "[lift] unsupported instruction in proto {proto} at instr #{instr_idx}: {:#?}",
                        other
                    );
                } else {
                    eprintln!("Unsupported instruction: {:#?}", other);
                }
            }
        }
    }

    if let Some((_, expr)) = pending_multret_call.take() {
        stmts.push(call_stmt(expr));
    }

    stmts
}

pub fn build_cfg(instrs: &[Instr], consts: &[Constant]) -> ControlFlowGraph {
    build_cfg_with_context(instrs, consts, None, &[])
}

pub fn build_cfg_for_proto(proto: &Proto, all_protos: &[Proto]) -> ControlFlowGraph {
    build_cfg_with_context(&proto.instrs, &proto.consts, Some(proto), all_protos)
}

fn build_cfg_with_context(
    instrs: &[Instr],
    consts: &[Constant],
    parent_proto: Option<&Proto>,
    all_protos: &[Proto],
) -> ControlFlowGraph {
    let instr_word_pcs = parent_proto.and_then(|proto| {
        if proto.instr_word_pcs.len() == instrs.len() && !proto.instr_word_pcs.is_empty() {
            Some(proto.instr_word_pcs.as_slice())
        } else {
            None
        }
    });

    // Pass 1: find all block entry points
    let mut entries = BTreeSet::new();
    entries.insert(0);

    for (i, instr) in instrs.iter().enumerate() {
        match instr {
            Instr::FornPrep { offset, .. }
            | Instr::ForgPrep { offset, .. }
            | Instr::ForgPrepInext { offset, .. }
            | Instr::ForgPrepNext { offset, .. } => {
                entries.insert(rel_target_from_instr(i, *offset, instrs, instr_word_pcs));
                entries.insert(i + 1); // body entry
            }
            Instr::FornLoop { offset, .. } | Instr::ForgLoop { offset, .. } => {
                entries.insert(rel_target_from_instr(i, *offset, instrs, instr_word_pcs));
                entries.insert(i + 1); // loop exit entry
            }
            Instr::Jump { offset }
            | Instr::JumpBack { offset }
            | Instr::JumpIf { offset, .. }
            | Instr::JumpIfNot { offset, .. }
            | Instr::JumpIfEq { offset, .. }
            | Instr::JumpIfLe { offset, .. }
            | Instr::JumpIfLt { offset, .. }
            | Instr::JumpIfNotEq { offset, .. }
            | Instr::JumpIfNotLe { offset, .. }
            | Instr::JumpIfNotLt { offset, .. }
            | Instr::JumpXEqKNil { offset, .. }
            | Instr::JumpXEqKB { offset, .. }
            | Instr::JumpXEqKN { offset, .. }
            | Instr::JumpXEqKS { offset, .. } => {
                entries.insert(rel_target_from_instr(i, *offset, instrs, instr_word_pcs));
                entries.insert(i + 1); // fallthrough is also an entry
            }
            _ => {}
        }
    }

    let entries_vec: Vec<usize> = entries.into_iter().collect(); // already sorted, BTreeSet
    let mut blocks = Vec::new();

    for (block_idx, &start) in entries_vec.iter().enumerate() {
        let end = entries_vec
            .get(block_idx + 1)
            .copied()
            .unwrap_or(instrs.len());

        let block_instrs = &instrs[start..end];
        let last = block_instrs.last();

        let (body, exit_instr) = match last {
            Some(Instr::Return { .. })
            | Some(Instr::Jump { .. })
            | Some(Instr::JumpBack { .. })
            | Some(Instr::JumpIf { .. })
            | Some(Instr::JumpIfNot { .. })
            | Some(Instr::JumpIfEq { .. })
            | Some(Instr::JumpIfLe { .. })
            | Some(Instr::JumpIfLt { .. })
            | Some(Instr::JumpIfNotEq { .. })
            | Some(Instr::JumpIfNotLe { .. })
            | Some(Instr::JumpIfNotLt { .. })
            | Some(Instr::JumpXEqKNil { .. })
            | Some(Instr::JumpXEqKB { .. })
            | Some(Instr::JumpXEqKN { .. })
            | Some(Instr::JumpXEqKS { .. })
            | Some(Instr::FornPrep { .. })
            | Some(Instr::FornLoop { .. })
            | Some(Instr::ForgPrep { .. })
            | Some(Instr::ForgPrepInext { .. })
            | Some(Instr::ForgPrepNext { .. })
            | Some(Instr::ForgLoop { .. }) => (&block_instrs[..block_instrs.len() - 1], last),
            _ => (block_instrs, None),
        };

        let exit = match exit_instr {
            Some(Instr::Return { base, count }) => {
                let rets = return_values(*base, *count);
                BlockExit::Return(rets)
            }
            Some(Instr::Jump { offset }) | Some(Instr::JumpBack { offset }) => {
                let target =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let target_block = pc_to_block_idx(&entries_vec, target);
                BlockExit::Jump(target_block)
            }
            Some(Instr::JumpIfNotLt { reg, aux, offset }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                BlockExit::CondJump {
                    cond: Expr::Binary(
                        BinOp::Lt,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Local(*aux)),
                    ),
                    then_block: fallthrough_block, // condition was TRUE, didn't jump
                    else_block: taken_block,       // condition was FALSE, jumped
                }
            }
            Some(Instr::JumpIf { reg, offset }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                BlockExit::CondJump {
                    cond: Expr::Local(*reg),
                    then_block: taken_block,       // jumped
                    else_block: fallthrough_block, // no jump
                }
            }
            Some(Instr::JumpIfNot { reg, offset }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                BlockExit::CondJump {
                    cond: Expr::Local(*reg),
                    then_block: fallthrough_block, // no jump
                    else_block: taken_block,       // jumped
                }
            }
            Some(Instr::JumpIfEq { reg, aux, offset }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                BlockExit::CondJump {
                    cond: Expr::Binary(
                        BinOp::Eq,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Local(*aux)),
                    ),
                    then_block: taken_block,       // jumped
                    else_block: fallthrough_block, // no jump
                }
            }
            Some(Instr::JumpIfLe { reg, aux, offset }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                BlockExit::CondJump {
                    cond: Expr::Binary(
                        BinOp::Lte,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Local(*aux)),
                    ),
                    then_block: taken_block,       // jumped
                    else_block: fallthrough_block, // no jump
                }
            }
            Some(Instr::JumpIfLt { reg, aux, offset }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                BlockExit::CondJump {
                    cond: Expr::Binary(
                        BinOp::Lt,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Local(*aux)),
                    ),
                    then_block: taken_block,       // jumped
                    else_block: fallthrough_block, // no jump
                }
            }
            Some(Instr::JumpIfNotEq { reg, aux, offset }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                BlockExit::CondJump {
                    cond: Expr::Binary(
                        BinOp::Eq,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Local(*aux)),
                    ),
                    then_block: fallthrough_block, // no jump
                    else_block: taken_block,       // jumped
                }
            }
            Some(Instr::JumpIfNotLe { reg, aux, offset }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                BlockExit::CondJump {
                    cond: Expr::Binary(
                        BinOp::Lte,
                        Box::new(Expr::Local(*reg)),
                        Box::new(Expr::Local(*aux)),
                    ),
                    then_block: fallthrough_block, // no jump
                    else_block: taken_block,       // jumped
                }
            }
            Some(Instr::JumpXEqKNil {
                reg,
                invert,
                offset,
            }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                let op = if *invert { BinOp::Ne } else { BinOp::Eq };

                BlockExit::CondJump {
                    cond: Expr::Binary(op, Box::new(Expr::Local(*reg)), Box::new(Expr::Nil)),
                    then_block: taken_block,
                    else_block: fallthrough_block,
                }
            }
            Some(Instr::JumpXEqKB {
                reg,
                k,
                invert,
                offset,
            }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                let op = if *invert { BinOp::Ne } else { BinOp::Eq };

                BlockExit::CondJump {
                    cond: Expr::Binary(op, Box::new(Expr::Local(*reg)), Box::new(Expr::Bool(*k))),
                    then_block: taken_block,
                    else_block: fallthrough_block,
                }
            }
            Some(Instr::JumpXEqKN {
                reg,
                k,
                invert,
                offset,
            })
            | Some(Instr::JumpXEqKS {
                reg,
                k,
                invert,
                offset,
            }) => {
                let taken =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                let taken_block = pc_to_block_idx(&entries_vec, taken);
                let fallthrough_block = block_idx + 1;
                let op = if *invert { BinOp::Ne } else { BinOp::Eq };

                BlockExit::CondJump {
                    cond: Expr::Binary(
                        op,
                        Box::new(Expr::Local(*reg)),
                        Box::new(const_expr(consts, *k as usize)),
                    ),
                    then_block: taken_block,
                    else_block: fallthrough_block,
                }
            }
            Some(Instr::FornPrep { base, offset }) => {
                let target =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                BlockExit::ForNPrep {
                    base: usize::from(*base),
                    loop_block: pc_to_block_idx(&entries_vec, target),
                }
            }
            Some(Instr::FornLoop { base, offset }) => {
                let target =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                BlockExit::ForNLoop {
                    base: usize::from(*base),
                    body_block: pc_to_block_idx(&entries_vec, target),
                    exit_block: block_idx + 1,
                }
            }
            Some(Instr::ForgPrep { base, offset })
            | Some(Instr::ForgPrepInext { base, offset })
            | Some(Instr::ForgPrepNext { base, offset }) => {
                let target =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                BlockExit::ForGPrep {
                    base: usize::from(*base),
                    loop_block: pc_to_block_idx(&entries_vec, target),
                }
            }
            Some(Instr::ForgLoop {
                base,
                offset,
                var_count,
                ..
            }) => {
                let target =
                    rel_target_from_instr(end.saturating_sub(1), *offset, instrs, instr_word_pcs);
                BlockExit::ForGLoop {
                    base: usize::from(*base),
                    body_block: pc_to_block_idx(&entries_vec, target),
                    exit_block: block_idx + 1,
                    result_count: usize::from(*var_count),
                }
            }
            _ => {
                // no explicit jump, falls through
                BlockExit::Fallthrough(block_idx + 1)
            }
        };

        blocks.push(Block {
            id: block_idx,
            stmts: lift_with_context(body, consts, parent_proto, all_protos),
            exit,
        });
    }

    ControlFlowGraph::new(blocks, 0)
}

#[cfg(test)]
mod tests {
    use super::{
        BinOp, Block, BlockExit, ControlFlowGraph, Expr, Stmt, build_cfg, build_cfg_for_proto,
        find_if_else_join, lift, resolve_generic_for_tail, resolve_numeric_for_tail,
    };
    use crate::disasm::Proto;
    use crate::il::{Constant, Instr};

    #[test]
    fn lift_namecall_call_assigns_result_and_keeps_explicit_args() {
        let consts = vec![Constant::String("FindFirstChild".to_string())];
        let instrs = vec![
            Instr::NameCall {
                dest: 0,
                object: 2,
                slot: 0,
                method: 0,
            },
            Instr::Call {
                func: 0,
                arg_count: 3,
                ret_count: 2,
            },
        ];

        let stmts = lift(&instrs, &consts);
        assert_eq!(stmts.len(), 2);

        match &stmts[0] {
            Stmt::Assign { left, value } => {
                assert!(matches!(left, Expr::Local(1)));
                assert!(matches!(value, Expr::Local(2)));
            }
            _ => panic!("expected NAMECALL receiver move"),
        }

        match &stmts[1] {
            Stmt::Assign { left, value } => {
                assert!(matches!(left, Expr::Local(0)));

                match value {
                    Expr::MethodCall(base, method, args) => {
                        assert!(matches!(base.as_ref(), Expr::Local(1)));
                        assert_eq!(method, "FindFirstChild");
                        assert_eq!(args.len(), 1);
                        assert!(matches!(args[0], Expr::Local(2)));
                    }
                    _ => panic!("expected method call assignment"),
                }
            }
            _ => panic!("expected CALL with return to be assignment"),
        }
    }

    #[test]
    fn lift_plain_call_assigns_when_call_returns_value() {
        let instrs = vec![Instr::Call {
            func: 3,
            arg_count: 2,
            ret_count: 2,
        }];

        let stmts = lift(&instrs, &[]);
        assert_eq!(stmts.len(), 1);

        match &stmts[0] {
            Stmt::Assign { left, value } => {
                assert!(matches!(left, Expr::Local(3)));
                match value {
                    Expr::Call(func, args) => {
                        assert!(matches!(func.as_ref(), Expr::Local(3)));
                        assert_eq!(args.len(), 1);
                        assert!(matches!(args[0], Expr::Local(4)));
                    }
                    _ => panic!("expected call expression"),
                }
            }
            _ => panic!("expected assignment"),
        }
    }

    #[test]
    fn lift_plain_call_stmt_keeps_args() {
        let instrs = vec![Instr::Call {
            func: 3,
            arg_count: 3,
            ret_count: 1,
        }];

        let stmts = lift(&instrs, &[]);
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Stmt::Call { expr, args } => {
                assert_eq!(args.len(), 2);
                assert!(matches!(args[0], Expr::Local(4)));
                assert!(matches!(args[1], Expr::Local(5)));
                match expr {
                    Expr::Call(func, call_args) => {
                        assert!(matches!(func.as_ref(), Expr::Local(3)));
                        assert_eq!(call_args.len(), 2);
                        assert!(matches!(call_args[0], Expr::Local(4)));
                        assert!(matches!(call_args[1], Expr::Local(5)));
                    }
                    _ => panic!("expected call expression"),
                }
            }
            _ => panic!("expected call statement"),
        }
    }

    #[test]
    fn lift_namecall_stmt_keeps_explicit_args() {
        let consts = vec![Constant::String("FindFirstChild".to_string())];
        let instrs = vec![
            Instr::NameCall {
                dest: 0,
                object: 2,
                slot: 0,
                method: 0,
            },
            Instr::Call {
                func: 0,
                arg_count: 3,
                ret_count: 1,
            },
        ];

        let stmts = lift(&instrs, &consts);
        assert_eq!(stmts.len(), 2);
        match &stmts[1] {
            Stmt::Call { expr, args } => {
                assert_eq!(args.len(), 1);
                assert!(matches!(args[0], Expr::Local(2)));
                match expr {
                    Expr::MethodCall(base, method, method_args) => {
                        assert!(matches!(base.as_ref(), Expr::Local(1)));
                        assert_eq!(method, "FindFirstChild");
                        assert_eq!(method_args.len(), 1);
                        assert!(matches!(method_args[0], Expr::Local(2)));
                    }
                    _ => panic!("expected method call expression"),
                }
            }
            _ => panic!("expected call statement"),
        }
    }

    #[test]
    fn lift_andk_and_ork_use_constant_rhs() {
        let consts = vec![
            Constant::Boolean(false),
            Constant::String("fallback".to_string()),
        ];
        let instrs = vec![
            Instr::AndK {
                dest: 0,
                reg: 1,
                k: 0,
            },
            Instr::OrK {
                dest: 2,
                reg: 3,
                k: 1,
            },
        ];

        let stmts = lift(&instrs, &consts);
        assert_eq!(stmts.len(), 2);

        match &stmts[0] {
            Stmt::Assign { left, value } => {
                assert!(matches!(left, Expr::Local(0)));
                assert!(matches!(
                    value,
                    Expr::Binary(BinOp::And, a, b)
                        if matches!(a.as_ref(), Expr::Local(1))
                            && matches!(b.as_ref(), Expr::Bool(false))
                ));
            }
            _ => panic!("expected ANDK assignment"),
        }

        match &stmts[1] {
            Stmt::Assign { left, value } => {
                assert!(matches!(left, Expr::Local(2)));
                assert!(matches!(
                    value,
                    Expr::Binary(BinOp::Or, a, b)
                        if matches!(a.as_ref(), Expr::Local(3))
                            && matches!(b.as_ref(), Expr::String(s) if s == "fallback")
                ));
            }
            _ => panic!("expected ORK assignment"),
        }
    }

    #[test]
    fn lift_getimport_decodes_path_segments() {
        let consts = vec![
            Constant::String("game".to_string()),
            Constant::String("ReplicatedStorage".to_string()),
            Constant::Import(0),
        ];
        let path = (2u32 << 30) | (0u32 << 20) | (1u32 << 10);
        let instrs = vec![Instr::GetImport {
            dest: 5,
            index: 2,
            path,
        }];

        let stmts = lift(&instrs, &consts);
        assert_eq!(stmts.len(), 1);

        match &stmts[0] {
            Stmt::Assign { left, value } => {
                assert!(matches!(left, Expr::Local(5)));
                assert!(matches!(value, Expr::Import(name) if name == "game.ReplicatedStorage"));
            }
            _ => panic!("expected GETIMPORT assignment"),
        }
    }

    #[test]
    fn lift_getimport_uses_bracket_access_for_non_identifier_segment() {
        let consts = vec![
            Constant::String("game".to_string()),
            Constant::String("Not-An-Ident".to_string()),
            Constant::Import(0),
        ];
        let path = (2u32 << 30) | (0u32 << 20) | (1u32 << 10);
        let instrs = vec![Instr::GetImport {
            dest: 0,
            index: 2,
            path,
        }];

        let stmts = lift(&instrs, &consts);
        assert_eq!(stmts.len(), 1);

        match &stmts[0] {
            Stmt::Assign { value, .. } => {
                assert!(matches!(
                    value,
                    Expr::Import(name) if name == "game[\"Not-An-Ident\"]"
                ));
            }
            _ => panic!("expected GETIMPORT assignment"),
        }
    }

    #[test]
    fn lift_multret_call_chain_into_vararg_call_argument() {
        let consts = vec![
            Constant::String("pairs".to_string()),
            Constant::String("getconnections".to_string()),
        ];
        let instrs = vec![
            Instr::GetGlobal {
                dest: 1,
                slot: 0,
                key: 0,
            },
            Instr::GetGlobal {
                dest: 2,
                slot: 0,
                key: 1,
            },
            Instr::Call {
                func: 2,
                arg_count: 2,
                ret_count: 0,
            },
            Instr::Call {
                func: 1,
                arg_count: 0,
                ret_count: 4,
            },
        ];

        let stmts = lift(&instrs, &consts);
        assert_eq!(stmts.len(), 3);

        match &stmts[2] {
            Stmt::AssignMany { left, value } => {
                assert!(matches!(
                    left.as_slice(),
                    [Expr::Local(1), Expr::Local(2), Expr::Local(3)]
                ));

                match value {
                    Expr::Call(func, args) => {
                        assert!(matches!(func.as_ref(), Expr::Local(1)));
                        assert_eq!(args.len(), 1);
                        match &args[0] {
                            Expr::Call(inner_func, inner_args) => {
                                assert!(matches!(inner_func.as_ref(), Expr::Local(2)));
                                assert_eq!(inner_args.len(), 1);
                                assert!(matches!(inner_args[0], Expr::Local(3)));
                            }
                            _ => panic!("expected nested call from MULTRET chain"),
                        }
                    }
                    _ => panic!("expected call expression"),
                }
            }
            _ => panic!("expected multi-assignment for 3 return values"),
        }
    }

    #[test]
    fn lift_multret_return_uses_base_register() {
        let instrs = vec![Instr::Return { base: 4, count: 0 }];
        let stmts = lift(&instrs, &[]);

        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Stmt::Return(vals) => {
                assert!(matches!(vals.as_slice(), [Expr::Local(4)]));
            }
            _ => panic!("expected return statement"),
        }

        let cfg = build_cfg(&instrs, &[]);
        assert_eq!(cfg.blocks.len(), 1);
        match &cfg.blocks[0].exit {
            BlockExit::Return(vals) => {
                assert!(matches!(vals.as_slice(), [Expr::Local(4)]));
            }
            _ => panic!("expected return block exit"),
        }
    }

    #[test]
    fn build_cfg_uses_next_pc_for_jumpifnot_targets() {
        let instrs = vec![
            Instr::LoadB {
                reg: 0,
                value: true,
                jump: 0,
            },
            Instr::JumpIfNot { reg: 0, offset: 1 },
            Instr::LoadB {
                reg: 1,
                value: true,
                jump: 0,
            },
            Instr::Return { base: 0, count: 1 },
        ];

        let cfg = build_cfg(&instrs, &[]);
        assert_eq!(cfg.blocks.len(), 3);

        match cfg.blocks[0].exit {
            BlockExit::CondJump {
                then_block,
                else_block,
                ..
            } => {
                assert_eq!(then_block, 1);
                assert_eq!(else_block, 2);
            }
            _ => panic!("expected conditional exit for JUMPIFNOT"),
        }
    }

    #[test]
    fn build_cfg_models_jumpifnoteq_as_eq_condition_with_fallthrough_then() {
        let instrs = vec![
            Instr::LoadN { reg: 0, value: 1 },
            Instr::JumpIfNotEq {
                offset: 1,
                reg: 0,
                aux: 1,
            },
            Instr::LoadN { reg: 2, value: 2 },
            Instr::Return { base: 0, count: 1 },
        ];

        let cfg = build_cfg(&instrs, &[]);
        assert_eq!(cfg.blocks.len(), 3);

        match &cfg.blocks[0].exit {
            BlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } => {
                assert_eq!(*then_block, 1);
                assert_eq!(*else_block, 2);
                assert!(matches!(
                    cond,
                    Expr::Binary(BinOp::Eq, a, b)
                        if matches!(a.as_ref(), Expr::Local(0))
                            && matches!(b.as_ref(), Expr::Local(1))
                ));
            }
            _ => panic!("expected conditional exit for JUMPIFNOTEQ"),
        }
    }

    #[test]
    fn build_cfg_records_generic_for_edges() {
        let instrs = vec![
            Instr::ForgPrep { base: 1, offset: 2 },
            Instr::LoadB {
                reg: 5,
                value: true,
                jump: 0,
            },
            Instr::LoadB {
                reg: 6,
                value: false,
                jump: 0,
            },
            Instr::ForgLoop {
                base: 1,
                offset: -3,
                var_count: 2,
                ipairs: false,
            },
            Instr::Return { base: 0, count: 1 },
        ];

        let cfg = build_cfg(&instrs, &[]);
        assert_eq!(cfg.blocks.len(), 4);

        match cfg.blocks[0].exit {
            BlockExit::ForGPrep { base, loop_block } => {
                assert_eq!(base, 1);
                assert_eq!(loop_block, 2);
            }
            _ => panic!("expected FORGPREP exit"),
        }

        match cfg.blocks[2].exit {
            BlockExit::ForGLoop {
                base,
                body_block,
                exit_block,
                result_count,
            } => {
                assert_eq!(base, 1);
                assert_eq!(body_block, 1);
                assert_eq!(exit_block, 3);
                assert_eq!(result_count, 2);
            }
            _ => panic!("expected FORGLOOP exit"),
        }
    }

    #[test]
    fn lift_settable_and_setlist_emit_index_assignments() {
        let instrs = vec![
            Instr::SetTable {
                src: 7,
                table: 0,
                key: 6,
            },
            Instr::SetList {
                table: 0,
                base: 1,
                count: 4,
                index: 1,
            },
        ];

        let stmts = lift(&instrs, &[]);
        assert_eq!(stmts.len(), 4);

        match &stmts[0] {
            Stmt::Assign { left, value } => {
                assert!(matches!(
                    left,
                    Expr::GetIndex(table, key)
                        if matches!(table.as_ref(), Expr::Local(0))
                            && matches!(key.as_ref(), Expr::Local(6))
                ));
                assert!(matches!(value, Expr::Local(7)));
            }
            _ => panic!("expected SETTABLE assignment"),
        }

        for (idx, stmt) in stmts.iter().enumerate().skip(1) {
            match stmt {
                Stmt::Assign { left, value } => {
                    assert!(matches!(
                        left,
                        Expr::GetIndex(table, key)
                            if matches!(table.as_ref(), Expr::Local(0))
                                && matches!(key.as_ref(), Expr::Number(n) if *n == idx as f64)
                    ));
                    assert!(matches!(value, Expr::Local(reg) if usize::from(*reg) == idx));
                }
                _ => panic!("expected SETLIST assignment"),
            }
        }
    }

    #[test]
    fn lift_setlist_variadic_consumes_pending_multret_call() {
        let consts = vec![Constant::String("newproxy".to_string())];
        let instrs = vec![
            Instr::GetGlobal {
                dest: 12,
                slot: 0,
                key: 0,
            },
            Instr::Call {
                func: 12,
                arg_count: 1,
                ret_count: 0,
            },
            Instr::SetList {
                table: 11,
                base: 12,
                count: 0,
                index: 1,
            },
        ];

        let stmts = lift(&instrs, &consts);
        assert_eq!(stmts.len(), 2);

        match &stmts[1] {
            Stmt::Assign { left, value } => {
                assert!(matches!(
                    left,
                    Expr::GetIndex(table, key)
                        if matches!(table.as_ref(), Expr::Local(11))
                            && matches!(key.as_ref(), Expr::Number(n) if *n == 1.0)
                ));
                match value {
                    Expr::Call(func, args) => {
                        assert!(matches!(func.as_ref(), Expr::Local(12)));
                        assert!(args.is_empty());
                    }
                    _ => panic!("expected variadic CALL expression to feed SETLIST"),
                }
            }
            _ => panic!("expected SETLIST assignment"),
        }
    }

    #[test]
    fn lift_getupval_and_setupval_are_modeled_as_assignments() {
        let instrs = vec![
            Instr::GetUpval { dest: 0, upval: 2 },
            Instr::SetUpval { src: 1, upval: 3 },
        ];
        let stmts = lift(&instrs, &[]);

        assert_eq!(stmts.len(), 2);
        assert!(matches!(
            &stmts[0],
            Stmt::Assign {
                left: Expr::Local(0),
                value: Expr::Upval(2)
            }
        ));
        assert!(matches!(
            &stmts[1],
            Stmt::Assign {
                left: Expr::Upval(3),
                value: Expr::Local(1)
            }
        ));
    }

    #[test]
    fn build_cfg_treats_jumpxeqks_as_block_exit() {
        let consts = vec![Constant::String("string".to_string())];
        let instrs = vec![
            Instr::JumpXEqKS {
                reg: 0,
                k: 0,
                invert: false,
                offset: 1,
            },
            Instr::LoadN { reg: 1, value: 1 },
            Instr::Return { base: 0, count: 1 },
        ];

        let cfg = build_cfg(&instrs, &consts);
        assert_eq!(cfg.blocks.len(), 3);
        assert!(cfg.blocks[0].stmts.is_empty());
        assert!(matches!(cfg.blocks[0].exit, BlockExit::CondJump { .. }));
    }

    #[test]
    fn lift_dupclosure_resolves_proto_index_from_constant_table() {
        let parent = Proto {
            consts: vec![Constant::Closure(7)],
            instrs: vec![Instr::DupClosure { dest: 0, k: 0 }],
            ..Proto::default()
        };
        let mut protos = vec![Proto::default(); 8];
        protos[7].index = 7;

        let cfg = build_cfg_for_proto(&parent, &protos);
        assert_eq!(cfg.blocks.len(), 1);
        assert_eq!(cfg.blocks[0].stmts.len(), 1);
        assert!(matches!(
            &cfg.blocks[0].stmts[0],
            Stmt::Assign {
                left: Expr::Local(0),
                value: Expr::Closure { proto: 7, captures }
            } if captures.is_empty()
        ));
    }

    #[test]
    fn lift_newclosure_resolves_child_proto_and_consumes_captures() {
        let parent = Proto {
            protos: vec![1],
            instrs: vec![
                Instr::NewClosure { dest: 4, proto: 0 },
                Instr::Capture {
                    capture_type: 0,
                    reg: 2,
                },
                Instr::Capture {
                    capture_type: 2,
                    reg: 3,
                },
            ],
            ..Proto::default()
        };
        let mut protos = vec![Proto::default(), Proto::default()];
        protos[1].index = 1;
        protos[1].num_upvals = 2;

        let cfg = build_cfg_for_proto(&parent, &protos);
        assert_eq!(cfg.blocks.len(), 1);
        assert_eq!(cfg.blocks[0].stmts.len(), 1);
        assert!(matches!(
            &cfg.blocks[0].stmts[0],
            Stmt::Assign {
                left: Expr::Local(4),
                value: Expr::Closure { proto: 1, captures }
            } if matches!(
                captures.as_slice(),
                [Expr::Local(2), Expr::Upval(3)]
            )
        ));
    }

    #[test]
    fn build_cfg_uses_word_pc_mapping_for_aux_instruction_jumps() {
        let proto = Proto {
            instrs: vec![
                Instr::Jump { offset: 3 }, // next word pc: 1, target word pc: 4
                Instr::GetImport {
                    dest: 0,
                    index: 0,
                    path: 0,
                }, // 2 words
                Instr::LoadN { reg: 1, value: 10 }, // word pc 3
                Instr::LoadN { reg: 2, value: 20 }, // word pc 4 (jump target)
                Instr::Return { base: 2, count: 2 },
                Instr::Return { base: 1, count: 2 },
            ],
            instr_word_pcs: vec![0, 1, 3, 4, 5, 6],
            ..Proto::default()
        };

        let cfg = build_cfg_for_proto(&proto, std::slice::from_ref(&proto));
        assert!(matches!(cfg.blocks[0].exit, BlockExit::Jump(_)));

        let target = match cfg.blocks[0].exit {
            BlockExit::Jump(target) => target,
            _ => unreachable!(),
        };

        assert!(
            cfg.blocks[target].stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    Stmt::Assign {
                        left: Expr::Local(2),
                        value: Expr::Number(20.0)
                    }
                )
            }),
            "jump target block did not resolve to the expected instruction start"
        );
    }

    #[test]
    fn cfg_populates_successors_predecessors_and_dominators() {
        let instrs = vec![
            Instr::LoadB {
                reg: 0,
                value: true,
                jump: 0,
            },
            Instr::JumpIfNot { reg: 0, offset: 1 },
            Instr::LoadB {
                reg: 1,
                value: true,
                jump: 0,
            },
            Instr::Return { base: 0, count: 1 },
        ];

        let cfg = build_cfg(&instrs, &[]);
        assert_eq!(cfg.successors(0), &[1, 2]);
        assert_eq!(cfg.successors(1), &[2]);
        assert_eq!(cfg.successors(2), &[]);

        assert_eq!(cfg.predecessors(0), &[]);
        assert_eq!(cfg.predecessors(1), &[0]);
        assert_eq!(cfg.predecessors(2), &[0, 1]);

        assert_eq!(cfg.dominators[0], vec![0]);
        assert_eq!(cfg.dominators[1], vec![0, 1]);
        assert_eq!(cfg.dominators[2], vec![0, 2]);
        assert_eq!(cfg.immediate_dominator(0), None);
        assert_eq!(cfg.immediate_dominator(1), Some(0));
        assert_eq!(cfg.immediate_dominator(2), Some(0));
    }

    #[test]
    fn find_if_else_join_detects_diamond_merge() {
        let cfg = ControlFlowGraph::new(
            vec![
                Block {
                    id: 0,
                    stmts: vec![],
                    exit: BlockExit::CondJump {
                        cond: Expr::Local(0),
                        then_block: 1,
                        else_block: 2,
                    },
                },
                Block {
                    id: 1,
                    stmts: vec![],
                    exit: BlockExit::Jump(3),
                },
                Block {
                    id: 2,
                    stmts: vec![],
                    exit: BlockExit::Fallthrough(3),
                },
                Block {
                    id: 3,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![]),
                },
            ],
            0,
        );

        assert_eq!(find_if_else_join(1, 2, &cfg), Some(3));
    }

    #[test]
    fn resolve_numeric_for_tail_uses_predecessor_metadata() {
        let cfg = ControlFlowGraph::new(
            vec![
                Block {
                    id: 0,
                    stmts: vec![],
                    exit: BlockExit::ForNPrep {
                        base: 0,
                        loop_block: 3,
                    },
                },
                Block {
                    id: 1,
                    stmts: vec![],
                    exit: BlockExit::Fallthrough(2),
                },
                Block {
                    id: 2,
                    stmts: vec![],
                    exit: BlockExit::ForNLoop {
                        base: 0,
                        body_block: 1,
                        exit_block: 3,
                    },
                },
                Block {
                    id: 3,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![]),
                },
            ],
            0,
        );

        assert_eq!(resolve_numeric_for_tail(0, 0, 3, &cfg), Some((2, 1, 3)));
    }

    #[test]
    fn resolve_generic_for_tail_uses_predecessor_metadata() {
        let cfg = ControlFlowGraph::new(
            vec![
                Block {
                    id: 0,
                    stmts: vec![],
                    exit: BlockExit::ForGPrep {
                        base: 1,
                        loop_block: 3,
                    },
                },
                Block {
                    id: 1,
                    stmts: vec![],
                    exit: BlockExit::Fallthrough(2),
                },
                Block {
                    id: 2,
                    stmts: vec![],
                    exit: BlockExit::ForGLoop {
                        base: 1,
                        body_block: 1,
                        exit_block: 3,
                        result_count: 2,
                    },
                },
                Block {
                    id: 3,
                    stmts: vec![],
                    exit: BlockExit::Return(vec![]),
                },
            ],
            0,
        );

        assert_eq!(resolve_generic_for_tail(0, 1, 3, &cfg), Some((2, 1, 3, 2)));
    }
}
