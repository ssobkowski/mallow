use std::collections::HashSet;

use crate::{
    disasm::Proto,
    hil::{BinOp, BlockExit, ControlFlowGraph, Expr, Stmt, UnaryOp, build_cfg_for_proto},
};

pub struct Emitter {
    indent: usize,
    buf: String,
    loop_exit_stack: Vec<usize>,
}

impl Emitter {
    pub fn new() -> Self {
        Emitter {
            indent: 0,
            buf: String::new(),
            loop_exit_stack: Vec::new(),
        }
    }

    pub fn take(self) -> String {
        self.buf
    }

    pub fn emit_cfg(&mut self, cfg: &ControlFlowGraph) {
        // For now we recursively emit from entry.
        let mut emitted = HashSet::new();
        self.emit_block(cfg.entry_block, None, cfg, &mut emitted);
    }

    pub fn emit_proto(&mut self, proto: &Proto, all_protos: &[Proto]) {
        self.buf
            .push_str(&format!("local function _proto_{}(", proto.index));

        let mut params: Vec<String> = (0..proto.num_upvals).map(|i| format!("_u{}", i)).collect();
        params.extend((0..proto.num_params).map(|i| format!("_r{}", i)));
        self.buf.push_str(&params.join(", "));
        self.buf.push_str(")\n");

        let cfg = build_cfg_for_proto(proto, all_protos);
        self.indent += 1;
        self.emit_cfg(&cfg);
        self.indent -= 1;

        self.buf.push_str("end\n");
    }

    pub fn emit_entry_proto(&mut self, proto: &Proto, all_protos: &[Proto]) {
        let cfg = build_cfg_for_proto(proto, all_protos);
        self.emit_cfg(&cfg);
    }

    fn emit_block(
        &mut self,
        block_id: usize,
        stop_at: Option<usize>,
        cfg: &ControlFlowGraph,
        emitted: &mut HashSet<usize>,
    ) {
        if Some(block_id) == stop_at {
            return;
        }
        if !emitted.insert(block_id) {
            return;
        }
        let Some(block) = cfg.blocks.get(block_id) else {
            return;
        };

        let resolved_generic_for = match &block.exit {
            BlockExit::ForGPrep { base, loop_block } => {
                resolve_generic_for_tail(block_id, *base, *loop_block, cfg)
            }
            _ => None,
        };

        let for_in_iter_call = match &block.exit {
            BlockExit::ForGPrep { base, .. } => {
                let base = reg_from_index(*base);
                match block.stmts.last() {
                    Some(Stmt::AssignMany { left, value })
                        if is_generic_for_iter_assign(left, base)
                            && matches!(value, Expr::Call(_, _) | Expr::MethodCall(_, _, _)) =>
                    {
                        Some(value)
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        for (idx, stmt) in block.stmts.iter().enumerate() {
            if for_in_iter_call.is_some()
                && resolved_generic_for.is_some()
                && idx + 1 == block.stmts.len()
            {
                // Render this as `for ... in <call>` instead of a standalone multi-assignment.
                continue;
            }
            self.emit_stmt(stmt);
        }
        match &block.exit {
            BlockExit::CondJump {
                cond,
                then_block,
                else_block,
            } => {
                if self.is_simple_while(block_id, *then_block, cfg) {
                    self.push_indent();
                    self.buf
                        .push_str(&format!("while {} do\n", self.emit_expr(cond)));

                    self.indent += 1;
                    self.emit_block(*then_block, Some(block_id), cfg, emitted);
                    self.indent -= 1;

                    self.push_indent();
                    self.buf.push_str("end\n");

                    self.emit_block(*else_block, stop_at, cfg, emitted);
                    return;
                }

                let pred_counts = predecessor_counts(cfg);
                if let Some(join_block) =
                    find_if_else_join(*then_block, *else_block, cfg, &pred_counts)
                {
                    self.push_indent();
                    self.buf
                        .push_str(&format!("if {} then\n", self.emit_expr(cond)));

                    self.indent += 1;
                    self.emit_block(*then_block, Some(join_block), cfg, emitted);
                    self.indent -= 1;

                    self.push_indent();
                    self.buf.push_str("else\n");

                    self.indent += 1;
                    self.emit_block(*else_block, Some(join_block), cfg, emitted);
                    self.indent -= 1;

                    self.push_indent();
                    self.buf.push_str("end\n");

                    if Some(join_block) != stop_at {
                        self.emit_block(join_block, stop_at, cfg, emitted);
                    }
                    return;
                }

                // Prefer source-like `if cond then body end` when the body is fallthrough.
                if *else_block == block_id + 1 && *then_block > *else_block {
                    let inverted = negate_expr(cond);

                    self.push_indent();
                    self.buf
                        .push_str(&format!("if {} then\n", self.emit_expr(&inverted)));

                    self.indent += 1;
                    self.emit_block(*else_block, Some(*then_block), cfg, emitted);
                    self.indent -= 1;

                    self.push_indent();
                    self.buf.push_str("end\n");

                    if Some(*then_block) != stop_at {
                        self.emit_block(*then_block, stop_at, cfg, emitted);
                    }
                    return;
                }

                self.push_indent();

                self.buf
                    .push_str(&format!("if {} then\n", self.emit_expr(cond)));

                self.indent += 1;
                self.emit_block(*then_block, Some(*else_block), cfg, emitted);
                self.indent -= 1;

                self.push_indent();
                self.buf.push_str("end\n");

                if Some(*else_block) == stop_at {
                    if let Some(else_branch) = cfg.blocks.get(*else_block) {
                        for stmt in &else_branch.stmts {
                            self.emit_stmt(stmt);
                        }
                    }
                } else {
                    self.emit_block(*else_block, stop_at, cfg, emitted);
                }
            }
            BlockExit::ForGPrep { base, loop_block } => {
                let mut emitted_as_loop = false;
                if let Some((loop_tail_block, body_block, exit_block, result_count)) =
                    resolved_generic_for
                {
                    emitted.insert(loop_tail_block);
                    emitted_as_loop = true;
                    let base = reg_from_index(*base);

                    let vars: Vec<String> = (0..result_count)
                        .map(|i| self.local_name(reg_with_offset(base, 3 + i)))
                        .collect();
                    let iter = if let Some(iter_call) = for_in_iter_call {
                        self.emit_expr(iter_call)
                    } else {
                        [
                            self.local_name(base),
                            self.local_name(reg_with_offset(base, 1)),
                            self.local_name(reg_with_offset(base, 2)),
                        ]
                        .join(", ")
                    };

                    let loop_vars = if vars.is_empty() {
                        "_".to_string()
                    } else {
                        vars.join(", ")
                    };

                    self.push_indent();
                    self.buf
                        .push_str(&format!("for {} in {} do\n", loop_vars, iter));

                    self.indent += 1;
                    self.loop_exit_stack.push(exit_block);
                    self.emit_block(body_block, Some(loop_tail_block), cfg, emitted);
                    self.loop_exit_stack.pop();
                    self.indent -= 1;

                    self.push_indent();
                    self.buf.push_str("end\n");

                    self.emit_block(exit_block, stop_at, cfg, emitted);
                }

                if !emitted_as_loop {
                    self.emit_block(*loop_block, stop_at, cfg, emitted);
                }
            }
            BlockExit::ForNPrep { base, loop_block } => {
                let mut emitted_as_loop = false;
                if let Some((loop_tail_block, body_block, exit_block)) =
                    resolve_numeric_for_tail(block_id, *base, *loop_block, cfg)
                {
                    emitted.insert(loop_tail_block);
                    emitted_as_loop = true;
                    let base = reg_from_index(*base);

                    let var_reg = detect_numeric_for_var(base, body_block, cfg);
                    let init = self.local_name(reg_with_offset(base, 2));
                    let limit = self.local_name(base);
                    let step = self.local_name(reg_with_offset(base, 1));

                    self.push_indent();
                    self.buf.push_str(&format!(
                        "for {} = {}, {}, {} do\n",
                        self.local_name(var_reg),
                        init,
                        limit,
                        step
                    ));

                    self.indent += 1;
                    self.loop_exit_stack.push(exit_block);
                    self.emit_block(body_block, Some(loop_tail_block), cfg, emitted);
                    self.loop_exit_stack.pop();
                    self.indent -= 1;

                    self.push_indent();
                    self.buf.push_str("end\n");

                    self.emit_block(exit_block, stop_at, cfg, emitted);
                }

                if !emitted_as_loop {
                    self.emit_block(*loop_block, stop_at, cfg, emitted);
                }
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
            } => {
                // Fallback when a prep block wasn't recognized.
                self.emit_block(*body_block, Some(block_id), cfg, emitted);
                self.emit_block(*exit_block, stop_at, cfg, emitted);
            }
            BlockExit::Fallthrough(next) => {
                if Some(*next) != stop_at {
                    self.emit_block(*next, stop_at, cfg, emitted);
                }
            }
            BlockExit::Return(vals) => {
                if !vals.is_empty() {
                    let vals_str: Vec<_> = vals.iter().map(|e| self.emit_expr(e)).collect();
                    self.push_indent();
                    self.buf
                        .push_str(&format!("return {}\n", vals_str.join(", ")));
                }
            }
            BlockExit::Jump(target) => {
                if self.loop_exit_stack.last().copied() == Some(*target) {
                    self.push_indent();
                    self.buf.push_str("break\n");
                    return;
                }
                if Some(*target) != stop_at {
                    self.emit_block(*target, stop_at, cfg, emitted);
                }
            }
        }
    }

    fn emit_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assign { left, value } => {
                self.emit_assignment(left, value);
            }
            Stmt::AssignMany { left, value } => {
                self.push_indent();
                let left_exprs: Vec<_> = left.iter().map(|e| self.emit_expr(e)).collect();
                self.buf.push_str(&format!(
                    "{} = {}\n",
                    left_exprs.join(", "),
                    self.emit_expr(value)
                ));
            }
            Stmt::Call(expr) => {
                if matches!(expr, Expr::Call(_, _) | Expr::MethodCall(_, _, _)) {
                    self.push_indent();
                    self.buf.push_str(&format!("{}\n", self.emit_expr(expr)));
                }
            }
            Stmt::SetField { table, key, value } => {
                self.push_indent();
                self.buf.push_str(&format!(
                    "{} = {}\n",
                    emit_field_access(&format!("_r{}", table), key),
                    self.emit_expr(value)
                ));
            }
            Stmt::Return(vals) => {
                if !vals.is_empty() {
                    let vals_str: Vec<_> = vals.iter().map(|e| self.emit_expr(e)).collect();
                    self.push_indent();
                    self.buf
                        .push_str(&format!("return {}\n", vals_str.join(", ")));
                } else {
                    self.push_indent();
                    self.buf.push_str("return\n");
                }
            }
        }
    }

    fn emit_assignment(&mut self, left: &Expr, value: &Expr) {
        self.push_indent();
        self.buf.push_str(&format!(
            "{} = {}\n",
            self.emit_expr(left),
            self.emit_expr(value)
        ));
    }

    fn emit_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Nil => "nil".into(),
            Expr::Bool(b) => b.to_string(),
            Expr::Number(n) => n.to_string(),
            Expr::String(s) => format!("\"{}\"", s),
            Expr::Local(r) => format!("_r{}", r),
            Expr::Upval(u) => format!("_u{}", u),
            Expr::Closure { proto, captures } => {
                if captures.is_empty() {
                    format!("_proto_{}", proto)
                } else {
                    let captures = captures
                        .iter()
                        .map(|capture| self.emit_expr(capture))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!(
                        "(function(...) return _proto_{}({}, ...) end)",
                        proto, captures
                    )
                }
            }
            Expr::Global(n) | Expr::Import(n) => n.clone(),
            Expr::Binary(op, a, b) => format!(
                "{} {} {}",
                self.emit_expr(a),
                emit_binop(op),
                self.emit_expr(b)
            ),
            Expr::Unary(op, e) => format!("{}{}", emit_unop(op), self.emit_expr(e)),
            Expr::Call(func, args) => {
                let args_str: Vec<_> = args.iter().map(|e| self.emit_expr(e)).collect();
                format!("{}({})", self.emit_expr(func), args_str.join(", "))
            }
            Expr::MethodCall(expr, key, args) => {
                let base = self.emit_expr(expr);
                let args_str: Vec<_> = args.iter().map(|e| self.emit_expr(e)).collect();
                if is_ident(key) {
                    format!("{}:{}({})", base, key, args_str.join(", "))
                } else {
                    let mut all_args = Vec::with_capacity(args_str.len() + 1);
                    all_args.push(base.clone());
                    all_args.extend(args_str);
                    format!("{}[\"{}\"]({})", base, key, all_args.join(", "))
                }
            }
            Expr::GetField(expr, key) => {
                if is_ident(key) {
                    format!("{}.{}", self.emit_expr(expr), key)
                } else {
                    format!("{}[\"{}\"]", self.emit_expr(expr), key)
                }
            }
            Expr::GetIndex(expr, key) => {
                format!("{}[{}]", self.emit_expr(expr), self.emit_expr(key))
            }
            Expr::Table(exprs) => {
                let values = exprs
                    .iter()
                    .map(|e| self.emit_expr(e))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{}}}", values)
            }
        }
    }

    fn push_indent(&mut self) {
        let indent = "  ".repeat(self.indent);
        self.buf.push_str(&indent);
    }

    fn local_name(&self, reg: u8) -> String {
        format!("_r{}", reg)
    }

    fn is_simple_while(&self, header: usize, body_start: usize, cfg: &ControlFlowGraph) -> bool {
        let mut seen = HashSet::new();
        let mut current = body_start;

        while seen.insert(current) {
            let Some(block) = cfg.blocks.get(current) else {
                return false;
            };
            match block.exit {
                BlockExit::Fallthrough(next) => {
                    current = next;
                }
                BlockExit::Jump(target) => {
                    return target == header;
                }
                _ => return false,
            }
        }

        false
    }
}

#[derive(Debug, Clone, Copy)]
enum LinearExit {
    Jump(usize),
    Fallthrough(usize),
    Other,
}

fn linear_exit_from(start: usize, cfg: &ControlFlowGraph, pred_counts: &[usize]) -> LinearExit {
    let mut seen = HashSet::new();
    let mut current = start;

    while seen.insert(current) {
        let Some(block) = cfg.blocks.get(current) else {
            return LinearExit::Other;
        };

        match block.exit {
            BlockExit::Fallthrough(next)
                if next == current + 1
                    && pred_counts.get(next).copied().unwrap_or(0) <= 1 =>
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

fn predecessor_counts(cfg: &ControlFlowGraph) -> Vec<usize> {
    let mut preds = vec![0usize; cfg.blocks.len()];

    for block in &cfg.blocks {
        match block.exit {
            BlockExit::Jump(target) | BlockExit::Fallthrough(target) => {
                if let Some(slot) = preds.get_mut(target) {
                    *slot += 1;
                }
            }
            BlockExit::CondJump {
                then_block,
                else_block,
                ..
            } => {
                if let Some(slot) = preds.get_mut(then_block) {
                    *slot += 1;
                }
                if let Some(slot) = preds.get_mut(else_block) {
                    *slot += 1;
                }
            }
            BlockExit::ForNPrep { loop_block, .. } | BlockExit::ForGPrep { loop_block, .. } => {
                if let Some(slot) = preds.get_mut(loop_block) {
                    *slot += 1;
                }
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
            } => {
                if let Some(slot) = preds.get_mut(body_block) {
                    *slot += 1;
                }
                if let Some(slot) = preds.get_mut(exit_block) {
                    *slot += 1;
                }
            }
            BlockExit::Return(_) => {}
        }
    }

    preds
}

fn find_if_else_join(
    then_block: usize,
    else_block: usize,
    cfg: &ControlFlowGraph,
    pred_counts: &[usize],
) -> Option<usize> {
    let then_exit = linear_exit_from(then_block, cfg, pred_counts);
    let else_exit = linear_exit_from(else_block, cfg, pred_counts);

    match (then_exit, else_exit) {
        (LinearExit::Jump(a), LinearExit::Fallthrough(b))
        | (LinearExit::Fallthrough(a), LinearExit::Jump(b))
            if a == b && a != then_block && a != else_block =>
        {
            Some(a)
        }
        _ => None,
    }
}

fn negate_expr(expr: &Expr) -> Expr {
    match expr {
        Expr::Unary(UnaryOp::Not, inner) => inner.as_ref().clone(),
        Expr::Binary(op, a, b) => {
            let inverted = match op {
                BinOp::Eq => Some(BinOp::Ne),
                BinOp::Ne => Some(BinOp::Eq),
                BinOp::Lt => Some(BinOp::Gte),
                BinOp::Lte => Some(BinOp::Gt),
                BinOp::Gt => Some(BinOp::Lte),
                BinOp::Gte => Some(BinOp::Lt),
                _ => None,
            };

            if let Some(op) = inverted {
                Expr::Binary(op, a.clone(), b.clone())
            } else {
                Expr::Unary(UnaryOp::Not, Box::new(expr.clone()))
            }
        }
        _ => Expr::Unary(UnaryOp::Not, Box::new(expr.clone())),
    }
}

fn detect_numeric_for_var(base: u8, body_block: usize, cfg: &ControlFlowGraph) -> u8 {
    let Some(block) = cfg.blocks.get(body_block) else {
        return reg_with_offset(base, 2);
    };

    for stmt in &block.stmts {
        if let Stmt::Assign {
            left: Expr::Local(dst),
            value: Expr::Local(src),
        } = stmt
            && *src == reg_with_offset(base, 2)
        {
            return *dst;
        }
    }

    reg_with_offset(base, 2)
}

fn is_generic_for_iter_assign(left: &[Expr], base: u8) -> bool {
    matches!(
        left,
        [Expr::Local(a), Expr::Local(b), Expr::Local(c)]
            if *a == base
                && *b == reg_with_offset(base, 1)
                && *c == reg_with_offset(base, 2)
    )
}

fn reg_from_index(index: usize) -> u8 {
    u8::try_from(index).expect("CFG register index must fit in u8")
}

fn reg_with_offset(base: u8, offset: usize) -> u8 {
    base.checked_add(u8::try_from(offset).expect("register offset must fit in u8"))
        .expect("register arithmetic overflowed u8")
}

fn resolve_numeric_for_tail(
    prep_block: usize,
    base: usize,
    prep_target_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<(usize, usize, usize)> {
    if let Some(block) = cfg.blocks.get(prep_target_block)
        && let BlockExit::ForNLoop {
            base: loop_base,
            body_block,
            exit_block,
        } = block.exit
        && loop_base == base
    {
        return Some((prep_target_block, body_block, exit_block));
    }

    for (idx, block) in cfg.blocks.iter().enumerate() {
        if let BlockExit::ForNLoop {
            base: loop_base,
            body_block,
            exit_block,
        } = block.exit
            && loop_base == base
            && exit_block == prep_target_block
            && body_block == prep_block + 1
        {
            return Some((idx, body_block, exit_block));
        }
    }

    for (idx, block) in cfg.blocks.iter().enumerate() {
        if let BlockExit::ForNLoop {
            base: loop_base,
            body_block,
            exit_block,
        } = block.exit
            && loop_base == base
            && exit_block == prep_target_block
        {
            return Some((idx, body_block, exit_block));
        }
    }

    None
}

fn resolve_generic_for_tail(
    prep_block: usize,
    base: usize,
    prep_target_block: usize,
    cfg: &ControlFlowGraph,
) -> Option<(usize, usize, usize, usize)> {
    let preferred_body = prep_block + 1;

    if let Some(block) = cfg.blocks.get(prep_target_block)
        && let BlockExit::ForGLoop {
            base: loop_base,
            body_block,
            exit_block,
            result_count,
        } = block.exit
        && loop_base == base
    {
        let chosen_body = prefer_sequential_loop_body(preferred_body, body_block, cfg);
        return Some((prep_target_block, chosen_body, exit_block, result_count));
    }

    for (idx, block) in cfg.blocks.iter().enumerate() {
        if let BlockExit::ForGLoop {
            base: loop_base,
            body_block,
            exit_block,
            result_count,
        } = block.exit
            && loop_base == base
            && exit_block == prep_target_block
            && body_block == preferred_body
        {
            return Some((idx, body_block, exit_block, result_count));
        }
    }

    for (idx, block) in cfg.blocks.iter().enumerate() {
        if let BlockExit::ForGLoop {
            base: loop_base,
            body_block,
            exit_block,
            result_count,
        } = block.exit
            && loop_base == base
            && exit_block == prep_target_block
        {
            let chosen_body = prefer_sequential_loop_body(preferred_body, body_block, cfg);
            return Some((idx, chosen_body, exit_block, result_count));
        }
    }

    for (idx, block) in cfg.blocks.iter().enumerate() {
        if let BlockExit::ForGLoop {
            base: loop_base,
            body_block,
            exit_block,
            result_count,
        } = block.exit
            && loop_base == base
            && body_block == preferred_body
        {
            return Some((idx, body_block, exit_block, result_count));
        }
    }

    for (idx, block) in cfg.blocks.iter().enumerate() {
        if let BlockExit::ForGLoop {
            base: loop_base,
            body_block,
            exit_block,
            result_count,
        } = block.exit
            && loop_base == base
        {
            let chosen_body = prefer_sequential_loop_body(preferred_body, body_block, cfg);
            return Some((idx, chosen_body, exit_block, result_count));
        }
    }

    None
}

fn prefer_sequential_loop_body(
    preferred_body: usize,
    detected_body: usize,
    cfg: &ControlFlowGraph,
) -> usize {
    if preferred_body == detected_body {
        return detected_body;
    }
    if preferred_body < cfg.blocks.len() {
        return preferred_body;
    }
    detected_body
}

fn emit_field_access(base: &str, key: &str) -> String {
    if is_ident(key) {
        format!("{}.{}", base, key)
    } else {
        format!("{}[\"{}\"]", base, key)
    }
}

fn emit_binop(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Pow => "^",
        BinOp::Eq => "==",
        BinOp::Ne => "~=",
        BinOp::Lt => "<",
        BinOp::Lte => "<=",
        BinOp::Gt => ">",
        BinOp::Gte => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Concat => "..",
    }
}

fn emit_unop(op: &UnaryOp) -> &'static str {
    match op {
        UnaryOp::Not => "not ",
        UnaryOp::Minus => "-",
        UnaryOp::Length => "#",
    }
}

fn is_ident(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) if c == '_' || c.is_ascii_alphabetic() => {}
        _ => return false,
    }
    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

#[cfg(test)]
mod tests {
    use crate::{
        codegen::Emitter,
        disasm::Proto,
        hil::{BinOp, Block, BlockExit, ControlFlowGraph, Expr, Stmt},
    };
    use indoc::indoc;

    fn emit_blocks(blocks: Vec<Block>) -> String {
        let cfg = ControlFlowGraph {
            blocks,
            entry_block: 0,
        };
        let mut emitter = Emitter::new();
        emitter.emit_cfg(&cfg);
        emitter.take()
    }

    #[test]
    fn keeps_call_argument_register_assignments() {
        let out = emit_blocks(vec![Block {
            id: 0,
            stmts: vec![
                Stmt::Assign {
                    left: Expr::Local(2),
                    value: Expr::Global("f".to_string()),
                },
                Stmt::Assign {
                    left: Expr::Local(1),
                    value: Expr::Local(0),
                },
                Stmt::Call(Expr::Call(Box::new(Expr::Local(2)), vec![Expr::Local(1)])),
            ],
            exit: BlockExit::Return(vec![]),
        }]);

        assert_eq!(
            out,
            indoc! {"
                _r2 = f
                _r1 = _r0
                _r2(_r1)
            "}
        );
    }

    #[test]
    fn keeps_transitive_register_assignments() {
        let out = emit_blocks(vec![Block {
            id: 0,
            stmts: vec![
                Stmt::Assign {
                    left: Expr::Local(1),
                    value: Expr::Local(0),
                },
                Stmt::Assign {
                    left: Expr::Local(2),
                    value: Expr::Local(1),
                },
                Stmt::Assign {
                    left: Expr::Local(3),
                    value: Expr::Binary(
                        BinOp::Add,
                        Box::new(Expr::Local(2)),
                        Box::new(Expr::Number(1.0)),
                    ),
                },
            ],
            exit: BlockExit::Return(vec![]),
        }]);

        assert_eq!(
            out,
            indoc! {"
                _r1 = _r0
                _r2 = _r1
                _r3 = _r2 + 1
            "}
        );
    }

    #[test]
    fn keeps_register_value_after_source_clobber() {
        let out = emit_blocks(vec![Block {
            id: 0,
            stmts: vec![
                Stmt::Assign {
                    left: Expr::Local(1),
                    value: Expr::Local(0),
                },
                Stmt::Assign {
                    left: Expr::Local(0),
                    value: Expr::Number(5.0),
                },
                Stmt::Call(Expr::Call(
                    Box::new(Expr::Global("use".to_string())),
                    vec![Expr::Local(1)],
                )),
            ],
            exit: BlockExit::Return(vec![]),
        }]);

        assert_eq!(
            out,
            indoc! {"
                _r1 = _r0
                _r0 = 5
                use(_r1)
            "}
        );
    }

    #[test]
    fn emits_local_once_then_reassigns() {
        let out = emit_blocks(vec![Block {
            id: 0,
            stmts: vec![
                Stmt::Assign {
                    left: Expr::Local(1),
                    value: Expr::Number(1.0),
                },
                Stmt::Assign {
                    left: Expr::Local(1),
                    value: Expr::Number(2.0),
                },
            ],
            exit: BlockExit::Return(vec![]),
        }]);

        assert_eq!(
            out,
            indoc! {"
                _r1 = 1
                _r1 = 2
            "}
        );
    }

    #[test]
    fn keeps_assignments_across_blocks() {
        let out = emit_blocks(vec![
            Block {
                id: 0,
                stmts: vec![Stmt::Assign {
                    left: Expr::Local(1),
                    value: Expr::Local(0),
                }],
                exit: BlockExit::Fallthrough(1),
            },
            Block {
                id: 1,
                stmts: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Global("use".to_string())),
                    vec![Expr::Local(1)],
                ))],
                exit: BlockExit::Return(vec![]),
            },
        ]);

        assert_eq!(
            out,
            indoc! {"
                _r1 = _r0
                use(_r1)
            "}
        );
    }

    #[test]
    fn keeps_conditional_and_return_registers() {
        let out = emit_blocks(vec![
            Block {
                id: 0,
                stmts: vec![Stmt::Assign {
                    left: Expr::Local(1),
                    value: Expr::Local(0),
                }],
                exit: BlockExit::CondJump {
                    cond: Expr::Binary(
                        BinOp::Eq,
                        Box::new(Expr::Local(1)),
                        Box::new(Expr::Number(0.0)),
                    ),
                    then_block: 1,
                    else_block: 2,
                },
            },
            Block {
                id: 1,
                stmts: vec![],
                exit: BlockExit::Return(vec![Expr::Local(1)]),
            },
            Block {
                id: 2,
                stmts: vec![],
                exit: BlockExit::Return(vec![Expr::Local(0)]),
            },
        ]);

        assert_eq!(
            out,
            indoc! {"
                _r1 = _r0
                if _r1 == 0 then
                  return _r1
                end
                return _r0
            "}
        );
    }

    #[test]
    fn keeps_method_call_receiver_assignment() {
        let out = emit_blocks(vec![Block {
            id: 0,
            stmts: vec![
                Stmt::Assign {
                    left: Expr::Local(3),
                    value: Expr::Local(2),
                },
                Stmt::Call(Expr::MethodCall(
                    Box::new(Expr::Local(3)),
                    "Disable".to_string(),
                    vec![],
                )),
            ],
            exit: BlockExit::Return(vec![]),
        }]);

        assert_eq!(
            out,
            indoc! {"
                _r3 = _r2
                _r3:Disable()
            "}
        );
    }

    #[test]
    fn emits_method_call_with_explicit_self_for_non_identifier_keys() {
        let out = emit_blocks(vec![Block {
            id: 0,
            stmts: vec![Stmt::Call(Expr::MethodCall(
                Box::new(Expr::Local(1)),
                "bad-key".to_string(),
                vec![Expr::Local(2)],
            ))],
            exit: BlockExit::Return(vec![]),
        }]);

        assert_eq!(
            out,
            indoc! {r#"
                _r1["bad-key"](_r1, _r2)
            "#}
        );
    }

    #[test]
    fn emits_generic_for_loop_from_cfg_loop_edges() {
        let out = emit_blocks(vec![
            Block {
                id: 0,
                stmts: vec![],
                exit: BlockExit::ForGPrep {
                    base: 1,
                    loop_block: 2,
                },
            },
            Block {
                id: 1,
                stmts: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Global("use".to_string())),
                    vec![Expr::Local(5)],
                ))],
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
        ]);

        assert_eq!(
            out,
            indoc! {"
                for _r4, _r5 in _r1, _r2, _r3 do
                  use(_r5)
                end
            "}
        );
    }

    #[test]
    fn emits_for_in_from_iter_triple_assignment_call() {
        let out = emit_blocks(vec![
            Block {
                id: 0,
                stmts: vec![Stmt::AssignMany {
                    left: vec![Expr::Local(1), Expr::Local(2), Expr::Local(3)],
                    value: Expr::Call(
                        Box::new(Expr::Local(1)),
                        vec![Expr::Call(Box::new(Expr::Local(2)), vec![Expr::Local(3)])],
                    ),
                }],
                exit: BlockExit::ForGPrep {
                    base: 1,
                    loop_block: 2,
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
        ]);

        assert_eq!(
            out,
            indoc! {"
                for _r4, _r5 in _r1(_r2(_r3)) do
                end
            "}
        );
    }

    #[test]
    fn emits_generic_for_when_prep_points_to_exit_block() {
        let out = emit_blocks(vec![
            Block {
                id: 0,
                stmts: vec![Stmt::AssignMany {
                    left: vec![Expr::Local(1), Expr::Local(2), Expr::Local(3)],
                    value: Expr::Call(
                        Box::new(Expr::Local(1)),
                        vec![Expr::Call(Box::new(Expr::Local(2)), vec![Expr::Local(3)])],
                    ),
                }],
                exit: BlockExit::ForGPrep {
                    base: 1,
                    loop_block: 3,
                },
            },
            Block {
                id: 1,
                stmts: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Global("use".to_string())),
                    vec![Expr::Local(5)],
                ))],
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
        ]);

        assert_eq!(
            out,
            indoc! {"
                for _r4, _r5 in _r1(_r2(_r3)) do
                  use(_r5)
                end
            "}
        );
    }

    #[test]
    fn emits_simple_while_from_cond_jump_and_backedge() {
        let out = emit_blocks(vec![
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
                stmts: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Global("tick".to_string())),
                    vec![],
                ))],
                exit: BlockExit::Jump(0),
            },
            Block {
                id: 2,
                stmts: vec![],
                exit: BlockExit::Return(vec![]),
            },
        ]);

        assert_eq!(
            out,
            indoc! {"
                while _r0 do
                  tick()
                end
            "}
        );
    }

    #[test]
    fn emits_numeric_for_loop_from_cfg_loop_edges() {
        let out = emit_blocks(vec![
            Block {
                id: 0,
                stmts: vec![],
                exit: BlockExit::ForNPrep {
                    base: 0,
                    loop_block: 2,
                },
            },
            Block {
                id: 1,
                stmts: vec![
                    Stmt::Assign {
                        left: Expr::Local(8),
                        value: Expr::Local(2),
                    },
                    Stmt::Call(Expr::Call(
                        Box::new(Expr::Global("use".to_string())),
                        vec![Expr::Local(8)],
                    )),
                ],
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
        ]);

        assert_eq!(
            out,
            indoc! {"
                for _r8 = _r2, _r0, _r1 do
                  _r8 = _r2
                  use(_r8)
                end
            "}
        );
    }

    #[test]
    fn emits_numeric_for_when_prep_points_to_exit_block() {
        let out = emit_blocks(vec![
            Block {
                id: 0,
                stmts: vec![],
                exit: BlockExit::ForNPrep {
                    base: 1,
                    loop_block: 3,
                },
            },
            Block {
                id: 1,
                stmts: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Global("use".to_string())),
                    vec![Expr::Local(3)],
                ))],
                exit: BlockExit::Fallthrough(2),
            },
            Block {
                id: 2,
                stmts: vec![],
                exit: BlockExit::ForNLoop {
                    base: 1,
                    body_block: 1,
                    exit_block: 3,
                },
            },
            Block {
                id: 3,
                stmts: vec![],
                exit: BlockExit::Return(vec![]),
            },
        ]);

        assert_eq!(
            out,
            indoc! {"
                for _r3 = _r3, _r1, _r2 do
                  use(_r3)
                end
            "}
        );
    }

    #[test]
    fn emits_break_for_jump_to_active_loop_exit() {
        let out = emit_blocks(vec![
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
                stmts: vec![Stmt::Assign {
                    left: Expr::Local(3),
                    value: Expr::Number(12.0),
                }],
                exit: BlockExit::CondJump {
                    cond: Expr::Binary(
                        BinOp::Eq,
                        Box::new(Expr::Local(2)),
                        Box::new(Expr::Local(3)),
                    ),
                    then_block: 2,
                    else_block: 4,
                },
            },
            Block {
                id: 2,
                stmts: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Global("print".to_string())),
                    vec![Expr::String("YES".to_string())],
                ))],
                exit: BlockExit::Jump(5),
            },
            Block {
                id: 3,
                stmts: vec![],
                exit: BlockExit::ForNLoop {
                    base: 0,
                    body_block: 1,
                    exit_block: 5,
                },
            },
            Block {
                id: 4,
                stmts: vec![Stmt::Call(Expr::Call(
                    Box::new(Expr::Global("print".to_string())),
                    vec![Expr::Local(2), Expr::String("NO".to_string())],
                ))],
                exit: BlockExit::Fallthrough(3),
            },
            Block {
                id: 5,
                stmts: vec![],
                exit: BlockExit::Return(vec![]),
            },
        ]);

        assert_eq!(
            out,
            indoc! {r#"
                for _r2 = _r2, _r0, _r1 do
                  _r3 = 12
                  if _r2 == _r3 then
                    print("YES")
                    break
                  end
                  print(_r2, "NO")
                end
            "#}
        );
    }

    #[test]
    fn emits_upvalue_expression_with_synthetic_name() {
        let out = emit_blocks(vec![Block {
            id: 0,
            stmts: vec![Stmt::Assign {
                left: Expr::Local(0),
                value: Expr::Upval(2),
            }],
            exit: BlockExit::Return(vec![]),
        }]);

        assert_eq!(
            out,
            indoc! {"
                _r0 = _u2
            "}
        );
    }

    #[test]
    fn emits_captured_closure_wrapper() {
        let out = emit_blocks(vec![Block {
            id: 0,
            stmts: vec![Stmt::Assign {
                left: Expr::Local(0),
                value: Expr::Closure {
                    proto: 3,
                    captures: vec![Expr::Upval(0), Expr::Local(1)],
                },
            }],
            exit: BlockExit::Return(vec![]),
        }]);

        assert_eq!(
            out,
            indoc! {"
                _r0 = (function(...) return _proto_3(_u0, _r1, ...) end)
            "}
        );
    }

    #[test]
    fn emit_proto_includes_upvalue_parameters_before_regular_params() {
        let proto = Proto {
            index: 8,
            num_params: 1,
            num_upvals: 2,
            instrs: vec![crate::il::Instr::Return { base: 0, count: 1 }],
            ..Proto::default()
        };
        let mut emitter = Emitter::new();
        emitter.emit_proto(&proto, std::slice::from_ref(&proto));
        let out = emitter.take();

        assert!(out.starts_with("local function _proto_8(_u0, _u1, _r0)\n"));
    }
}
