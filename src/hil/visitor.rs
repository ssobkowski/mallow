use smol_str::SmolStr;

use crate::hil::{
    StructuredFunction,
    cflow::{
        cfg::{Block, BlockExit},
        graph::GraphView,
        region::RegionNode,
    },
    ir::{Expr, Number, PhiNode, Stmt, TableItem},
    lifter::ssa::SymbolId,
};

#[allow(dead_code, reason = "might be used in the future")]
pub trait Visitor {
    fn visit_function(&mut self, fun: &StructuredFunction) {
        walk_function(self, fun);
    }

    // note to self: if I ever need dyn Visitor, force `Self: Sized` here
    fn visit_graph(&mut self, graph: impl GraphView<Item = Block>) {
        let order = graph
            .reverse_post_order()
            .into_iter()
            .map(|node| graph.get(node).expect("this block should exist"));
        for block in order {
            self.visit_block(block);
        }
    }

    fn visit_region(&mut self, region: &RegionNode) {
        walk_region(self, region);
    }

    fn visit_block(&mut self, block: &Block) {
        walk_block(self, block);
    }

    fn visit_block_exit(&mut self, exit: &BlockExit) {
        walk_block_exit(self, exit);
    }

    fn visit_stmts(&mut self, stmts: &[Stmt]) {
        walk_stmts(self, stmts);
    }

    fn visit_stmt(&mut self, stmt: &Stmt) {
        walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &Expr) {
        walk_expr(self, expr);
    }

    fn visit_lvalue_expr(&mut self, expr: &Expr) {
        walk_lvalue_expr(self, expr);
    }

    fn visit_table_item(&mut self, item: &TableItem) {
        walk_table_item(self, item);
    }

    fn visit_phi(&mut self, _phi: &PhiNode) {}

    fn visit_capture(&mut self, _index: usize, _sym: SymbolId) {}

    fn visit_symbol(&mut self, _sym: SymbolId) {}

    fn visit_number(&mut self, _number: Number) {}

    fn visit_string(&mut self, _string: &str) {}

    fn visit_bool(&mut self, _value: bool) {}

    fn visit_global(&mut self, _name: &str) {}

    fn visit_import(&mut self, _path: &str) {}
}

#[allow(dead_code, reason = "might be used in the future")]
pub trait VisitorMut {
    fn visit_function(&mut self, fun: &mut StructuredFunction) {
        walk_function_mut(self, fun);
    }

    fn visit_region(&mut self, region: &mut RegionNode) {
        walk_region_mut(self, region);
    }

    fn visit_block(&mut self, block: &mut Block) {
        walk_block_mut(self, block);
    }

    fn visit_block_exit(&mut self, exit: &mut BlockExit) {
        walk_block_exit_mut(self, exit);
    }

    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        walk_stmts_mut(self, stmts);
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt) {
        walk_stmt_mut(self, stmt);
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        walk_expr_mut(self, expr);
    }

    fn visit_lvalue_expr(&mut self, expr: &mut Expr) {
        walk_lvalue_expr_mut(self, expr);
    }

    fn visit_table_item(&mut self, item: &mut TableItem) {
        walk_table_item_mut(self, item);
    }

    fn visit_phi(&mut self, _phi: &mut PhiNode) {}

    fn visit_capture(&mut self, _index: usize, _sym: &mut SymbolId) {}

    fn visit_symbol(&mut self, _sym: &mut SymbolId) {}

    fn visit_number(&mut self, _number: &mut Number) {}

    fn visit_string(&mut self, _string: &mut String) {}

    fn visit_bool(&mut self, _value: &mut bool) {}

    fn visit_global(&mut self, _name: &mut SmolStr) {}

    fn visit_import(&mut self, _path: &mut SmolStr) {}
}

pub fn walk_function<V: Visitor + ?Sized>(visitor: &mut V, fun: &StructuredFunction) {
    visitor.visit_region(&fun.root);
}

pub fn walk_region<V: Visitor + ?Sized>(visitor: &mut V, node: &RegionNode) {
    match node {
        RegionNode::BasicBlock { stmts } => {
            visitor.visit_stmts(stmts);
        }
        RegionNode::Sequence { nodes } => {
            for n in nodes {
                visitor.visit_region(n);
            }
        }
        RegionNode::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_region(then_branch);
            if let Some(else_branch) = else_branch {
                visitor.visit_region(else_branch);
            }
        }
        RegionNode::While { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_region(body);
        }
        RegionNode::RepeatUntil { condition, body } => {
            visitor.visit_region(body);
            visitor.visit_expr(condition);
        }
        RegionNode::NumericFor {
            body,
            var,
            start,
            end,
            step,
        } => {
            visitor.visit_symbol(*var);
            visitor.visit_expr(start);
            visitor.visit_expr(end);
            visitor.visit_expr(step);
            visitor.visit_region(body);
        }
        RegionNode::GenericFor { body, vars, exprs } => {
            for expr in exprs {
                visitor.visit_expr(expr);
            }
            for var in vars {
                visitor.visit_symbol(*var);
            }
            visitor.visit_region(body);
        }
        RegionNode::Continue | RegionNode::Break => {}
        RegionNode::Return { values } => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
    }
}

pub fn walk_block<V: Visitor + ?Sized>(visitor: &mut V, block: &Block) {
    visitor.visit_stmts(block.stmts());
    visitor.visit_block_exit(block.exit());
}

pub fn walk_block_exit<V: Visitor + ?Sized>(visitor: &mut V, exit: &BlockExit) {
    match exit {
        BlockExit::CondJump { cond, .. } => visitor.visit_expr(cond),
        BlockExit::FornPrep {
            var,
            start,
            end,
            step,
            ..
        } => {
            visitor.visit_symbol(*var);
            visitor.visit_expr(start);
            visitor.visit_expr(end);
            visitor.visit_expr(step);
        }
        BlockExit::FornLoop { .. } => {
            // this block carries no valuable info
        }
        BlockExit::ForgPrep { exprs, .. } => {
            for expr in exprs {
                visitor.visit_expr(expr);
            }
        }
        BlockExit::ForgLoop { vars, .. } => {
            for var in vars {
                visitor.visit_symbol(*var);
            }
        }
        BlockExit::Return(values) => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
        BlockExit::Jump(_) | BlockExit::Fallthrough(_) => {
            // [design limitation] - visitor carries no cfg context, so it cannot jump to the blocks on its own.
        }
    }
}

pub fn walk_stmts<V: Visitor + ?Sized>(visitor: &mut V, stmts: &[Stmt]) {
    for stmt in stmts {
        visitor.visit_stmt(stmt);
    }
}

pub fn walk_stmt<V: Visitor + ?Sized>(visitor: &mut V, stmt: &Stmt) {
    match stmt {
        Stmt::Assign { left, value } => {
            visitor.visit_lvalue_expr(left);
            visitor.visit_expr(value);
        }
        Stmt::AssignMany { left, value } => {
            for lvalue in left {
                visitor.visit_lvalue_expr(lvalue);
            }
            visitor.visit_expr(value);
        }
        Stmt::SetList { table, values, .. } => {
            visitor.visit_symbol(*table);
            for value in values {
                visitor.visit_expr(value);
            }
        }
        Stmt::Call(expr) => visitor.visit_expr(expr),
        Stmt::Phi(phi) => visitor.visit_phi(phi),
    }
}

pub fn walk_expr<V: Visitor + ?Sized>(visitor: &mut V, expr: &Expr) {
    match expr {
        Expr::Nil | Expr::VarArgs => {}
        Expr::Number(number) => visitor.visit_number(*number),
        Expr::String(string) => visitor.visit_string(string),
        Expr::Bool(value) => visitor.visit_bool(*value),
        Expr::Symbol(symbol) => visitor.visit_symbol(*symbol),
        Expr::Closure { captures, .. } => {
            for (index, capture) in captures.iter().enumerate() {
                visitor.visit_capture(index, *capture);
            }
        }
        Expr::Global(name) => visitor.visit_global(name),
        Expr::GetField { obj, .. } => visitor.visit_expr(obj),
        Expr::GetIndex { obj, index } => {
            visitor.visit_expr(obj);
            visitor.visit_expr(index);
        }
        Expr::Call { fun, args } => {
            visitor.visit_expr(fun);
            for arg in args {
                visitor.visit_expr(arg);
            }
        }
        Expr::MethodCall { object, args, .. } => {
            visitor.visit_expr(object);
            for arg in args {
                visitor.visit_expr(arg);
            }
        }
        Expr::Binary { lhs, rhs, .. } => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        Expr::Unary { expr, .. } => visitor.visit_expr(expr),
        Expr::IfElse {
            condition,
            then_expr,
            else_expr,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_expr(then_expr);
            visitor.visit_expr(else_expr);
        }
        Expr::Table { items } => {
            for item in items {
                visitor.visit_table_item(item);
            }
        }
    }
}

pub fn walk_lvalue_expr<V: Visitor + ?Sized>(visitor: &mut V, expr: &Expr) {
    match expr {
        Expr::Symbol(symbol) => visitor.visit_symbol(*symbol),
        Expr::GetField { obj, .. } => visitor.visit_expr(obj),
        Expr::GetIndex { obj, index } => {
            visitor.visit_expr(obj);
            visitor.visit_expr(index);
        }
        _ => walk_expr(visitor, expr),
    }
}

pub fn walk_table_item<V: Visitor + ?Sized>(visitor: &mut V, item: &TableItem) {
    match item {
        TableItem::List(expr) => visitor.visit_expr(expr),
        TableItem::Index(key, value) => {
            visitor.visit_expr(key);
            visitor.visit_expr(value);
        }
    }
}

pub fn walk_function_mut<V: VisitorMut + ?Sized>(visitor: &mut V, fun: &mut StructuredFunction) {
    let root = &mut fun.root;
    visitor.visit_region(root);
}

pub fn walk_region_mut<V: VisitorMut + ?Sized>(visitor: &mut V, node: &mut RegionNode) {
    match node {
        RegionNode::BasicBlock { stmts } => {
            visitor.visit_stmts(stmts);
        }
        RegionNode::Sequence { nodes } => {
            for n in nodes {
                visitor.visit_region(n);
            }
        }
        RegionNode::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_region(then_branch);
            if let Some(else_branch) = else_branch {
                visitor.visit_region(else_branch);
            }
        }
        RegionNode::While { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_region(body);
        }
        RegionNode::RepeatUntil { condition, body } => {
            visitor.visit_region(body);
            visitor.visit_expr(condition);
        }
        RegionNode::NumericFor {
            body,
            var,
            start,
            end,
            step,
        } => {
            visitor.visit_symbol(var);
            visitor.visit_expr(start);
            visitor.visit_expr(end);
            visitor.visit_expr(step);
            visitor.visit_region(body);
        }
        RegionNode::GenericFor { body, vars, exprs } => {
            for expr in exprs {
                visitor.visit_expr(expr);
            }
            for var in vars {
                visitor.visit_symbol(var);
            }
            visitor.visit_region(body);
        }
        RegionNode::Continue | RegionNode::Break => {}
        RegionNode::Return { values } => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
    }
}

pub fn walk_block_mut<V: VisitorMut + ?Sized>(visitor: &mut V, block: &mut Block) {
    for stmt in block.stmts_mut() {
        visitor.visit_stmt(stmt);
    }
    visitor.visit_block_exit(block.exit_mut());
}

pub fn walk_block_exit_mut<V: VisitorMut + ?Sized>(visitor: &mut V, exit: &mut BlockExit) {
    match exit {
        BlockExit::CondJump { cond, .. } => visitor.visit_expr(cond),
        BlockExit::FornPrep {
            var,
            start,
            end,
            step,
            ..
        } => {
            visitor.visit_symbol(var);
            visitor.visit_expr(start);
            visitor.visit_expr(end);
            visitor.visit_expr(step);
        }
        BlockExit::FornLoop { .. } => {
            // this block carries no valuable info
        }
        BlockExit::ForgPrep { exprs, .. } => {
            for expr in exprs {
                visitor.visit_expr(expr);
            }
        }
        BlockExit::ForgLoop { vars, .. } => {
            for var in vars {
                visitor.visit_symbol(var);
            }
        }
        BlockExit::Return(values) => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
        BlockExit::Jump(_) | BlockExit::Fallthrough(_) => {
            // [design limitation] - visitor carries no cfg context, so it cannot jump to the blocks on its own.
        }
    }
}

pub fn walk_stmts_mut<V: VisitorMut + ?Sized>(visitor: &mut V, stmts: &mut Vec<Stmt>) {
    for stmt in stmts {
        visitor.visit_stmt(stmt);
    }
}

pub fn walk_stmt_mut<V: VisitorMut + ?Sized>(visitor: &mut V, stmt: &mut Stmt) {
    match stmt {
        Stmt::Assign { left, value } => {
            visitor.visit_lvalue_expr(left);
            visitor.visit_expr(value);
        }
        Stmt::AssignMany { left, value } => {
            for lvalue in left {
                visitor.visit_lvalue_expr(lvalue);
            }
            visitor.visit_expr(value);
        }
        Stmt::SetList { table, values, .. } => {
            visitor.visit_symbol(table);
            for value in values {
                visitor.visit_expr(value);
            }
        }
        Stmt::Call(expr) => visitor.visit_expr(expr),
        Stmt::Phi(phi) => visitor.visit_phi(phi),
    }
}

pub fn walk_expr_mut<V: VisitorMut + ?Sized>(visitor: &mut V, expr: &mut Expr) {
    match expr {
        Expr::Nil | Expr::VarArgs => {}
        Expr::Number(number) => visitor.visit_number(number),
        Expr::String(string) => visitor.visit_string(string),
        Expr::Bool(value) => visitor.visit_bool(value),
        Expr::Symbol(symbol) => visitor.visit_symbol(symbol),
        Expr::Closure { captures, .. } => {
            for (index, capture) in captures.iter_mut().enumerate() {
                visitor.visit_capture(index, capture);
            }
        }
        Expr::Global(name) => visitor.visit_global(name),
        Expr::GetField { obj, .. } => visitor.visit_expr(obj),
        Expr::GetIndex { obj, index } => {
            visitor.visit_expr(obj);
            visitor.visit_expr(index);
        }
        Expr::Call { fun, args } => {
            visitor.visit_expr(fun);
            for arg in args {
                visitor.visit_expr(arg);
            }
        }
        Expr::MethodCall { object, args, .. } => {
            visitor.visit_expr(object);
            for arg in args {
                visitor.visit_expr(arg);
            }
        }
        Expr::Binary { lhs, rhs, .. } => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        Expr::Unary { expr, .. } => visitor.visit_expr(expr),
        Expr::IfElse {
            condition,
            then_expr,
            else_expr,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_expr(then_expr);
            visitor.visit_expr(else_expr);
        }
        Expr::Table { items } => {
            for item in items {
                visitor.visit_table_item(item);
            }
        }
    }
}

pub fn walk_lvalue_expr_mut<V: VisitorMut + ?Sized>(visitor: &mut V, expr: &mut Expr) {
    match expr {
        Expr::Symbol(symbol) => visitor.visit_symbol(symbol),
        Expr::GetField { obj, .. } => visitor.visit_expr(obj),
        Expr::GetIndex { obj, index } => {
            visitor.visit_expr(obj);
            visitor.visit_expr(index);
        }
        _ => walk_expr_mut(visitor, expr),
    }
}

pub fn walk_table_item_mut<V: VisitorMut + ?Sized>(visitor: &mut V, item: &mut TableItem) {
    match item {
        TableItem::List(expr) => visitor.visit_expr(expr),
        TableItem::Index(key, value) => {
            visitor.visit_expr(key);
            visitor.visit_expr(value);
        }
    }
}
