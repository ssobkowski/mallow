use smol_str::SmolStr;

use crate::hil::{
    StructuredFunction,
    cflow::region::RegionNode,
    ir::{HilExpr, HilStmt, HilTableItem, PhiNode},
    lifter::ssa::SymbolId,
};

pub trait Visitor {
    fn visit_function(&mut self, fun: &StructuredFunction) {
        walk_function(self, fun);
    }

    fn visit_region(&mut self, region: &RegionNode) {
        walk_region(self, region);
    }

    fn visit_block(&mut self, stmts: &[HilStmt]) {
        walk_block(self, stmts);
    }

    fn visit_stmt(&mut self, stmt: &HilStmt) {
        walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &HilExpr) {
        walk_expr(self, expr);
    }

    fn visit_lvalue_expr(&mut self, expr: &HilExpr) {
        walk_lvalue_expr(self, expr);
    }

    fn visit_table_item(&mut self, item: &HilTableItem) {
        walk_table_item(self, item);
    }

    fn visit_phi(&mut self, _phi: &PhiNode) {}

    fn visit_capture(&mut self, _index: usize, _sym: SymbolId) {}

    fn visit_symbol(&mut self, _sym: SymbolId) {}

    fn visit_number(&mut self, _number: f64) {}

    fn visit_string(&mut self, _string: &str) {}

    fn visit_bool(&mut self, _value: bool) {}

    fn visit_global(&mut self, _name: &str) {}

    fn visit_import(&mut self, _path: &str) {}
}

pub trait VisitorMut {
    fn visit_function(&mut self, fun: &mut StructuredFunction) {
        walk_function_mut(self, fun);
    }

    fn visit_region(&mut self, region: &mut RegionNode) {
        walk_region_mut(self, region);
    }

    fn visit_block(&mut self, stmts: &mut Vec<HilStmt>) {
        walk_block_mut(self, stmts);
    }

    fn visit_stmt(&mut self, stmt: &mut HilStmt) {
        walk_stmt_mut(self, stmt);
    }

    fn visit_expr(&mut self, expr: &mut HilExpr) {
        walk_expr_mut(self, expr);
    }

    fn visit_lvalue_expr(&mut self, expr: &mut HilExpr) {
        walk_lvalue_expr_mut(self, expr);
    }

    fn visit_table_item(&mut self, item: &mut HilTableItem) {
        walk_table_item_mut(self, item);
    }

    fn visit_phi(&mut self, _phi: &mut PhiNode) {}

    fn visit_capture(&mut self, _index: usize, _sym: &mut SymbolId) {}

    fn visit_symbol(&mut self, _sym: &mut SymbolId) {}

    fn visit_number(&mut self, _number: &mut f64) {}

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
            visitor.visit_block(stmts);
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
        RegionNode::While { condition, body } | RegionNode::RepeatUntil { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_region(body);
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

pub fn walk_block<V: Visitor + ?Sized>(visitor: &mut V, stmts: &[HilStmt]) {
    for stmt in stmts {
        visitor.visit_stmt(stmt);
    }
}

pub fn walk_stmt<V: Visitor + ?Sized>(visitor: &mut V, stmt: &HilStmt) {
    match stmt {
        HilStmt::Assign { left, value } => {
            visitor.visit_lvalue_expr(left);
            visitor.visit_expr(value);
        }
        HilStmt::AssignMany { left, value } => {
            for lvalue in left {
                visitor.visit_lvalue_expr(lvalue);
            }
            visitor.visit_expr(value);
        }
        HilStmt::SetList { table, values, .. } => {
            visitor.visit_symbol(*table);
            for value in values {
                visitor.visit_expr(value);
            }
        }
        HilStmt::Call(expr) => visitor.visit_expr(expr),
        HilStmt::Phi(phi) => visitor.visit_phi(phi),
    }
}

pub fn walk_expr<V: Visitor + ?Sized>(visitor: &mut V, expr: &HilExpr) {
    match expr {
        HilExpr::Nil | HilExpr::VarArgs => {}
        HilExpr::Number(number) => visitor.visit_number(*number),
        HilExpr::String(string) => visitor.visit_string(string),
        HilExpr::Bool(value) => visitor.visit_bool(*value),
        HilExpr::Symbol(symbol) => visitor.visit_symbol(*symbol),
        HilExpr::Closure { captures, .. } => {
            for (index, capture) in captures.iter().enumerate() {
                visitor.visit_capture(index, *capture);
            }
        }
        HilExpr::Global(name) => visitor.visit_global(name),
        HilExpr::Import(path) => visitor.visit_import(path),
        HilExpr::GetField { obj, .. } => visitor.visit_expr(obj),
        HilExpr::GetIndex { obj, index } => {
            visitor.visit_expr(obj);
            visitor.visit_expr(index);
        }
        HilExpr::Call { fun, args } => {
            visitor.visit_expr(fun);
            for arg in args {
                visitor.visit_expr(arg);
            }
        }
        HilExpr::MethodCall { object, args, .. } => {
            visitor.visit_expr(object);
            for arg in args {
                visitor.visit_expr(arg);
            }
        }
        HilExpr::Binary { lhs, rhs, .. } => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        HilExpr::Unary { expr, .. } => visitor.visit_expr(expr),
        HilExpr::Table { items } => {
            for item in items {
                visitor.visit_table_item(item);
            }
        }
    }
}

pub fn walk_lvalue_expr<V: Visitor + ?Sized>(visitor: &mut V, expr: &HilExpr) {
    match expr {
        HilExpr::Symbol(symbol) => visitor.visit_symbol(*symbol),
        HilExpr::GetField { obj, .. } => visitor.visit_expr(obj),
        HilExpr::GetIndex { obj, index } => {
            visitor.visit_expr(obj);
            visitor.visit_expr(index);
        }
        _ => walk_expr(visitor, expr),
    }
}

pub fn walk_table_item<V: Visitor + ?Sized>(visitor: &mut V, item: &HilTableItem) {
    match item {
        HilTableItem::List(expr) => visitor.visit_expr(expr),
        HilTableItem::Index(key, value) => {
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
            visitor.visit_block(stmts);
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
        RegionNode::While { condition, body } | RegionNode::RepeatUntil { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_region(body);
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

pub fn walk_block_mut<V: VisitorMut + ?Sized>(visitor: &mut V, stmts: &mut Vec<HilStmt>) {
    for stmt in stmts {
        visitor.visit_stmt(stmt);
    }
}

pub fn walk_stmt_mut<V: VisitorMut + ?Sized>(visitor: &mut V, stmt: &mut HilStmt) {
    match stmt {
        HilStmt::Assign { left, value } => {
            visitor.visit_lvalue_expr(left);
            visitor.visit_expr(value);
        }
        HilStmt::AssignMany { left, value } => {
            for lvalue in left {
                visitor.visit_lvalue_expr(lvalue);
            }
            visitor.visit_expr(value);
        }
        HilStmt::SetList { table, values, .. } => {
            visitor.visit_symbol(table);
            for value in values {
                visitor.visit_expr(value);
            }
        }
        HilStmt::Call(expr) => visitor.visit_expr(expr),
        HilStmt::Phi(phi) => visitor.visit_phi(phi),
    }
}

pub fn walk_expr_mut<V: VisitorMut + ?Sized>(visitor: &mut V, expr: &mut HilExpr) {
    match expr {
        HilExpr::Nil | HilExpr::VarArgs => {}
        HilExpr::Number(number) => visitor.visit_number(number),
        HilExpr::String(string) => visitor.visit_string(string),
        HilExpr::Bool(value) => visitor.visit_bool(value),
        HilExpr::Symbol(symbol) => visitor.visit_symbol(symbol),
        HilExpr::Closure { captures, .. } => {
            for (index, capture) in captures.iter_mut().enumerate() {
                visitor.visit_capture(index, capture);
            }
        }
        HilExpr::Global(name) => visitor.visit_global(name),
        HilExpr::Import(path) => visitor.visit_import(path),
        HilExpr::GetField { obj, .. } => visitor.visit_expr(obj),
        HilExpr::GetIndex { obj, index } => {
            visitor.visit_expr(obj);
            visitor.visit_expr(index);
        }
        HilExpr::Call { fun, args } => {
            visitor.visit_expr(fun);
            for arg in args {
                visitor.visit_expr(arg);
            }
        }
        HilExpr::MethodCall { object, args, .. } => {
            visitor.visit_expr(object);
            for arg in args {
                visitor.visit_expr(arg);
            }
        }
        HilExpr::Binary { lhs, rhs, .. } => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        HilExpr::Unary { expr, .. } => visitor.visit_expr(expr),
        HilExpr::Table { items } => {
            for item in items {
                visitor.visit_table_item(item);
            }
        }
    }
}

pub fn walk_lvalue_expr_mut<V: VisitorMut + ?Sized>(visitor: &mut V, expr: &mut HilExpr) {
    match expr {
        HilExpr::Symbol(symbol) => visitor.visit_symbol(symbol),
        HilExpr::GetField { obj, .. } => visitor.visit_expr(obj),
        HilExpr::GetIndex { obj, index } => {
            visitor.visit_expr(obj);
            visitor.visit_expr(index);
        }
        _ => walk_expr_mut(visitor, expr),
    }
}

pub fn walk_table_item_mut<V: VisitorMut + ?Sized>(visitor: &mut V, item: &mut HilTableItem) {
    match item {
        HilTableItem::List(expr) => visitor.visit_expr(expr),
        HilTableItem::Index(key, value) => {
            visitor.visit_expr(key);
            visitor.visit_expr(value);
        }
    }
}
