use smol_str::SmolStr;

use crate::hil::{
    StructuredFunction,
    cflow::{
        graph::{Block, ControlFlowGraph},
        region::{RegionBlock, RegionNode},
    },
    ir::{HilExpr, HilStmt, HilTableItem, PhiNode, Spanned},
    lifter::ssa::SymbolId,
};

pub trait Visitor {
    fn visit_function(&mut self, fun: &StructuredFunction) {
        walk_function(self, fun);
    }

    fn visit_region(&mut self, region: &RegionBlock, cfg: &ControlFlowGraph) {
        walk_region(self, region, cfg);
    }

    fn visit_node(&mut self, node: &RegionNode, cfg: &ControlFlowGraph) {
        walk_node(self, node, cfg);
    }

    fn visit_block(&mut self, block_id: usize, block: &Block, cfg: &ControlFlowGraph) {
        walk_block(self, block_id, block, cfg);
    }

    fn visit_stmt_spanned(&mut self, stmt: &Spanned<HilStmt>) {
        self.visit_stmt(&stmt.inner);
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

    fn visit_phi(&mut self, phi: &PhiNode) {
        self.visit_binding_symbol(phi.target);
        for (_, operand) in &phi.operands {
            self.visit_symbol(*operand);
        }
    }

    fn visit_binding_symbol(&mut self, sym: SymbolId) {
        self.visit_symbol(sym);
    }

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

    fn visit_region(&mut self, region: &mut RegionBlock, cfg: &mut ControlFlowGraph) {
        walk_region_mut(self, region, cfg);
    }

    fn visit_node(&mut self, node: &mut RegionNode, cfg: &mut ControlFlowGraph) {
        walk_node_mut(self, node, cfg);
    }

    fn visit_block(&mut self, block_id: usize, block: &mut Block) {
        walk_block_mut(self, block_id, block);
    }

    fn visit_stmt_spanned(&mut self, stmt: &mut Spanned<HilStmt>) {
        self.visit_stmt(&mut stmt.inner);
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

    fn visit_phi(&mut self, phi: &mut PhiNode) {
        self.visit_binding_symbol(&mut phi.target);
        for (_, operand) in &mut phi.operands {
            self.visit_symbol(operand);
        }
    }

    fn visit_binding_symbol(&mut self, sym: &mut SymbolId) {
        self.visit_symbol(sym);
    }

    fn visit_symbol(&mut self, _sym: &mut SymbolId) {}

    fn visit_number(&mut self, _number: &mut f64) {}

    fn visit_string(&mut self, _string: &mut String) {}

    fn visit_bool(&mut self, _value: &mut bool) {}

    fn visit_global(&mut self, _name: &mut SmolStr) {}

    fn visit_import(&mut self, _path: &mut SmolStr) {}
}

pub fn walk_function<V: Visitor + ?Sized>(visitor: &mut V, fun: &StructuredFunction) {
    visitor.visit_region(&fun.root, &fun.cfg);
}

pub fn walk_region<V: Visitor + ?Sized>(
    visitor: &mut V,
    region: &RegionBlock,
    cfg: &ControlFlowGraph,
) {
    for node in &region.nodes {
        visitor.visit_node(node, cfg);
    }
}

pub fn walk_node<V: Visitor + ?Sized>(visitor: &mut V, node: &RegionNode, cfg: &ControlFlowGraph) {
    match node {
        RegionNode::BasicBlock { block } => {
            if let Some(block_data) = cfg.blocks.get(*block) {
                visitor.visit_block(*block, block_data, cfg);
            }
        }
        RegionNode::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_region(then_branch, cfg);
            visitor.visit_region(else_branch, cfg);
        }
        RegionNode::While { condition, body } | RegionNode::RepeatUntil { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_region(body, cfg);
        }
        RegionNode::NumericFor { body, .. } | RegionNode::GenericFor { body, .. } => {
            visitor.visit_region(body, cfg);
        }
        RegionNode::Continue | RegionNode::Break => {}
        RegionNode::Return { values } => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
    }
}

pub fn walk_block<V: Visitor + ?Sized>(
    visitor: &mut V,
    _block_id: usize,
    block: &Block,
    _cfg: &ControlFlowGraph,
) {
    for stmt in &block.stmts {
        visitor.visit_stmt_spanned(stmt);
    }
}

pub fn walk_stmt<V: Visitor + ?Sized>(visitor: &mut V, stmt: &HilStmt) {
    match stmt {
        HilStmt::Assign { left, value } => {
            visitor.visit_lvalue_expr(left);
            visitor.visit_expr(value);
        }
        HilStmt::AssignMany { left, value } => {
            for symbol in left {
                visitor.visit_binding_symbol(*symbol);
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
            for capture in captures {
                visitor.visit_symbol(*capture);
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
        HilExpr::If {
            condition,
            then_expr,
            else_expr,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_expr(then_expr);
            visitor.visit_expr(else_expr);
        }
        HilExpr::Table { items } => {
            for item in items {
                visitor.visit_table_item(item);
            }
        }
    }
}

pub fn walk_lvalue_expr<V: Visitor + ?Sized>(visitor: &mut V, expr: &HilExpr) {
    match expr {
        HilExpr::Symbol(symbol) => visitor.visit_binding_symbol(*symbol),
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
        HilTableItem::List(expr) | HilTableItem::Packed(expr) => visitor.visit_expr(expr),
        HilTableItem::Index(key, value) => {
            visitor.visit_expr(key);
            visitor.visit_expr(value);
        }
    }
}

pub fn walk_function_mut<V: VisitorMut + ?Sized>(visitor: &mut V, fun: &mut StructuredFunction) {
    let root = &mut fun.root;
    let cfg = &mut fun.cfg;
    visitor.visit_region(root, cfg);
}

pub fn walk_region_mut<V: VisitorMut + ?Sized>(
    visitor: &mut V,
    region: &mut RegionBlock,
    cfg: &mut ControlFlowGraph,
) {
    for node in &mut region.nodes {
        visitor.visit_node(node, cfg);
    }
}

pub fn walk_node_mut<V: VisitorMut + ?Sized>(
    visitor: &mut V,
    node: &mut RegionNode,
    cfg: &mut ControlFlowGraph,
) {
    match node {
        RegionNode::BasicBlock { block } => {
            if let Some(block_data) = cfg.blocks.get_mut(*block) {
                visitor.visit_block(*block, block_data);
            }
        }
        RegionNode::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_region(then_branch, cfg);
            visitor.visit_region(else_branch, cfg);
        }
        RegionNode::While { condition, body } | RegionNode::RepeatUntil { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_region(body, cfg);
        }
        RegionNode::NumericFor { body, .. } | RegionNode::GenericFor { body, .. } => {
            visitor.visit_region(body, cfg);
        }
        RegionNode::Continue | RegionNode::Break => {}
        RegionNode::Return { values } => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
    }
}

pub fn walk_block_mut<V: VisitorMut + ?Sized>(
    visitor: &mut V,
    _block_id: usize,
    block: &mut Block,
) {
    for stmt in &mut block.stmts {
        visitor.visit_stmt_spanned(stmt);
    }
}

pub fn walk_stmt_mut<V: VisitorMut + ?Sized>(visitor: &mut V, stmt: &mut HilStmt) {
    match stmt {
        HilStmt::Assign { left, value } => {
            visitor.visit_lvalue_expr(left);
            visitor.visit_expr(value);
        }
        HilStmt::AssignMany { left, value } => {
            for symbol in left {
                visitor.visit_binding_symbol(symbol);
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
            for capture in captures {
                visitor.visit_symbol(capture);
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
        HilExpr::If {
            condition,
            then_expr,
            else_expr,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_expr(then_expr);
            visitor.visit_expr(else_expr);
        }
        HilExpr::Table { items } => {
            for item in items {
                visitor.visit_table_item(item);
            }
        }
    }
}

pub fn walk_lvalue_expr_mut<V: VisitorMut + ?Sized>(visitor: &mut V, expr: &mut HilExpr) {
    match expr {
        HilExpr::Symbol(symbol) => visitor.visit_binding_symbol(symbol),
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
        HilTableItem::List(expr) | HilTableItem::Packed(expr) => visitor.visit_expr(expr),
        HilTableItem::Index(key, value) => {
            visitor.visit_expr(key);
            visitor.visit_expr(value);
        }
    }
}
