#![allow(
    dead_code,
    reason = "visitor infrastructure may be used by future NIR passes"
)]

use crate::common::ByteString;
use crate::hil::ir::{CellId, Number};
use crate::ir::fir::Constant;
use crate::ir::nir::TableItem;
use smol_str::SmolStr;

use super::{Capture, Expr, Function, PackExpr, Place, Region, Stmt};
use super::{LocalId, PackLocalId};

/// Visits NIR without changing it.
pub trait Visitor {
    /// Visits one complete NIR function.
    fn visit_function(&mut self, function: &Function) {
        walk_function(self, function);
    }

    /// Visits one nested control-flow region.
    fn visit_region(&mut self, region: &Region) {
        walk_region(self, region);
    }

    /// Visits a list of statements in evaluation order.
    fn visit_stmts(&mut self, stmts: &[Stmt]) {
        walk_stmts(self, stmts);
    }

    /// Visits one statement.
    fn visit_stmt(&mut self, stmt: &Stmt) {
        walk_stmt(self, stmt);
    }

    /// Visits one value expression.
    fn visit_expr(&mut self, expr: &Expr) {
        walk_expr(self, expr);
    }

    /// Visits one value-pack expression.
    fn visit_pack_expr(&mut self, pack: &PackExpr) {
        walk_pack_expr(self, pack);
    }

    /// Visits one writable place.
    fn visit_place(&mut self, place: &Place) {
        walk_place(self, place);
    }

    /// Visits one closure capture.
    fn visit_capture(&mut self, _index: usize, capture: Capture) {
        match capture {
            Capture::Copy(local) => self.visit_local(local),
            Capture::Share(cell) => self.visit_cell(cell),
        }
    }

    /// Visits one literal constant.
    fn visit_constant(&mut self, constant: &Constant) {
        match constant {
            Constant::Nil => {}
            Constant::Number(number) => self.visit_number(*number),
            Constant::String(string) => self.visit_string(string),
            Constant::Bool(value) => self.visit_bool(*value),
        }
    }

    /// Visits one table item.
    fn visit_table_item(&mut self, item: &TableItem) {
        match item {
            TableItem::List(pack) => self.visit_pack_expr(pack),
            TableItem::Index(key, value) => {
                self.visit_expr(key);
                self.visit_expr(value);
            }
        }
    }

    /// Visits one NIR local identity.
    fn visit_local(&mut self, _local: LocalId) {}

    /// Visits one NIR pack-local identity.
    fn visit_pack_local(&mut self, _local: PackLocalId) {}

    /// Visits one mutable cell identity.
    fn visit_cell(&mut self, _cell: CellId) {}

    /// Visits one numeric constant.
    fn visit_number(&mut self, _number: Number) {}

    /// Visits one byte string constant.
    fn visit_string(&mut self, _string: &ByteString) {}

    /// Visits one boolean constant.
    fn visit_bool(&mut self, _value: bool) {}

    /// Visits one global name.
    fn visit_global(&mut self, _name: &str) {}
}

/// Visits NIR while allowing every visited value to be changed.
pub trait VisitorMut {
    /// Visits one complete NIR function.
    fn visit_function(&mut self, function: &mut Function) {
        walk_function_mut(self, function);
    }

    /// Visits one nested control-flow region.
    fn visit_region(&mut self, region: &mut Region) {
        walk_region_mut(self, region);
    }

    /// Visits a mutable list of statements in evaluation order.
    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        walk_stmts_mut(self, stmts);
    }

    /// Visits one mutable statement.
    fn visit_stmt(&mut self, stmt: &mut Stmt) {
        walk_stmt_mut(self, stmt);
    }

    /// Visits one mutable value expression.
    fn visit_expr(&mut self, expr: &mut Expr) {
        walk_expr_mut(self, expr);
    }

    /// Visits one mutable value-pack expression.
    fn visit_pack_expr(&mut self, pack: &mut PackExpr) {
        walk_pack_expr_mut(self, pack);
    }

    /// Visits one mutable writable place.
    fn visit_place(&mut self, place: &mut Place) {
        walk_place_mut(self, place);
    }

    /// Visits one mutable closure capture.
    fn visit_capture(&mut self, _index: usize, capture: &mut Capture) {
        match capture {
            Capture::Copy(local) => self.visit_local(local),
            Capture::Share(cell) => self.visit_cell(cell),
        }
    }

    /// Visits one mutable literal constant.
    fn visit_constant(&mut self, constant: &mut Constant) {
        match constant {
            Constant::Nil => {}
            Constant::Number(number) => self.visit_number(number),
            Constant::String(string) => self.visit_string(string),
            Constant::Bool(value) => self.visit_bool(value),
        }
    }

    /// Visits one mutable table item.
    fn visit_table_item(&mut self, item: &mut TableItem) {
        match item {
            TableItem::List(pack) => self.visit_pack_expr(pack),
            TableItem::Index(key, value) => {
                self.visit_expr(key);
                self.visit_expr(value);
            }
        }
    }

    /// Visits one mutable NIR local identity.
    fn visit_local(&mut self, _local: &mut LocalId) {}

    /// Visits one mutable NIR pack-local identity.
    fn visit_pack_local(&mut self, _local: &mut PackLocalId) {}

    /// Visits one mutable cell identity.
    fn visit_cell(&mut self, _cell: &mut CellId) {}

    /// Visits one mutable numeric constant.
    fn visit_number(&mut self, _number: &mut Number) {}

    /// Visits one mutable byte string constant.
    fn visit_string(&mut self, _string: &mut ByteString) {}

    /// Visits one mutable boolean constant.
    fn visit_bool(&mut self, _value: &mut bool) {}

    /// Visits one mutable global name.
    fn visit_global(&mut self, _name: &mut SmolStr) {}
}

/// Walks a complete NIR function in source evaluation order.
pub fn walk_function<V: Visitor + ?Sized>(visitor: &mut V, function: &Function) {
    visitor.visit_stmts(&function.prologue);
    visitor.visit_region(&function.body);
}

/// Walks one NIR control-flow region in source evaluation order.
pub fn walk_region<V: Visitor + ?Sized>(visitor: &mut V, region: &Region) {
    match region {
        Region::Block { stmts, .. } => visitor.visit_stmts(stmts),
        Region::Sequence(nodes) => {
            for node in nodes {
                visitor.visit_region(node);
            }
        }
        Region::If {
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
        Region::While { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_region(body);
        }
        Region::RepeatUntil { condition, body } => {
            visitor.visit_region(body);
            visitor.visit_expr(condition);
        }
        Region::NumericFor {
            variable,
            start,
            end,
            step,
            body,
        } => {
            visitor.visit_local(*variable);
            visitor.visit_expr(start);
            visitor.visit_expr(end);
            visitor.visit_expr(step);
            visitor.visit_region(body);
        }
        Region::GenericFor {
            variables,
            values,
            body,
        } => {
            for variable in variables {
                visitor.visit_local(*variable);
            }
            for value in values {
                visitor.visit_expr(value);
            }
            visitor.visit_region(body);
        }
        Region::Continue | Region::Break => {}
        Region::Return(values) => visitor.visit_pack_expr(values),
    }
}

/// Walks a list of statements in evaluation order.
pub fn walk_stmts<V: Visitor + ?Sized>(visitor: &mut V, stmts: &[Stmt]) {
    for stmt in stmts {
        visitor.visit_stmt(stmt);
    }
}

/// Walks one statement in evaluation order.
pub fn walk_stmt<V: Visitor + ?Sized>(visitor: &mut V, stmt: &Stmt) {
    match stmt {
        Stmt::Bind { target, value, .. } => {
            visitor.visit_place(target);
            visitor.visit_expr(value);
        }
        Stmt::BindMany { targets, values } => {
            for target in targets {
                visitor.visit_place(target);
            }
            visitor.visit_pack_expr(values);
        }
        Stmt::BindPack { local, value } => {
            visitor.visit_pack_local(*local);
            visitor.visit_pack_expr(value);
        }
        Stmt::Eval { value } => visitor.visit_pack_expr(value),
        Stmt::OpenCell { cell, value, .. } => {
            visitor.visit_cell(*cell);
            visitor.visit_expr(value);
        }
        Stmt::SetList { table, values, .. } => {
            visitor.visit_expr(table);
            visitor.visit_pack_expr(values);
        }
    }
}

/// Walks one value expression in evaluation order.
pub fn walk_expr<V: Visitor + ?Sized>(visitor: &mut V, expr: &Expr) {
    match expr {
        Expr::Local(local) => visitor.visit_local(*local),
        Expr::Constant(constant) => visitor.visit_constant(constant),
        Expr::Closure { captures, .. } => {
            for (index, capture) in captures.iter().copied().enumerate() {
                visitor.visit_capture(index, capture);
            }
        }
        Expr::GetTable { table, key } => {
            visitor.visit_expr(table);
            visitor.visit_expr(key);
        }
        Expr::GetGlobal(name) => visitor.visit_global(name),
        Expr::Binary { lhs, rhs, .. } => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        Expr::Unary { value, .. } => visitor.visit_expr(value),
        Expr::Concat(values) => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
        Expr::Select {
            condition,
            then_value,
            else_value,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_expr(then_value);
            visitor.visit_expr(else_value);
        }
        Expr::Table { items } => {
            for item in items {
                visitor.visit_table_item(item);
            }
        }
        Expr::Project { pack, .. } => visitor.visit_pack_expr(pack),
        Expr::LoadCell(cell) => visitor.visit_cell(*cell),
    }
}

/// Walks one writable place in evaluation order.
pub fn walk_place<V: Visitor + ?Sized>(visitor: &mut V, place: &Place) {
    match place {
        Place::Local(local) => visitor.visit_local(*local),
        Place::Cell(cell) => visitor.visit_cell(*cell),
        Place::Global(name) => visitor.visit_global(name),
        Place::Table { table, key } => {
            visitor.visit_expr(table);
            visitor.visit_expr(key);
        }
        Place::Discard => {}
    }
}

/// Walks one value-pack expression in evaluation order.
pub fn walk_pack_expr<V: Visitor + ?Sized>(visitor: &mut V, pack: &PackExpr) {
    match pack {
        PackExpr::Local(local) => visitor.visit_pack_local(*local),
        PackExpr::Values { head, tail } => {
            for value in head {
                visitor.visit_expr(value);
            }
            if let Some(tail) = tail {
                visitor.visit_pack_expr(tail);
            }
        }
        PackExpr::Call { function, args } => {
            visitor.visit_expr(function);
            visitor.visit_pack_expr(args);
        }
        PackExpr::MethodCall { object, args, .. } => {
            visitor.visit_expr(object);
            visitor.visit_pack_expr(args);
        }
        PackExpr::VarArgs => {}
    }
}

/// Walks a complete mutable NIR function in source evaluation order.
pub fn walk_function_mut<V: VisitorMut + ?Sized>(visitor: &mut V, function: &mut Function) {
    visitor.visit_stmts(&mut function.prologue);
    visitor.visit_region(&mut function.body);
}

/// Walks one mutable NIR control-flow region in source evaluation order.
pub fn walk_region_mut<V: VisitorMut + ?Sized>(visitor: &mut V, region: &mut Region) {
    match region {
        Region::Block { stmts, .. } => visitor.visit_stmts(stmts),
        Region::Sequence(nodes) => {
            for node in nodes {
                visitor.visit_region(node);
            }
        }
        Region::If {
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
        Region::While { condition, body } => {
            visitor.visit_expr(condition);
            visitor.visit_region(body);
        }
        Region::RepeatUntil { condition, body } => {
            visitor.visit_region(body);
            visitor.visit_expr(condition);
        }
        Region::NumericFor {
            variable,
            start,
            end,
            step,
            body,
        } => {
            visitor.visit_local(variable);
            visitor.visit_expr(start);
            visitor.visit_expr(end);
            visitor.visit_expr(step);
            visitor.visit_region(body);
        }
        Region::GenericFor {
            variables,
            values,
            body,
        } => {
            for variable in variables {
                visitor.visit_local(variable);
            }
            for value in values {
                visitor.visit_expr(value);
            }
            visitor.visit_region(body);
        }
        Region::Continue | Region::Break => {}
        Region::Return(values) => visitor.visit_pack_expr(values),
    }
}

/// Walks a mutable list of statements in evaluation order.
pub fn walk_stmts_mut<V: VisitorMut + ?Sized>(visitor: &mut V, stmts: &mut Vec<Stmt>) {
    for stmt in stmts {
        visitor.visit_stmt(stmt);
    }
}

/// Walks one mutable statement in evaluation order.
pub fn walk_stmt_mut<V: VisitorMut + ?Sized>(visitor: &mut V, stmt: &mut Stmt) {
    match stmt {
        Stmt::Bind { target, value, .. } => {
            visitor.visit_place(target);
            visitor.visit_expr(value);
        }
        Stmt::BindMany { targets, values } => {
            for target in targets {
                visitor.visit_place(target);
            }
            visitor.visit_pack_expr(values);
        }
        Stmt::BindPack { local, value } => {
            visitor.visit_pack_local(local);
            visitor.visit_pack_expr(value);
        }
        Stmt::Eval { value } => visitor.visit_pack_expr(value),
        Stmt::OpenCell { cell, value, .. } => {
            visitor.visit_cell(cell);
            visitor.visit_expr(value);
        }
        Stmt::SetList { table, values, .. } => {
            visitor.visit_expr(table);
            visitor.visit_pack_expr(values);
        }
    }
}

/// Walks one mutable value expression in evaluation order.
pub fn walk_expr_mut<V: VisitorMut + ?Sized>(visitor: &mut V, expr: &mut Expr) {
    match expr {
        Expr::Local(local) => visitor.visit_local(local),
        Expr::Constant(constant) => visitor.visit_constant(constant),
        Expr::Closure { captures, .. } => {
            for (index, capture) in captures.iter_mut().enumerate() {
                visitor.visit_capture(index, capture);
            }
        }
        Expr::GetTable { table, key } => {
            visitor.visit_expr(table);
            visitor.visit_expr(key);
        }
        Expr::GetGlobal(name) => visitor.visit_global(name),
        Expr::Binary { lhs, rhs, .. } => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        Expr::Unary { value, .. } => visitor.visit_expr(value),
        Expr::Concat(values) => {
            for value in values {
                visitor.visit_expr(value);
            }
        }
        Expr::Select {
            condition,
            then_value,
            else_value,
        } => {
            visitor.visit_expr(condition);
            visitor.visit_expr(then_value);
            visitor.visit_expr(else_value);
        }
        Expr::Table { items } => {
            for item in items {
                visitor.visit_table_item(item);
            }
        }
        Expr::Project { pack, .. } => visitor.visit_pack_expr(pack),
        Expr::LoadCell(cell) => visitor.visit_cell(cell),
    }
}

/// Walks one mutable writable place in evaluation order.
pub fn walk_place_mut<V: VisitorMut + ?Sized>(visitor: &mut V, place: &mut Place) {
    match place {
        Place::Local(local) => visitor.visit_local(local),
        Place::Cell(cell) => visitor.visit_cell(cell),
        Place::Global(name) => visitor.visit_global(name),
        Place::Table { table, key } => {
            visitor.visit_expr(table);
            visitor.visit_expr(key);
        }
        Place::Discard => {}
    }
}

/// Walks one mutable value-pack expression in evaluation order.
pub fn walk_pack_expr_mut<V: VisitorMut + ?Sized>(visitor: &mut V, pack: &mut PackExpr) {
    match pack {
        PackExpr::Local(local) => visitor.visit_pack_local(local),
        PackExpr::Values { head, tail } => {
            for value in head {
                visitor.visit_expr(value);
            }
            if let Some(tail) = tail {
                visitor.visit_pack_expr(tail);
            }
        }
        PackExpr::Call { function, args } => {
            visitor.visit_expr(function);
            visitor.visit_pack_expr(args);
        }
        PackExpr::MethodCall { object, args, .. } => {
            visitor.visit_expr(object);
            visitor.visit_pack_expr(args);
        }
        PackExpr::VarArgs => {}
    }
}
