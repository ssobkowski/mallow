//! Statement generation and the program skeleton.

use mallow_core::ast::{Block, ElseClause, Expr, If, Parameter, Stmt, Typed};
use mallow_core::operator::{BinOp, CompoundBinOp};

use crate::config::Config;
use crate::dice::Dice;
use crate::expr::Exprs;
use crate::scope::{BindingId, Kind, Name, Scopes, Signature};
use crate::syntax::{ends_in_terminator, if_then, increment, library_call, local, param, print};

/// The level of the main chunk. It may call every function.
const MAIN_LEVEL: u32 = u32::MAX;
/// The highest level a new function gets.
const MAX_LEVEL: u32 = 6;
/// Luau allows 200 active locals per function. The generator stays well below.
const MAX_LOCALS: usize = 120;
/// Weight of accumulator updates inside `pairs` loop bodies.
const ACCUMULATE_WEIGHT: u32 = 6;

/// One function body being generated.
#[derive(Debug)]
struct Body {
    /// Number of values every `return` produces. The main chunk has none.
    returns: Option<u32>,
    /// `...` holds numbers.
    variadic: bool,
    /// Only functions with a level below this may be called.
    call_level: u32,
    /// `error(...)` may be raised, because the body runs under `pcall`.
    can_error: bool,
    /// Active locals, kept below [`MAX_LOCALS`].
    locals: usize,
    /// Enclosing loops inside this body, innermost last.
    loops: Vec<Loop>,
}

#[derive(Debug, Clone, Copy)]
struct Loop {
    /// `break` may leave this loop.
    breakable: bool,
}

/// Rules for the body of a `pairs` loop.
///
/// `pairs` visits keys in an unspecified order. So the body has no output, no
/// calls and no `break`, and it only assigns locals declared inside it plus
/// two accumulators whose final values do not depend on the order.
#[derive(Debug, Clone, Copy)]
struct Pure {
    /// Bindings declared before this point are read-only.
    floor: BindingId,
    /// Counts with `count += 1`.
    count: Name,
    /// Set to 1 with `if cond then flag = 1 end`.
    flag: Name,
}

/// Prelude functions that generic `for` loops iterate with.
#[derive(Debug, Default)]
struct Helpers {
    /// `local function stepper(limit, i)`, a stateless iterator.
    stepper: Option<Name>,
    /// `local function counter(n)`, which returns a closure iterator.
    counter: Option<Name>,
}

/// What a block ends with, ahead of an optional terminator.
#[derive(Debug, Clone, Default)]
enum Tail {
    #[default]
    None,
    /// `return` with as many values as the current function produces.
    Return,
    /// Assigns every name, which initializes a deferred local.
    Assign(Vec<Name>),
}

/// How to generate one block.
#[derive(Debug)]
struct BlockOptions {
    /// Bindings declared at the start, such as loop variables.
    bindings: Vec<(Name, Kind)>,
    /// Statements placed ahead of the generated ones.
    head: Vec<Stmt>,
    /// Number of statements to generate.
    len: u32,
    tail: Tail,
    /// Probability of ending with `break`, `continue`, `return` or `error`.
    terminate: f64,
    /// Locals of this block may reuse visible names. See [`Scopes::push`].
    shadowing: bool,
}

impl Default for BlockOptions {
    fn default() -> Self {
        Self {
            bindings: Vec::new(),
            head: Vec::new(),
            len: 0,
            tail: Tail::None,
            terminate: 0.0,
            shadowing: true,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Shape {
    Local,
    Assign,
    MultiAssign,
    CompoundAssign,
    Print,
    Call,
    If,
    Guard,
    NumericFor,
    While,
    Repeat,
    Ipairs,
    Pairs,
    IteratorFor,
    Do,
    LocalFunction,
    DeferredInit,
    Closures,
    Pcall,
    Recursion,
    Accumulate,
}

/// Generates one program.
///
/// Every program it generates is:
///
/// * valid, because it only reads visible locals and only puts `break`,
///   `continue` and `return` last in a block where they are legal.
/// * free of runtime errors, because every value is a number. The only
///   `error` calls run directly inside a `pcall`.
/// * terminating, because loops are bounded by literals or by fixed counters,
///   calls follow function levels (see [`Signature::level`]) and recursion
///   burns literal fuel.
/// * deterministic, because nothing depends on addresses, time or `pairs`
///   order. See [`Pure`].
/// * observable, because it prints values along the way and every top-level
///   number at the end.
pub struct Generator {
    dice: Dice,
    config: Config,
    scopes: Scopes,
    bodies: Vec<Body>,
    pure: Option<Pure>,
    helpers: Helpers,
    budget: i64,
    /// Nested generation stops once `budget` drops to this.
    budget_floor: i64,
    block_depth: u32,
}

impl Generator {
    pub fn new(seed: u64, config: Config) -> Self {
        let budget = i64::from(config.max_stmts);
        Self {
            dice: Dice::new(seed),
            config,
            scopes: Scopes::default(),
            bodies: Vec::new(),
            pure: None,
            helpers: Helpers::default(),
            budget,
            budget_floor: 0,
            block_depth: 0,
        }
    }

    pub fn program(mut self) -> Block {
        self.bodies.push(Body {
            returns: None,
            variadic: true,
            call_level: MAIN_LEVEL,
            can_error: false,
            locals: 0,
            loops: Vec::new(),
        });
        self.scopes.push(true);

        let mut stmts = self.prelude();
        while self.budget > 0 {
            let generated = self.stmt();
            stmts.extend(generated);
        }
        stmts.extend(self.epilogue());
        Block::with_stmts(stmts)
    }

    fn body(&self) -> &Body {
        self.bodies.last().expect("a function body is open")
    }

    fn body_mut(&mut self) -> &mut Body {
        self.bodies.last_mut().expect("a function body is open")
    }

    /// Builds expressions for the current point in the program.
    fn exprs(&mut self) -> Exprs<'_> {
        let body = self.bodies.last().expect("a function body is open");
        Exprs::new(
            &mut self.dice,
            &self.scopes,
            &self.config,
            body.call_level,
            body.variadic,
            self.pure.is_none(),
        )
    }

    /// A number expression of random depth.
    fn number(&mut self) -> Expr {
        let mut exprs = self.exprs();
        let d = exprs.depth();
        exprs.number(d)
    }

    /// A branch condition of random depth.
    fn condition(&mut self) -> Expr {
        let mut exprs = self.exprs();
        let d = exprs.depth();
        exprs.condition(d)
    }

    /// Expressions for at least `count` values, of random depth.
    fn list(&mut self, count: u32) -> Vec<Expr> {
        let mut exprs = self.exprs();
        let d = exprs.depth();
        exprs.list(count, d)
    }

    fn fresh(&mut self, prefix: &'static str) -> Name {
        self.scopes.fresh(prefix)
    }

    fn declare(&mut self, name: Name, kind: Kind) {
        self.body_mut().locals += 1;
        self.scopes.declare(name, kind);
    }

    fn pop_scope(&mut self) {
        let declared = self.scopes.pop();
        let body = self.body_mut();
        body.locals = body.locals.saturating_sub(declared);
    }

    fn can_declare(&self, count: usize) -> bool {
        self.body().locals + count <= MAX_LOCALS
    }

    fn fn_depth(&self) -> u32 {
        self.bodies.len() as u32 - 1
    }

    /// A level for a function created here that this body can still call.
    fn callable_level(&mut self) -> u32 {
        let bound = self.body().call_level.min(MAX_LEVEL + 1);
        if bound <= 1 {
            1
        } else {
            self.dice.range(1..=bound - 1)
        }
    }

    fn random_signature(&mut self, level: u32) -> Signature {
        Signature {
            params: self.dice.range(0..=2),
            variadic: self.dice.chance(0.15),
            returns: self.dice.weighted(&[2, 6, 2, 1]) as u32,
            level,
            fuel: false,
        }
    }

    /// Defines iterator helpers that `for ... in` loops use.
    fn prelude(&mut self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        let (i, n, limit) = (Expr::named("i"), Expr::named("n"), Expr::named("limit"));
        if self.config.weights.iterator_for > 0 && self.dice.chance(0.5) {
            // local function stepper(limit, i)
            //     if i < limit then return i + 1 end
            //     return nil
            // end
            let name = self.fresh("stepper");
            stmts.push(Stmt::LocalFunction {
                name: name.ident(),
                params: vec![param("limit".into()), param("i".into())],
                body: Block::with_stmts(vec![
                    if_then(
                        Expr::binary(i.clone(), BinOp::Lt, limit),
                        vec![Stmt::Return {
                            values: vec![Expr::binary(i.clone(), BinOp::Add, Expr::float(1.0))],
                        }],
                    ),
                    Stmt::Return {
                        values: vec![Expr::nil()],
                    },
                ]),
            });
            self.helpers.stepper = Some(name);
        }
        if self.config.weights.iterator_for > 0 && self.dice.chance(0.5) {
            // local function counter(n)
            //     local i = 0
            //     return function()
            //         i += 1
            //         if i <= n then return i, i * i end
            //         return nil
            //     end
            // end
            let name = self.fresh("counter");
            let iterator = Expr::AnonymousFunction {
                params: Vec::new(),
                body: Block::with_stmts(vec![
                    increment(i.clone()),
                    if_then(
                        Expr::binary(i.clone(), BinOp::Lte, n),
                        vec![Stmt::Return {
                            values: vec![i.clone(), Expr::binary(i.clone(), BinOp::Mul, i)],
                        }],
                    ),
                    Stmt::Return {
                        values: vec![Expr::nil()],
                    },
                ]),
            };
            stmts.push(Stmt::LocalFunction {
                name: name.ident(),
                params: vec![param("n".into())],
                body: Block::with_stmts(vec![
                    local(vec!["i".into()], vec![Expr::float(0.0)]),
                    Stmt::Return {
                        values: vec![iterator],
                    },
                ]),
            });
            self.helpers.counter = Some(name);
        }
        stmts
    }

    /// Prints every visible top-level number, so the final state is part of
    /// the output.
    fn epilogue(&mut self) -> Vec<Stmt> {
        let names: Vec<Expr> = self
            .scopes
            .numbers()
            .map(|id| self.scopes.name(id).expr())
            .collect();
        names.chunks(6).map(|chunk| print(chunk.to_vec())).collect()
    }

    fn block_len(&mut self) -> u32 {
        let max = self
            .config
            .max_block_len
            .saturating_sub(self.block_depth / 2)
            .max(1);
        self.dice.range(1..=max)
    }

    fn block(&mut self, options: BlockOptions) -> Block {
        self.block_depth += 1;
        self.scopes.push(options.shadowing);
        for (name, kind) in options.bindings {
            self.declare(name, kind);
        }
        let mut stmts = options.head;
        for _ in 0..options.len {
            if self.budget <= self.budget_floor {
                break;
            }
            let generated = self.stmt();
            stmts.extend(generated);
        }
        match options.tail {
            Tail::None => {}
            Tail::Return => {
                let count = self.body().returns.unwrap_or(0);
                let values = self.list(count);
                stmts.push(Stmt::Return { values });
            }
            Tail::Assign(names) => {
                for name in names {
                    let value = self.number();
                    stmts.push(Stmt::Assignment {
                        lhs: vec![name.expr()],
                        rhs: vec![value],
                    });
                }
            }
        }
        // Print the block's own locals before they go out of scope.
        if self.pure.is_none() && !ends_in_terminator(&stmts) && self.dice.chance(0.35) {
            let locals: Vec<Expr> = self
                .scopes
                .innermost_numbers()
                .take(4)
                .map(|id| self.scopes.name(id).expr())
                .collect();
            if !locals.is_empty() {
                stmts.push(print(locals));
            }
        }
        if !ends_in_terminator(&stmts)
            && self.dice.chance(options.terminate)
            && let Some(terminator) = self.terminator()
        {
            stmts.push(terminator);
        }
        self.pop_scope();
        self.block_depth -= 1;
        Block::with_stmts(stmts)
    }

    fn sub_block(&mut self, terminate: f64) -> Block {
        let len = self.block_len();
        self.block(BlockOptions {
            len,
            terminate,
            ..BlockOptions::default()
        })
    }

    /// A statement that must end its block, if one is legal here.
    fn terminator(&mut self) -> Option<Stmt> {
        let pure = self.pure.is_some();
        let body = self.body();
        let in_loop = !body.loops.is_empty();
        let breakable = body.loops.last().is_some_and(|l| l.breakable);
        let returns = body.returns;
        let can_error = body.can_error;
        // A `return` in the main chunk ends the program and skips the final
        // dump, so it stays rare.
        let main_return =
            returns.is_none() && !pure && self.block_depth > 1 && self.dice.chance(0.1);
        let weights = [
            if in_loop && breakable && !pure { 4 } else { 0 },
            if in_loop { 4 } else { 0 },
            if returns.is_some() && !pure { 3 } else { 0 },
            u32::from(main_return),
            if can_error && !pure { 3 } else { 0 },
        ];
        if weights.iter().all(|&w| w == 0) {
            return None;
        }
        Some(match self.dice.weighted(&weights) {
            0 => Stmt::Break,
            1 => Stmt::Continue,
            2 => {
                let values = self.list(returns.unwrap_or(0));
                Stmt::Return { values }
            }
            3 => Stmt::Return { values: Vec::new() },
            _ => {
                let message = self.fresh("e").to_string();
                Stmt::Expression {
                    expr: Expr::call(
                        Expr::named("error"),
                        vec![Expr::string(message), Expr::float(0.0)],
                    ),
                }
            }
        })
    }

    /// Generates one statement, or a few that belong together, such as a
    /// counter local and its loop.
    fn stmt(&mut self) -> Vec<Stmt> {
        // Each statement and everything nested in it may only spend a share
        // of the budget. The share shrinks with depth, so one early statement
        // cannot take the whole program.
        let saved_floor = self.budget_floor;
        let share = (f64::from(self.config.max_stmts) * 0.2 * 0.4f64.powi(self.block_depth as i32))
            .max(2.0);
        self.budget_floor = saved_floor.max(self.budget - share as i64);
        let out = self.pick_stmt();
        self.budget_floor = saved_floor;
        out
    }

    fn pick_stmt(&mut self) -> Vec<Stmt> {
        self.budget -= 1;
        let w = &self.config.weights;
        let body = self.body();
        let pure = self.pure.is_some();
        let nest = self.block_depth < self.config.max_block_depth && self.budget > 2;
        let fns = nest && !pure && self.fn_depth() < self.config.max_fn_depth;
        let locals = self.can_declare(3);
        let guards =
            !body.loops.is_empty() || (!pure && (body.returns.is_some() || body.can_error));
        let on = |enabled: bool, weight: u32| if enabled { weight } else { 0 };
        let table = [
            (Shape::Local, on(locals, w.local)),
            (Shape::Assign, w.assign),
            (Shape::MultiAssign, w.multi_assign),
            (Shape::CompoundAssign, w.compound_assign),
            (Shape::Print, on(!pure, w.print)),
            (Shape::Call, on(!pure, w.call)),
            (Shape::If, on(nest, w.if_stmt)),
            (Shape::Guard, on(nest && guards, w.guard)),
            (Shape::NumericFor, on(nest, w.numeric_for)),
            (Shape::While, on(nest && locals, w.while_loop)),
            (Shape::Repeat, on(nest && locals, w.repeat_loop)),
            (Shape::Ipairs, on(nest && locals, w.ipairs_for)),
            (Shape::Pairs, on(nest && locals, w.pairs_for)),
            (Shape::IteratorFor, on(nest, w.iterator_for)),
            (Shape::Do, on(nest, w.do_block)),
            (Shape::LocalFunction, on(fns && locals, w.local_function)),
            (Shape::DeferredInit, on(nest && locals, w.deferred_init)),
            (Shape::Closures, on(fns && locals, w.closures)),
            (Shape::Pcall, on(fns && locals, w.pcall)),
            (Shape::Recursion, on(fns && locals, w.recursion)),
            (Shape::Accumulate, on(pure, ACCUMULATE_WEIGHT)),
        ];
        let weights = table.map(|(_, weight)| weight);
        if weights.iter().all(|&w| w == 0) {
            return self.fallback_stmt();
        }
        let generated = match table[self.dice.weighted(&weights)].0 {
            Shape::Local => Some(vec![self.local_stmt()]),
            Shape::Assign => self.assign_stmt(),
            Shape::MultiAssign => self.multi_assign_stmt(),
            Shape::CompoundAssign => self.compound_assign_stmt(),
            Shape::Print => Some(vec![self.print_stmt()]),
            Shape::Call => self.call_stmt(),
            Shape::If => Some(vec![self.if_stmt()]),
            Shape::Guard => Some(vec![self.guard_stmt()]),
            Shape::NumericFor => Some(vec![self.numeric_for()]),
            Shape::While => Some(self.while_loop()),
            Shape::Repeat => Some(self.repeat_loop()),
            Shape::Ipairs => Some(self.ipairs_for()),
            Shape::Pairs => Some(self.pairs_for()),
            Shape::IteratorFor => self.iterator_for(),
            Shape::Do => Some(vec![Stmt::Do {
                body: self.sub_block(0.05),
            }]),
            Shape::LocalFunction => Some(vec![self.local_function()]),
            Shape::DeferredInit => Some(self.deferred_init()),
            Shape::Closures => Some(self.closures()),
            Shape::Pcall => Some(self.pcall()),
            Shape::Recursion => Some(self.recursion()),
            Shape::Accumulate => Some(vec![self.accumulate()]),
        };
        generated.unwrap_or_else(|| self.fallback_stmt())
    }

    /// Used when the chosen shape has nothing to work with.
    fn fallback_stmt(&mut self) -> Vec<Stmt> {
        if self.pure.is_some() {
            return vec![self.accumulate()];
        }
        if self.can_declare(1) && self.dice.chance(0.6) {
            return vec![self.local_stmt()];
        }
        vec![self.print_stmt()]
    }

    /// Picks an assignable number. Inside a `pairs` body only locals of that
    /// body qualify.
    fn assignable(&mut self) -> Option<Name> {
        let floor = self.pure.map(|pure| pure.floor);
        let id = self.dice.choose(
            self.scopes
                .values()
                .filter(|&id| floor.is_none_or(|floor| id >= floor)),
        )?;
        Some(self.scopes.name(id))
    }

    /// `local a, b = ...`. Names are declared after the values, so the values
    /// still see any variable a new local hides.
    fn local_stmt(&mut self) -> Stmt {
        let count = self.dice.pick(&[1, 1, 1, 1, 2, 3]);
        let values = self.list(count);
        let mut names = Vec::with_capacity(count as usize);
        let mut shadowed = Vec::new();
        for _ in 0..count {
            let target = if self.scopes.allows_shadowing() && self.dice.chance(0.08) {
                self.dice.choose(self.scopes.values())
            } else {
                None
            };
            let name = match target {
                Some(target) if !shadowed.contains(&target) => {
                    shadowed.push(target);
                    self.body_mut().locals += 1;
                    self.scopes.shadow(target, Kind::Value);
                    self.scopes.name(target)
                }
                _ => {
                    let name = self.fresh("v");
                    self.declare(name, Kind::Value);
                    name
                }
            };
            names.push(name.ident());
        }
        local(names, values)
    }

    fn assign_stmt(&mut self) -> Option<Vec<Stmt>> {
        let target = self.assignable()?;
        let value = self.number();
        Some(vec![Stmt::Assignment {
            lhs: vec![target.expr()],
            rhs: vec![value],
        }])
    }

    /// `a, b = b, a` or `a, b = x, f()`.
    fn multi_assign_stmt(&mut self) -> Option<Vec<Stmt>> {
        let a = self.assignable()?;
        let b = self.assignable()?;
        if a == b {
            return None;
        }
        let rhs = if self.dice.chance(0.5) {
            vec![b.expr(), a.expr()]
        } else {
            self.list(2)
        };
        Some(vec![Stmt::Assignment {
            lhs: vec![a.expr(), b.expr()],
            rhs,
        }])
    }

    fn compound_assign_stmt(&mut self) -> Option<Vec<Stmt>> {
        let target = self.assignable()?;
        let op = self.dice.pick(&[
            CompoundBinOp::Add,
            CompoundBinOp::Add,
            CompoundBinOp::Sub,
            CompoundBinOp::Mul,
            CompoundBinOp::Div,
            CompoundBinOp::IDiv,
            CompoundBinOp::Mod,
            CompoundBinOp::Pow,
        ]);
        let rhs = self.number();
        Some(vec![Stmt::CompoundAssignment {
            lhs: target.expr(),
            op,
            rhs,
        }])
    }

    fn print_stmt(&mut self) -> Stmt {
        let count = self.dice.range(1..=3);
        let trailing_call = self.dice.chance(0.2);
        let vararg = self.body().variadic && self.dice.chance(0.1);
        let mut exprs = self.exprs();
        let d = exprs.depth();
        let mut args: Vec<Expr> = (0..count).map(|_| exprs.number(d)).collect();
        // A trailing call prints every value it returns.
        if trailing_call && let Some(callee) = exprs.callee(1) {
            args.push(exprs.call(callee, d));
        } else if vararg {
            args.push(Expr::Vararg);
        }
        print(args)
    }

    fn call_stmt(&mut self) -> Option<Vec<Stmt>> {
        let mut exprs = self.exprs();
        let callee = exprs.callee(0)?;
        let d = exprs.depth();
        Some(vec![Stmt::Expression {
            expr: exprs.call(callee, d),
        }])
    }

    fn if_stmt(&mut self) -> Stmt {
        let branches = self.dice.weighted(&[4, 3, 2, 1]) + 1;
        let has_else = self.dice.chance(0.5);
        Stmt::If(self.if_chain(branches, has_else, &Tail::None))
    }

    /// `if c1 then .. elseif c2 then .. [else ..] end` with `branches`
    /// conditions.
    fn if_chain(&mut self, branches: usize, has_else: bool, tail: &Tail) -> If {
        let condition = self.condition();
        let len = self.block_len();
        let then_body = self.block(BlockOptions {
            len,
            tail: tail.clone(),
            terminate: 0.15,
            ..BlockOptions::default()
        });
        let else_clause = if branches > 1 {
            Some(ElseClause::If(Box::new(self.if_chain(
                branches - 1,
                has_else,
                tail,
            ))))
        } else if has_else {
            let len = self.block_len();
            Some(ElseClause::Else(self.block(BlockOptions {
                len,
                tail: tail.clone(),
                terminate: 0.15,
                ..BlockOptions::default()
            })))
        } else {
            None
        };
        If {
            condition,
            then_body,
            else_clause,
        }
    }

    /// `if cond then break end` and friends, sometimes with work ahead of the
    /// terminator.
    fn guard_stmt(&mut self) -> Stmt {
        let condition = self.condition();
        let len = if self.dice.chance(0.6) {
            0
        } else {
            self.block_len()
        };
        let then_body = self.block(BlockOptions {
            len,
            terminate: 1.0,
            ..BlockOptions::default()
        });
        let else_clause = self
            .dice
            .chance(0.2)
            .then(|| ElseClause::Else(self.sub_block(0.3)));
        Stmt::If(If {
            condition,
            then_body,
            else_clause,
        })
    }

    fn loop_body(
        &mut self,
        head: Vec<Stmt>,
        bindings: Vec<(Name, Kind)>,
        breakable: bool,
        shadowing: bool,
    ) -> Block {
        self.body_mut().loops.push(Loop { breakable });
        let len = self.block_len();
        let body = self.block(BlockOptions {
            bindings,
            head,
            len,
            terminate: 0.1,
            shadowing,
            ..BlockOptions::default()
        });
        self.body_mut().loops.pop();
        body
    }

    fn numeric_for(&mut self) -> Stmt {
        let var = self.fresh("i");
        let (start, end, step) = match self.dice.weighted(&[5, 2, 2, 1]) {
            0 => {
                let start = self.dice.range(-2..=3);
                (
                    Expr::float(start as f64),
                    Expr::float((start + self.dice.range(-1..=6)) as f64),
                    None,
                )
            }
            1 => {
                let step = self.dice.pick(&[-1.0, -2.0, -0.5]);
                (
                    Expr::float(self.dice.range(4..=8) as f64),
                    Expr::float(self.dice.range(-2..=2) as f64),
                    Some(Expr::float(step)),
                )
            }
            2 => {
                // A bound that depends on data, clamped so the loop stays short.
                let bound = self.number();
                let end = library_call(
                    &["math", "min"],
                    vec![bound, Expr::float(self.dice.range(2..=8) as f64)],
                );
                let step = self.dice.pick(&[1.0, 2.0, 0.5, 1.5]);
                (
                    Expr::float(self.dice.range(0..=2) as f64),
                    end,
                    (step != 1.0).then(|| Expr::float(step)),
                )
            }
            _ => {
                let start = self.dice.pick(&[0.5, 0.25, 1.0, -1.5]);
                (
                    Expr::float(start),
                    Expr::float(start + f64::from(self.dice.range(1i32..=4))),
                    Some(Expr::float(self.dice.pick(&[0.5, 1.0, 0.75]))),
                )
            }
        };
        let body = self.loop_body(Vec::new(), vec![(var, Kind::Fixed)], true, true);
        Stmt::NumericFor {
            var: var.ident(),
            start,
            end,
            step,
            body,
        }
    }

    /// A fresh fixed counter, its `local c = 0`, and a literal bound.
    fn counter(&mut self) -> (Name, Stmt, Expr) {
        let name = self.fresh("c");
        let decl = local(vec![name.ident()], vec![Expr::float(0.0)]);
        self.declare(name, Kind::Fixed);
        let limit = Expr::float(self.dice.range(1..=5) as f64);
        (name, decl, limit)
    }

    fn while_loop(&mut self) -> Vec<Stmt> {
        let (c, decl, limit) = self.counter();
        let stmt = match self.dice.weighted(&[3, 3, 2]) {
            // while c < N do c += 1 ... end
            0 => Stmt::While {
                condition: Expr::binary(c.expr(), BinOp::Lt, limit),
                body: self.loop_body(vec![increment(c.expr())], Vec::new(), true, true),
            },
            // while c < N and cond do c += 1 ... end
            1 => {
                let extra = self.condition();
                Stmt::While {
                    condition: Expr::binary(
                        Expr::binary(c.expr(), BinOp::Lt, limit),
                        BinOp::And,
                        extra,
                    ),
                    body: self.loop_body(vec![increment(c.expr())], Vec::new(), true, true),
                }
            }
            // while true do c += 1 if c > N then break end ... end
            _ => {
                let head = vec![
                    increment(c.expr()),
                    if_then(Expr::binary(c.expr(), BinOp::Gt, limit), vec![Stmt::Break]),
                ];
                Stmt::While {
                    condition: Expr::boolean(true),
                    body: self.loop_body(head, Vec::new(), true, true),
                }
            }
        };
        vec![decl, stmt]
    }

    fn repeat_loop(&mut self) -> Vec<Stmt> {
        let (c, decl, limit) = self.counter();
        let body = self.loop_body(vec![increment(c.expr())], Vec::new(), true, false);
        // The condition only reads bindings from outside the body. That keeps
        // `continue` legal, which Luau forbids when `until` reads a body local.
        let exit = Expr::binary(c.expr(), BinOp::Gte, limit);
        let condition = if self.dice.chance(0.4) {
            let extra = self.condition();
            Expr::binary(exit, BinOp::Or, extra)
        } else {
            exit
        };
        vec![decl, Stmt::RepeatUntil { condition, body }]
    }

    /// `for k, e in ipairs({...})`, sometimes through a local table.
    fn ipairs_for(&mut self) -> Vec<Stmt> {
        let mut out = Vec::new();
        let source = {
            let mut exprs = self.exprs();
            let d = exprs.depth();
            exprs.array(d)
        };
        let source = if self.dice.chance(0.5) {
            let table = self.fresh("t");
            out.push(local(vec![table.ident()], vec![source]));
            self.declare(table, Kind::Opaque);
            table.expr()
        } else {
            source
        };
        let (k, e) = (self.fresh("k"), self.fresh("e"));
        let mut bindings = vec![(k, Kind::Fixed)];
        if self.dice.chance(0.8) {
            bindings.push((e, Kind::Fixed));
        }
        let vars = bindings.iter().map(|(name, _)| name.ident()).collect();
        let body = self.loop_body(Vec::new(), bindings, true, true);
        out.push(Stmt::GenericFor {
            vars,
            exprs: vec![Expr::call(Expr::named("ipairs"), vec![source])],
            body,
        });
        out
    }

    /// A `pairs` loop or generalized iteration over a table constructor.
    ///
    /// The body follows the [`Pure`] rules and feeds two accumulators, which
    /// become ordinary locals after the loop.
    fn pairs_for(&mut self) -> Vec<Stmt> {
        let record = self.dice.chance(0.4);
        let table = {
            let mut exprs = self.exprs();
            let d = exprs.depth();
            if record {
                exprs.record(d)
            } else {
                exprs.array(d)
            }
        };
        let (count, flag) = (self.fresh("n"), self.fresh("f"));
        let mut out = vec![
            local(vec![count.ident()], vec![Expr::float(0.0)]),
            local(vec![flag.ident()], vec![Expr::float(0.0)]),
        ];
        let exprs = if self.dice.chance(0.6) {
            vec![Expr::call(Expr::named("pairs"), vec![table])]
        } else {
            vec![table]
        };
        let (k, e) = (self.fresh("k"), self.fresh("e"));
        // Record keys are strings, which number expressions must not read.
        let key = if record { Kind::Opaque } else { Kind::Fixed };

        let saved = self.pure.replace(Pure {
            floor: self.scopes.next_id(),
            count,
            flag,
        });
        // The head counts every iteration.
        let head = vec![self.accumulate()];
        let body = self.loop_body(head, vec![(k, key), (e, Kind::Fixed)], false, true);
        self.pure = saved;

        self.declare(count, Kind::Value);
        self.declare(flag, Kind::Value);
        out.push(Stmt::GenericFor {
            vars: vec![k.ident(), e.ident()],
            exprs,
            body,
        });
        if self.pure.is_none() {
            out.push(print(vec![count.expr(), flag.expr()]));
        }
        out
    }

    /// An update of the innermost `pairs` accumulators that does not depend on
    /// iteration order.
    fn accumulate(&mut self) -> Stmt {
        let pure = self.pure.expect("accumulators exist inside a pairs body");
        match self.dice.range(0..=2) {
            0 => increment(pure.count.expr()),
            1 => {
                let condition = self.condition();
                if_then(condition, vec![increment(pure.count.expr())])
            }
            _ => {
                let condition = self.condition();
                if_then(
                    condition,
                    vec![Stmt::Assignment {
                        lhs: vec![pure.flag.expr()],
                        rhs: vec![Expr::float(1.0)],
                    }],
                )
            }
        }
    }

    /// `for i in stepper, N, 0` or `for a, b in counter(N)` over the prelude
    /// helpers.
    fn iterator_for(&mut self) -> Option<Vec<Stmt>> {
        let helpers = [
            self.helpers.stepper.map(|name| (name, true)),
            self.helpers.counter.map(|name| (name, false)),
        ];
        let (helper, stateless) = self.dice.choose(helpers.into_iter().flatten())?;
        let a = self.fresh("i");
        if stateless {
            let limit = self.dice.range(0..=5);
            let start = self.dice.range(-1..=limit);
            let body = self.loop_body(Vec::new(), vec![(a, Kind::Fixed)], true, true);
            Some(vec![Stmt::GenericFor {
                vars: vec![a.ident()],
                exprs: vec![
                    helper.expr(),
                    Expr::float(limit as f64),
                    Expr::float(start as f64),
                ],
                body,
            }])
        } else {
            let b = self.fresh("j");
            let limit = self.dice.range(0..=4);
            let body = self.loop_body(
                Vec::new(),
                vec![(a, Kind::Fixed), (b, Kind::Fixed)],
                true,
                true,
            );
            Some(vec![Stmt::GenericFor {
                vars: vec![a.ident(), b.ident()],
                exprs: vec![Expr::call(helper.expr(), vec![Expr::float(limit as f64)])],
                body,
            }])
        }
    }

    fn local_function(&mut self) -> Stmt {
        let level = self.callable_level();
        let signature = self.random_signature(level);
        let name = self.fresh("f");
        let params = (0..signature.params)
            .map(|_| (self.fresh("p"), Kind::Value))
            .collect();
        let (params, body) = self.function_body(signature, params, false);
        // Declared after the body, so the body cannot call itself.
        self.declare(name, Kind::Function(signature));
        Stmt::LocalFunction {
            name: name.ident(),
            params,
            body,
        }
    }

    /// Generates the parameters and body of a function in a new [`Body`].
    fn function_body(
        &mut self,
        signature: Signature,
        params: Vec<(Name, Kind)>,
        can_error: bool,
    ) -> (Vec<Typed<Parameter>>, Block) {
        let mut out: Vec<Typed<Parameter>> =
            params.iter().map(|(name, _)| param(name.ident())).collect();
        if signature.variadic {
            out.push(Typed::untyped(Parameter::Vararg));
        }

        let saved_pure = self.pure.take();
        self.bodies.push(Body {
            returns: Some(signature.returns),
            variadic: signature.variadic,
            call_level: signature.level,
            can_error,
            locals: 0,
            loops: Vec::new(),
        });
        let len = if self.fn_depth() > self.config.max_fn_depth {
            0
        } else {
            self.block_len()
        };
        let tail = if signature.returns > 0 {
            Tail::Return
        } else {
            Tail::None
        };
        let body = self.block(BlockOptions {
            bindings: params,
            len,
            tail,
            ..BlockOptions::default()
        });
        self.bodies.pop();
        self.pure = saved_pure;
        (out, body)
    }

    /// `local x` followed by an `if` chain whose every branch assigns `x`.
    fn deferred_init(&mut self) -> Vec<Stmt> {
        let names: Vec<Name> = (0..self.dice.range(1..=2))
            .map(|_| self.fresh("v"))
            .collect();
        let decl = local(names.iter().map(|name| name.ident()).collect(), Vec::new());
        let branches = self.dice.range(1..=3);
        let chain = self.if_chain(branches, true, &Tail::Assign(names.clone()));
        for name in names {
            self.declare(name, Kind::Value);
        }
        vec![decl, Stmt::If(chain)]
    }

    /// Closures that capture a loop variable, collected into a table and
    /// called afterwards.
    ///
    /// ```lua
    /// local fns = {}
    /// for i = 1, N do
    ///     table.insert(fns, function() ... return i + ... end)
    /// end
    /// for k, f in ipairs(fns) do print(k, f()) end
    /// ```
    fn closures(&mut self) -> Vec<Stmt> {
        let signature = Signature {
            params: 0,
            variadic: false,
            returns: 1,
            level: self.callable_level(),
            fuel: false,
        };
        let fns = self.fresh("fns");
        let i = self.fresh("i");
        let decl = local(vec![fns.ident()], vec![Expr::Table { items: Vec::new() }]);

        self.block_depth += 1;
        self.scopes.push(true);
        self.declare(i, Kind::Fixed);
        let mut body = Vec::new();
        if self.can_declare(1) && self.dice.chance(0.5) {
            // A local per iteration, also captured.
            let v = self.fresh("v");
            let value = self.number();
            body.push(local(vec![v.ident()], vec![value]));
            self.declare(v, Kind::Value);
        }
        let (params, mut func_body) = self.function_body(signature, Vec::new(), false);
        // Make sure the loop variable is captured.
        if let Some(Stmt::Return { values }) = func_body.stmts.last_mut()
            && let Some(value) = values.first_mut()
        {
            *value = Expr::binary(i.expr(), BinOp::Add, value.clone());
        }
        body.push(Stmt::Expression {
            expr: library_call(
                &["table", "insert"],
                vec![
                    fns.expr(),
                    Expr::AnonymousFunction {
                        params,
                        body: func_body,
                    },
                ],
            ),
        });
        self.pop_scope();
        self.block_depth -= 1;

        let loop_stmt = Stmt::NumericFor {
            var: i.ident(),
            start: Expr::float(1.0),
            end: Expr::float(self.dice.range(1..=4) as f64),
            step: None,
            body: Block::with_stmts(body),
        };
        self.declare(fns, Kind::Opaque);

        let (k, f) = (self.fresh("k"), self.fresh("e"));
        let call_loop = Stmt::GenericFor {
            vars: vec![k.ident(), f.ident()],
            exprs: vec![Expr::call(Expr::named("ipairs"), vec![fns.expr()])],
            body: Block::with_stmts(vec![print(vec![
                k.expr(),
                Expr::call(f.expr(), Vec::new()),
            ])]),
        };
        vec![decl, loop_stmt, call_loop]
    }

    /// `local ok, r = pcall(function() ... error(...) ... end)`, then prints
    /// both results.
    fn pcall(&mut self) -> Vec<Stmt> {
        let signature = Signature {
            params: 0,
            variadic: false,
            returns: 1,
            level: self.callable_level(),
            fuel: false,
        };
        let (params, body) = self.function_body(signature, Vec::new(), true);
        let (ok, result) = (self.fresh("ok"), self.fresh("r"));
        let decl = local(
            vec![ok.ident(), result.ident()],
            vec![Expr::call(
                Expr::named("pcall"),
                vec![Expr::AnonymousFunction { params, body }],
            )],
        );
        self.declare(ok, Kind::Opaque);
        self.declare(result, Kind::Opaque);
        vec![decl, print(vec![ok.expr(), result.expr()])]
    }

    /// A function that calls itself with an explicit literal fuel parameter.
    ///
    /// ```lua
    /// local function rec(n, a)
    ///     if n <= 0 then return ... end
    ///     ...
    ///     return ... + rec(n - 1, ...)
    /// end
    /// print(rec(3, ...))
    /// ```
    fn recursion(&mut self) -> Vec<Stmt> {
        let level = self.callable_level();
        let signature = Signature {
            params: 2,
            variadic: false,
            returns: 1,
            level,
            fuel: true,
        };
        let name = self.fresh("rec");
        let (n, a) = (self.fresh("p"), self.fresh("p"));
        // Visible inside its own body, but the body's level stops generated
        // calls to it. Only the explicit calls below recurse.
        self.declare(name, Kind::Function(signature));

        let saved_pure = self.pure.take();
        self.bodies.push(Body {
            returns: Some(1),
            variadic: false,
            call_level: level,
            can_error: false,
            locals: 0,
            loops: Vec::new(),
        });
        self.scopes.push(true);
        self.declare(n, Kind::Fixed);
        self.declare(a, Kind::Value);

        let base_value = self.number();
        let base = if_then(
            Expr::binary(n.expr(), BinOp::Lte, Expr::float(0.0)),
            vec![Stmt::Return {
                values: vec![base_value],
            }],
        );
        // Locals of the middle get fresh names, so splicing it into the body
        // never hides a name the final `return` reads.
        let len = self.block_len();
        let middle = self.block(BlockOptions {
            len,
            shadowing: false,
            ..BlockOptions::default()
        });
        let recurse = |generator: &mut Self, decrement: f64| {
            let arg = generator.number();
            Expr::call(
                name.expr(),
                vec![
                    Expr::binary(n.expr(), BinOp::Sub, Expr::float(decrement)),
                    arg,
                ],
            )
        };
        let first = recurse(self, 1.0);
        let mut result = Expr::binary(self.number(), BinOp::Add, first);
        if self.dice.chance(0.3) {
            let second = recurse(self, 2.0);
            result = Expr::binary(result, BinOp::Add, second);
        }
        let mut stmts = vec![base];
        if self.dice.chance(0.5) {
            stmts.push(Stmt::Do { body: middle });
        } else {
            stmts.extend(middle.stmts);
        }
        stmts.push(Stmt::Return {
            values: vec![result],
        });

        self.pop_scope();
        self.bodies.pop();
        self.pure = saved_pure;

        let fuel = Expr::float(self.dice.range(0..=5) as f64);
        let arg = {
            let mut exprs = self.exprs();
            exprs.number(1)
        };
        vec![
            Stmt::LocalFunction {
                name: name.ident(),
                params: vec![param(n.ident()), param(a.ident())],
                body: Block::with_stmts(stmts),
            },
            print(vec![Expr::call(name.expr(), vec![fuel, arg])]),
        ]
    }
}
