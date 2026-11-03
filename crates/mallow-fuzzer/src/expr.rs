//! Expression generation.

use mallow_core::ast::{Expr, TableItem};
use mallow_core::operator::{BinOp, UnOp};

use crate::config::Config;
use crate::dice::Dice;
use crate::scope::{BindingId, Scopes, Signature};
use crate::syntax::library_call;

const ARITHMETIC: &[BinOp] = &[
    BinOp::Add,
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::Div,
    BinOp::IDiv,
    BinOp::Mod,
    BinOp::Pow,
];

const COMPARISONS: &[BinOp] = &[
    BinOp::Lt,
    BinOp::Lte,
    BinOp::Gt,
    BinOp::Gte,
    BinOp::Eq,
    BinOp::Ne,
];

/// Numbers that are interesting for constant folding and printing.
const SPECIAL_NUMBERS: &[f64] = &[
    1e300,
    9007199254740992.0,
    1e-7,
    0.1,
    -0.0,
    f64::NAN,
    f64::INFINITY,
    f64::NEG_INFINITY,
    1e16,
    123456.789,
    2147483648.0,
];

/// Field names for table constructors that `pairs` walks over.
const FIELD_NAMES: &[&str] = &["a", "b", "c", "x", "y", "n", "id", "value", "count"];

/// Builds expressions over the bindings visible at one point.
pub struct Exprs<'a> {
    dice: &'a mut Dice,
    scopes: &'a Scopes,
    /// Only functions with a level below this may be called.
    call_level: u32,
    /// `...` holds numbers here.
    variadic: bool,
    /// Calls are allowed. Bodies of `pairs` loops turn them off.
    calls: bool,
    max_depth: u32,
    /// Number of variable reads so far. [`Exprs::condition`] uses it to
    /// prefer conditions that read a variable.
    reads: u32,
}

impl<'a> Exprs<'a> {
    pub fn new(
        dice: &'a mut Dice,
        scopes: &'a Scopes,
        config: &Config,
        call_level: u32,
        variadic: bool,
        calls: bool,
    ) -> Self {
        Self {
            dice,
            scopes,
            call_level,
            variadic,
            calls,
            max_depth: config.max_expr_depth.max(1),
            reads: 0,
        }
    }

    /// Returns a random depth for a new top-level expression.
    pub fn depth(&mut self) -> u32 {
        self.dice.range(1..=self.max_depth)
    }

    /// Generates a number expression with nesting at most `d`.
    pub fn number(&mut self, d: u32) -> Expr {
        if d == 0 {
            return self.leaf();
        }
        let sub = d - 1;
        let callee = self.callee(1);
        let weights = [
            3,
            8,
            1,
            3,
            u32::from(self.variadic),
            if callee.is_some() { 4 } else { 0 },
            2,
            2,
            1,
        ];
        match self.dice.weighted(&weights) {
            0 => self.leaf(),
            1 => {
                let op = self.dice.pick(ARITHMETIC);
                let lhs = self.number(sub);
                let rhs = self.number(sub);
                Expr::binary(lhs, op, rhs)
            }
            2 => Expr::unary(UnOp::Minus, self.number(sub)),
            3 => self.math(sub),
            4 => {
                if self.dice.chance(0.5) {
                    Expr::call(Expr::named("select"), vec![Expr::string("#"), Expr::Vararg])
                } else {
                    // `...` may be empty, which reads as nil.
                    let fallback = self.number(sub.min(1));
                    Expr::binary(Expr::Vararg, BinOp::Or, fallback)
                }
            }
            5 => {
                let callee = callee.expect("weight is zero without a callee");
                let multi = self.scopes.signature(callee).returns > 1;
                let call = self.call(callee, sub);
                // A call with several results in the last slot of a list would
                // expand, so truncate it to one value explicitly.
                if multi || self.dice.chance(0.1) {
                    Expr::parenthesized(call)
                } else {
                    call
                }
            }
            6 => Expr::IfElse {
                condition: Box::new(self.boolean(sub)),
                then_expr: Box::new(self.number(sub)),
                else_expr: Box::new(self.number(sub)),
            },
            7 => {
                // Every number is truthy, so `c and a or b` always picks `a`
                // when `c` holds.
                let condition = self.boolean(sub);
                let a = self.number(sub);
                let b = self.number(sub);
                Expr::binary(Expr::binary(condition, BinOp::And, a), BinOp::Or, b)
            }
            _ => Expr::parenthesized(self.number(sub)),
        }
    }

    /// A variable or a literal.
    fn leaf(&mut self) -> Expr {
        if self.dice.chance(0.7)
            && let Some(id) = self.dice.choose(self.scopes.numbers())
        {
            self.reads += 1;
            return self.scopes.name(id).expr();
        }
        self.literal()
    }

    pub fn literal(&mut self) -> Expr {
        let value = match self.dice.weighted(&[8, 3, 3, 1]) {
            0 => self.dice.range(0..=9) as f64,
            1 => self.dice.range(11..=999) as f64,
            2 => self.dice.range(1..=39) as f64 / self.dice.pick(&[2.0, 4.0, 10.0]),
            _ => self.dice.pick(SPECIAL_NUMBERS),
        };
        Expr::float(if self.dice.chance(0.15) {
            -value
        } else {
            value
        })
    }

    /// A `math` library call. Every one of them accepts any number.
    fn math(&mut self, sub: u32) -> Expr {
        let (func, arity) = self.dice.pick(&[
            ("floor", 1),
            ("ceil", 1),
            ("abs", 1),
            ("max", 2),
            ("min", 2),
            ("sqrt", 1),
            ("sign", 1),
            ("clamp", 3),
        ]);
        if func == "clamp" {
            // `math.clamp` raises unless min <= max, so the bounds are ordered
            // literals.
            let lo = self.dice.range(-10..=4);
            let hi = lo + self.dice.range(0..=9);
            let x = self.number(sub);
            return library_call(
                &["math", "clamp"],
                vec![x, Expr::float(lo as f64), Expr::float(hi as f64)],
            );
        }
        let args = (0..arity).map(|_| self.number(sub)).collect();
        library_call(&["math", func], args)
    }

    /// Generates a boolean with nesting at most `d`.
    pub fn boolean(&mut self, d: u32) -> Expr {
        if d == 0 {
            return self.comparison(0);
        }
        let sub = d - 1;
        match self.dice.weighted(&[1, 8, 2, 3]) {
            0 => Expr::boolean(self.dice.chance(0.5)),
            1 => self.comparison(sub),
            2 => Expr::unary(UnOp::Not, self.boolean(sub)),
            _ => {
                let op = self.dice.pick(&[BinOp::And, BinOp::Or]);
                let lhs = self.boolean(sub);
                let rhs = self.boolean(sub);
                Expr::binary(lhs, op, rhs)
            }
        }
    }

    fn comparison(&mut self, d: u32) -> Expr {
        let op = self.dice.pick(COMPARISONS);
        let lhs = self.number(d);
        let rhs = self.number(d);
        Expr::binary(lhs, op, rhs)
    }

    /// A boolean for a branch condition.
    ///
    /// The compiler folds conditions over literals away, and mallow never sees
    /// the dead branch. So this retries a few times to get a condition that
    /// reads a variable.
    pub fn condition(&mut self, d: u32) -> Expr {
        let readable = self.scopes.numbers().next().is_some();
        let mut before = self.reads;
        let mut expr = self.boolean(d.max(1));
        for _ in 0..4 {
            if !readable || self.reads > before {
                break;
            }
            before = self.reads;
            expr = self.boolean(d.max(1));
        }
        expr
    }

    /// Returns a callable function with at least `min_returns` results.
    pub fn callee(&mut self, min_returns: u32) -> Option<BindingId> {
        if !self.calls {
            return None;
        }
        let (scopes, level) = (self.scopes, self.call_level);
        self.dice.choose(scopes.functions().filter(|&id| {
            let signature = scopes.signature(id);
            signature.level < level && signature.returns >= min_returns
        }))
    }

    pub fn call(&mut self, callee: BindingId, d: u32) -> Expr {
        let signature = self.scopes.signature(callee);
        let args = self.args(signature, d);
        Expr::call(self.scopes.name(callee).expr(), args)
    }

    fn args(&mut self, signature: Signature, d: u32) -> Vec<Expr> {
        let mut args = Vec::with_capacity(signature.params as usize);
        for i in 0..signature.params {
            let last = i + 1 == signature.params;
            if signature.fuel && i == 0 {
                args.push(Expr::float(self.dice.range(0..=5) as f64));
            } else if last
                && !signature.variadic
                && self.dice.chance(0.1)
                && let Some(callee) = self.callee(1)
            {
                // The last argument may expand to several values. Luau drops
                // the extra ones.
                args.push(self.call(callee, d));
            } else {
                args.push(self.number(d));
            }
        }
        if signature.variadic {
            if self.variadic && self.dice.chance(0.3) {
                args.push(Expr::Vararg);
            } else {
                for _ in 0..self.dice.range(0..=2) {
                    args.push(self.number(d));
                }
            }
        }
        args
    }

    /// Expressions producing at least `count` values.
    ///
    /// Sometimes a trailing call fills several of the last slots at once.
    pub fn list(&mut self, count: u32, d: u32) -> Vec<Expr> {
        if count == 0 {
            return Vec::new();
        }
        if self.dice.chance(0.3)
            && let Some(callee) = self.callee(1)
        {
            let returns = self.scopes.signature(callee).returns;
            let covered = self.dice.range(1..=returns.min(count));
            let mut out: Vec<_> = (0..count - covered).map(|_| self.number(d)).collect();
            out.push(self.call(callee, d));
            return out;
        }
        (0..count).map(|_| self.number(d)).collect()
    }

    /// `{a, b, c}`, sometimes with a trailing call or `...` that expands.
    pub fn array(&mut self, d: u32) -> Expr {
        let mut items: Vec<_> = (0..self.dice.range(0..=3))
            .map(|_| TableItem::Implicit {
                value: self.number(d),
            })
            .collect();
        if self.dice.chance(0.2) {
            if let Some(callee) = self.callee(1) {
                items.push(TableItem::Implicit {
                    value: self.call(callee, d),
                });
            } else if self.variadic {
                items.push(TableItem::Implicit {
                    value: Expr::Vararg,
                });
            }
        }
        Expr::Table { items }
    }

    /// `{a = 1, b = 2}` with distinct field names.
    pub fn record(&mut self, d: u32) -> Expr {
        let mut names = Vec::new();
        for _ in 0..self.dice.range(1..=3) {
            let name = self.dice.pick(FIELD_NAMES);
            if !names.contains(&name) {
                names.push(name);
            }
        }
        let items = names
            .into_iter()
            .map(|name| TableItem::Named {
                name: name.into(),
                value: self.number(d),
            })
            .collect();
        Expr::Table { items }
    }
}
