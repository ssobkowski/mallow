//! The locals a generated program can see at the current point.

use std::fmt;

use mallow_core::ast::{Expr, Identifier};
use mallow_core::{Index, IndexSet};

/// A handle to one [`Binding`] in [`Scopes`].
///
/// Ids grow in declaration order. So an id compares below every id declared
/// after it, which [`Scopes::next_id`] uses to mark a point in time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BindingId(u32);

impl BindingId {
    fn from_index(index: usize) -> Self {
        Self(u32::try_from(index).expect("fewer than 2^32 bindings"))
    }
}

impl Index for BindingId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

/// The printed name of a local, such as `v12`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Name {
    prefix: &'static str,
    number: u32,
}

impl Name {
    pub fn ident(self) -> Identifier {
        Identifier::new(self.to_string())
    }

    pub fn expr(self) -> Expr {
        Expr::Named(self.ident())
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.prefix, self.number)
    }
}

/// The shape of a local function. A call site needs nothing else.
#[derive(Debug, Clone, Copy)]
pub struct Signature {
    /// Number of number parameters.
    pub params: u32,
    /// Accepts extra number arguments through `...`.
    pub variadic: bool,
    /// Number of values every `return` in the body produces.
    pub returns: u32,
    /// The termination argument.
    ///
    /// A body of level `L` only calls functions with a level below `L`. So
    /// every chain of calls is finite and every program halts. The main chunk
    /// has the highest level.
    pub level: u32,
    /// The first parameter is a recursion budget.
    ///
    /// The function calls itself with a smaller budget, and every other call
    /// site passes a small literal.
    pub fuel: bool,
}

/// What a binding holds and what generated code may do with it.
#[derive(Debug, Clone, Copy)]
pub enum Kind {
    /// A number that statements may read and assign.
    Value,
    /// A number that statements only read, such as a loop counter.
    Fixed,
    /// A local function.
    Function(Signature),
    /// A local that holds a table or a pcall result.
    ///
    /// Only the statement that declares it uses it. It still counts toward
    /// Luau's local limit.
    Opaque,
}

#[derive(Debug, Clone, Copy)]
struct Binding {
    name: Name,
    kind: Kind,
}

/// One lexical block.
#[derive(Debug, Default)]
struct Frame {
    declared: Vec<BindingId>,
    /// Bindings that a binding of this frame hid by reusing their name.
    shadowed: Vec<BindingId>,
    /// Locals declared here may reuse a visible name.
    shadowing: bool,
}

/// Every binding ever declared, plus which ones are visible right now.
///
/// Visibility lives in one dense set per [`Kind`]. Each set iterates in id
/// order, which is also declaration order.
#[derive(Debug, Default)]
pub struct Scopes {
    bindings: Vec<Binding>,
    values: IndexSet<BindingId>,
    fixed: IndexSet<BindingId>,
    functions: IndexSet<BindingId>,
    frames: Vec<Frame>,
    names: u32,
}

impl Scopes {
    /// Returns a name no other local uses.
    pub fn fresh(&mut self, prefix: &'static str) -> Name {
        self.names += 1;
        Name {
            prefix,
            number: self.names,
        }
    }

    /// Opens a block. With `shadowing` off, locals declared directly in it
    /// always get fresh names.
    ///
    /// `repeat` bodies need that. Their `until` condition is generated after
    /// the body but resolves names inside it, so a body local must never hide
    /// a name the condition reads.
    pub fn push(&mut self, shadowing: bool) {
        self.frames.push(Frame {
            shadowing,
            ..Frame::default()
        });
    }

    /// Closes the innermost block and returns how many locals it declared.
    pub fn pop(&mut self) -> usize {
        let frame = self.frames.pop().expect("a block is open");
        // A frame may hide its own earlier local. So restore hidden bindings
        // first, and then remove everything the frame declared.
        for &id in &frame.shadowed {
            self.show(id);
        }
        for &id in &frame.declared {
            self.hide(id);
        }
        frame.declared.len()
    }

    /// Declares a local in the innermost block.
    pub fn declare(&mut self, name: Name, kind: Kind) -> BindingId {
        let id = BindingId::from_index(self.bindings.len());
        self.bindings.push(Binding { name, kind });
        self.show(id);
        self.innermost_frame().declared.push(id);
        id
    }

    /// Declares a local that reuses the name of the visible binding `target`.
    ///
    /// `target` stays hidden until the innermost block closes.
    pub fn shadow(&mut self, target: BindingId, kind: Kind) -> BindingId {
        debug_assert!(self.allows_shadowing());
        self.hide(target);
        self.innermost_frame().shadowed.push(target);
        self.declare(self.name(target), kind)
    }

    pub fn allows_shadowing(&self) -> bool {
        self.frames.last().is_some_and(|frame| frame.shadowing)
    }

    /// Returns the id the next declared binding gets.
    pub fn next_id(&self) -> BindingId {
        BindingId::from_index(self.bindings.len())
    }

    pub fn name(&self, id: BindingId) -> Name {
        self.bindings[id.index()].name
    }

    pub fn signature(&self, id: BindingId) -> Signature {
        match self.bindings[id.index()].kind {
            Kind::Function(signature) => signature,
            kind => panic!("binding {id:?} is a {kind:?}, not a function"),
        }
    }

    /// Visible numbers that statements may assign.
    pub fn values(&self) -> impl Iterator<Item = BindingId> + '_ {
        self.values.iter().map(BindingId::from_index)
    }

    /// Visible numbers, both assignable and fixed.
    pub fn numbers(&self) -> impl Iterator<Item = BindingId> + '_ {
        self.values
            .iter()
            .chain(self.fixed.iter())
            .map(BindingId::from_index)
    }

    /// Visible local functions.
    pub fn functions(&self) -> impl Iterator<Item = BindingId> + '_ {
        self.functions.iter().map(BindingId::from_index)
    }

    /// Visible numbers declared directly in the innermost block, newest first.
    pub fn innermost_numbers(&self) -> impl Iterator<Item = BindingId> + '_ {
        let frame = self.frames.last().expect("a block is open");
        frame
            .declared
            .iter()
            .rev()
            .copied()
            .filter(|&id| self.values.contains(id) || self.fixed.contains(id))
    }

    fn innermost_frame(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("a block is open")
    }

    fn set_of(&mut self, id: BindingId) -> Option<&mut IndexSet<BindingId>> {
        match self.bindings[id.index()].kind {
            Kind::Value => Some(&mut self.values),
            Kind::Fixed => Some(&mut self.fixed),
            Kind::Function(_) => Some(&mut self.functions),
            Kind::Opaque => None,
        }
    }

    fn show(&mut self, id: BindingId) {
        if let Some(set) = self.set_of(id) {
            set.insert(id);
        }
    }

    fn hide(&mut self, id: BindingId) {
        if let Some(set) = self.set_of(id) {
            set.remove(id);
        }
    }
}
