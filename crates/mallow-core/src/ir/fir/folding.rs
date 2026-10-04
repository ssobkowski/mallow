//! Expression folding over FIR blocks.
//!
//! The Luau compiler evaluates every source expression into temporaries in
//! evaluation order, so the operands of one source expression are defined by a
//! contiguous run of instructions that ends right before their consumer. This
//! analysis walks each block backwards and folds a definition into its single
//! use when the definition is exactly the next instruction in that run. The
//! bytecode order of the folded instructions is then the post-order of the
//! tree, so folding never reorders evaluation and needs no effect analysis.
//!
//! Constants, and copies of values whose storage is assigned once, read nothing
//! that can change. They float to their single use regardless of position.
//!
//! A table constructor compiles to a new table followed by the statements
//! which initialize it. Each such run is treated as one constructor node, so
//! the whole table can fold into its use like any other expression.

use crate::collections::{HashMap, HashSet, IndexSet};

use smallvec::{SmallVec, smallvec};

use super::storage::{Storage, initializes_loop_variable};
use super::{BlockExit, Capture, Constant, Function, Instr, PackId, ValueId};
use crate::ir::graph::GraphView;
use crate::operator::BinOp;

/// Location of one instruction as its block and index.
pub(crate) type InstrRef = (usize, usize);

/// Values and packs whose definitions are folded into their single use.
#[derive(Debug, Default)]
pub(crate) struct Folding {
    /// Values materialized as an expression at their use.
    values: HashSet<ValueId>,
    /// Packs materialized as an expression at their use.
    packs: HashSet<PackId>,
    /// Ordered comparisons whose right operand was evaluated first.
    ///
    /// Luau compiles `a > b` as `b < a` while still evaluating `a` first, so
    /// these must be emitted with the mirrored operator to keep that order.
    mirrored: HashSet<ValueId>,
    /// Folded values whose definition floats to their use from any position.
    floating: HashSet<ValueId>,
    /// Initializing statements of every folded table constructor, in order.
    constructors: HashMap<ValueId, Vec<InstrRef>>,
    /// Statements materialized inside a folded table constructor.
    initializers: HashSet<InstrRef>,
    /// Blocks whose instructions are all folded into their branch condition.
    ///
    /// The structurer may emit such a block purely as part of a predicate,
    /// without a statement block of its own.
    condition_only_blocks: IndexSet<usize>,
}

impl Folding {
    /// Decides the folding of every reachable block of one function.
    pub(crate) fn build(function: &Function, storage: &Storage) -> Self {
        let facts = UseFacts::collect(function, storage);
        let mut folding = Self {
            floating: facts.floating.clone(),
            values: facts.floating.clone(),
            ..Self::default()
        };

        for block_id in function.cfg.nodes() {
            if function.cfg.is_reachable(block_id) {
                let block = BlockFolding::build(function, &facts, block_id);
                folding.merge(block);
            }
        }

        folding
    }

    /// Returns whether a value is materialized at its use instead of being bound.
    #[inline]
    pub(crate) fn is_folded(&self, value: ValueId) -> bool {
        self.values.contains(&value)
    }

    /// Returns whether a pack is materialized at its use instead of being bound.
    #[inline]
    pub(crate) fn is_pack_folded(&self, pack: PackId) -> bool {
        self.packs.contains(&pack)
    }

    /// Returns whether a folded value floats to its use from any position.
    #[inline]
    pub(crate) fn is_floating(&self, value: ValueId) -> bool {
        self.floating.contains(&value)
    }

    /// Returns whether an ordered comparison must be emitted with mirrored operands.
    #[inline]
    pub(crate) fn is_mirrored(&self, value: ValueId) -> bool {
        self.mirrored.contains(&value)
    }

    /// Returns the initializing statements of a folded table constructor.
    #[inline]
    pub(crate) fn constructor(&self, table: ValueId) -> Option<&[InstrRef]> {
        self.constructors.get(&table).map(Vec::as_slice)
    }

    /// Returns whether a statement is materialized inside a folded table constructor.
    #[inline]
    pub(crate) fn is_initializer(&self, instr: InstrRef) -> bool {
        self.initializers.contains(&instr)
    }

    /// Returns whether a block only computes its branch condition.
    #[inline]
    pub(crate) fn is_condition_only(&self, block: usize) -> bool {
        self.condition_only_blocks.contains(&block)
    }

    /// Returns all blocks which only compute their branch condition.
    #[inline]
    pub(crate) fn condition_only_blocks(&self) -> &IndexSet<usize> {
        &self.condition_only_blocks
    }

    /// Adds the trees of one block.
    fn merge(&mut self, block: BlockFolding) {
        self.values.extend(block.values);
        self.packs.extend(block.packs);
        self.mirrored.extend(block.mirrored);
        self.constructors.extend(block.constructors);
        self.initializers.extend(block.initializers);
        if block.is_condition_only {
            self.condition_only_blocks.insert(block.block);
        }
    }
}

/// Whether an operand is always evaluated by its consumer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Eval {
    /// The consumer always evaluates the operand.
    Eager,
    /// The consumer may skip the operand, as in the right side of `and`.
    Lazy,
}

/// One operand position of an instruction or block exit.
#[derive(Debug, Clone, Copy)]
enum Slot {
    /// A scalar operand.
    Value(ValueId, Eval),
    /// A pack operand.
    Pack(PackId),
}

impl Slot {
    /// Creates a new eagerly evaluated value slot.
    fn eager(value: ValueId) -> Self {
        Self::Value(value, Eval::Eager)
    }

    /// Creates a new lazily evaluated value slot.
    fn lazy(value: ValueId) -> Self {
        Self::Value(value, Eval::Lazy)
    }
}

/// Use facts shared by every block.
#[derive(Debug, Default)]
struct UseFacts {
    /// Number of uses of every value.
    value_uses: HashMap<ValueId, usize>,
    /// Number of uses of every pack.
    pack_uses: HashMap<PackId, usize>,
    /// Values which must stay bound to a local.
    pinned_values: HashSet<ValueId>,
    /// Packs which must stay bound to a pack local.
    pinned_packs: HashSet<PackId>,
    /// Values whose definition folds into their use from any position.
    floating: HashSet<ValueId>,
    /// Floating constants holding a string.
    string_constants: HashSet<ValueId>,
}

impl UseFacts {
    /// Collects use counts and pinned identities for one function.
    fn collect(function: &Function, storage: &Storage) -> Self {
        let mut facts = Self::default();

        for binding in &function.bindings {
            facts.pinned_values.extend(binding.values.iter().copied());
        }

        for block in function.cfg.items() {
            for instr in &block.instrs {
                for value in instr.used_values() {
                    *facts.value_uses.entry(value).or_default() += 1;
                }
                for pack in instr.used_packs() {
                    *facts.pack_uses.entry(pack).or_default() += 1;
                }
                match instr {
                    // Captured values are referenced by name from the closure.
                    Instr::Closure { captures, .. } => {
                        facts
                            .pinned_values
                            .extend(captures.iter().filter_map(|capture| match capture {
                                Capture::Copy(value) => Some(*value),
                                Capture::Share(_) => None,
                            }));
                    }
                    // Opened cells are backed by the local holding their initial value.
                    Instr::OpenCell { value, .. } => {
                        facts.pinned_values.insert(*value);
                    }
                    // Projections past the first one need a multiple binding.
                    Instr::Project { pack, index, .. } if *index != 0 => {
                        facts.pinned_packs.insert(*pack);
                    }
                    _ => {}
                }
            }

            for value in block.exit.used_values() {
                *facts.value_uses.entry(value).or_default() += 1;
            }
            if let BlockExit::Return(pack) = &block.exit {
                *facts.pack_uses.entry(*pack).or_default() += 1;
            }
            for edge in block.exit.edges() {
                let target = &function.cfg[edge.target];
                facts.pinned_values.extend(
                    edge.params
                        .iter()
                        .zip(&target.params)
                        .filter(|(_, parameter)| {
                            !initializes_loop_variable(&block.exit, edge.target, **parameter)
                        })
                        .map(|(argument, _)| *argument),
                );
            }
        }

        facts.string_constants = function
            .cfg
            .items()
            .flat_map(|block| block.instrs.iter())
            .filter_map(|instr| match instr {
                Instr::Const {
                    out,
                    value: Constant::String(_),
                } if facts.is_candidate(*out) => Some(*out),
                _ => None,
            })
            .collect();
        // A copy floats once its source is floating, so iterate to a fixpoint.
        let instrs: Vec<&Instr> = function
            .cfg
            .items()
            .flat_map(|block| block.instrs.iter())
            .collect();
        let mut instr_defined = HashSet::default();
        instr_defined.extend(instrs.iter().filter_map(|instr| instr.defined_value()));
        loop {
            let floating: HashSet<_> = instrs
                .iter()
                .filter(|instr| facts.is_floating(instr, storage, &instr_defined))
                .filter_map(|instr| instr.defined_value())
                .collect();
            if floating.len() == facts.floating.len() {
                break;
            }
            facts.floating = floating;
        }
        facts
    }

    /// Returns whether a value has exactly one use which may hold its expression.
    #[inline]
    fn is_candidate(&self, value: ValueId) -> bool {
        self.value_uses.get(&value) == Some(&1) && !self.pinned_values.contains(&value)
    }

    /// Returns whether a pack has exactly one use which may hold its expression.
    #[inline]
    fn is_pack_candidate(&self, pack: PackId) -> bool {
        self.pack_uses.get(&pack) == Some(&1) && !self.pinned_packs.contains(&pack)
    }

    /// Returns whether an instruction can be folded at any later point.
    ///
    /// Constants are always stable. A copy of a single assignment value is stable as
    /// well, unless the copied value is a positioned definition with no other
    /// use, in which case it may fold into the copy and the copy keeps its
    /// position.
    fn is_floating(
        &self,
        instr: &Instr,
        storage: &Storage,
        instr_defined: &HashSet<ValueId>,
    ) -> bool {
        match instr {
            Instr::Const { out, .. } => self.is_candidate(*out),
            Instr::Copy { out, value } => {
                self.is_candidate(*out)
                    && storage.is_single_assignment(*value)
                    && (!self.is_candidate(*value)
                        || !instr_defined.contains(value)
                        || self.floating.contains(value))
            }
            _ => false,
        }
    }
}

/// One positioned element of a block.
#[derive(Debug, Clone)]
enum Item<'f> {
    /// One instruction.
    Instr(usize, &'f Instr),
    /// A new table followed by the statements which initialize it.
    Constructor {
        /// Table defined by the constructor.
        table: ValueId,
        /// The table definition, its initializers and their operand trees.
        members: Vec<Item<'f>>,
    },
}

impl Item<'_> {
    /// Returns the value defined by this item.
    fn defined_value(&self) -> Option<ValueId> {
        match self {
            Self::Instr(_, instr) => instr.defined_value(),
            Self::Constructor { table, .. } => Some(*table),
        }
    }

    /// Returns the pack defined by this item.
    fn defined_pack(&self) -> Option<PackId> {
        match self {
            Self::Instr(_, instr) => instr.defined_pack(),
            Self::Constructor { .. } => None,
        }
    }
}

/// A table constructor found in one block, as a range of instruction indices.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ConstructorSpan {
    /// Table defined by the constructor.
    table: ValueId,
    /// Index of the table definition.
    start: usize,
    /// Index of the last initializer.
    end: usize,
    /// Number of initializing statements.
    initializers: usize,
    /// Length of the array part, if known.
    array_len: Option<usize>,
    /// Whether the last initializer ends the constructor with an open pack.
    closed: bool,
}

/// Expression trees of one block.
#[derive(Debug, Default)]
struct BlockFolding {
    /// Block owning these trees.
    block: usize,
    /// Values folded in this block.
    values: HashSet<ValueId>,
    /// Packs folded in this block.
    packs: HashSet<PackId>,
    /// Comparisons emitted with mirrored operands.
    mirrored: HashSet<ValueId>,
    /// Folded table constructors and their initializers.
    constructors: HashMap<ValueId, Vec<InstrRef>>,
    /// Statements materialized inside a folded constructor.
    initializers: HashSet<InstrRef>,
    /// Whether every instruction folds into the branch condition.
    is_condition_only: bool,
}

impl BlockFolding {
    /// Builds the trees of one block, collapsing table constructors until stable.
    fn build(function: &Function, facts: &UseFacts, block_id: usize) -> Self {
        let block = &function.cfg[block_id];

        // Floating instructions have no position in the evaluation order.
        let positioned: Vec<_> = block
            .instrs
            .iter()
            .enumerate()
            .filter(|(_, instr)| {
                !instr
                    .defined_value()
                    .is_some_and(|value| facts.floating.contains(&value))
            })
            .collect();

        // Every round can expose initializers which only became trees once inner
        // constructors were collapsed, so spans only grow until they are stable.
        let mut spans = Vec::new();
        let mut folding = loop {
            let span_refs: Vec<&ConstructorSpan> = spans.iter().collect();
            let items = group_constructors(&positioned, &span_refs, 0, positioned.len());
            let mut builder = TreeBuilder {
                facts,
                block: block_id,
                spans: &spans,
                folding: Self {
                    block: block_id,
                    ..Self::default()
                },
            };
            builder.walk(&items, &block.exit);
            let folding = builder.folding;

            if !folding.grow_constructor_spans(facts, &positioned, &items, &mut spans) {
                break folding;
            }
        };

        folding.is_condition_only = matches!(block.exit, BlockExit::Branch { .. })
            && block.instrs.iter().enumerate().all(|(index, instr)| {
                instr.defined_value().is_some_and(|value| {
                    facts.floating.contains(&value) || folding.values.contains(&value)
                }) || instr
                    .defined_pack()
                    .is_some_and(|pack| folding.packs.contains(&pack))
                    || folding.initializers.contains(&(block_id, index))
            });
        folding
    }

    /// Returns whether a top-level item remains a statement.
    fn is_root(&self, item: &Item<'_>) -> bool {
        match item {
            Item::Instr(_, instr) => {
                !instr
                    .defined_value()
                    .is_some_and(|value| self.values.contains(&value))
                    && !instr
                        .defined_pack()
                        .is_some_and(|pack| self.packs.contains(&pack))
            }
            Item::Constructor { table, .. } => !self.values.contains(table),
        }
    }

    /// Extends constructor spans with the statements which follow and only initialize them.
    ///
    /// Mirrors the constructor rules of the NIR table folding pass: array
    /// stores must continue the array part, and a store with a multiple value
    /// tail ends the constructor. Returns whether any span changed.
    fn grow_constructor_spans(
        &self,
        facts: &UseFacts,
        positioned: &[(usize, &Instr)],
        items: &[Item<'_>],
        spans: &mut Vec<ConstructorSpan>,
    ) -> bool {
        let roots: Vec<_> = items.iter().filter(|item| self.is_root(item)).collect();

        let mut changed = false;
        for (root_index, root) in roots.iter().enumerate() {
            let mut span = match root {
                Item::Instr(start, Instr::NewTable { out: table })
                    if !facts.pinned_values.contains(table) =>
                {
                    ConstructorSpan {
                        table: *table,
                        start: *start,
                        end: *start,
                        initializers: 0,
                        array_len: Some(0),
                        closed: false,
                    }
                }
                Item::Constructor { table, .. } => {
                    match spans.iter().find(|span| span.table == *table) {
                        Some(span) if !span.closed => span.clone(),
                        _ => continue,
                    }
                }
                _ => continue,
            };

            let table = span.table;
            let initializers = span.initializers;
            for root in &roots[root_index + 1..] {
                let Item::Instr(index, instr) = root else {
                    break;
                };
                match instr {
                    Instr::SetTable {
                        table: target,
                        key,
                        value,
                    } if *target == table && *key != table && *value != table => {
                        span.end = *index;
                        span.initializers += 1;
                    }
                    Instr::SetList {
                        table: target,
                        index: base,
                        values,
                    } if *target == table => {
                        let Some(len) = span.array_len else { break };
                        let contiguous = *base as usize == len + 1;
                        let (fixed_len, is_open) = self.pack_shape(positioned, *values);
                        if !contiguous && (is_open || fixed_len.is_none()) {
                            break;
                        }
                        if contiguous {
                            span.array_len = fixed_len.map(|fixed| len + fixed);
                        }
                        span.end = *index;
                        span.initializers += 1;
                        if is_open {
                            span.closed = true;
                            break;
                        }
                    }
                    _ => break,
                }
            }

            if span.initializers > initializers {
                changed = true;
                match spans.iter_mut().find(|existing| existing.table == table) {
                    Some(existing) => *existing = span,
                    None => spans.push(span),
                }
            }
        }
        changed
    }

    /// Returns the fixed length of a folded value pack and whether it has an open tail.
    fn pack_shape(&self, positioned: &[(usize, &Instr)], pack: PackId) -> (Option<usize>, bool) {
        if !self.packs.contains(&pack) {
            return (None, false);
        }
        positioned
            .iter()
            .find_map(|(_, instr)| match instr {
                Instr::MakePack { out, head, tail } if *out == pack => {
                    Some((tail.is_none().then_some(head.len()), tail.is_some()))
                }
                _ => None,
            })
            .unwrap_or((None, false))
    }
}

/// Collapses constructor spans between two positions into items.
fn group_constructors<'f>(
    positioned: &[(usize, &'f Instr)],
    spans: &[&ConstructorSpan],
    start: usize,
    end: usize,
) -> Vec<Item<'f>> {
    let mut items = Vec::new();
    let mut position = start;
    while position < end {
        let (index, instr) = positioned[position];
        let owner = spans
            .iter()
            .find(|span| span.start == index)
            .and_then(|span| {
                let last = positioned[position..end]
                    .iter()
                    .position(|(index, _)| *index == span.end)?;
                Some((*span, position + last + 1))
            });

        if let Some((span, span_end)) = owner {
            // Spans nest without overlapping, so inner spans lie inside the members.
            let inner: Vec<_> = spans
                .iter()
                .copied()
                .filter(|other| other.table != span.table)
                .collect();
            items.push(Item::Constructor {
                table: span.table,
                members: group_constructors(positioned, &inner, position, span_end),
            });
            position = span_end;
        } else {
            items.push(Item::Instr(index, instr));
            position += 1;
        }
    }
    items
}

/// Builds the expression trees of one block by folding operands off a stack.
struct TreeBuilder<'w> {
    /// Use facts for the function.
    facts: &'w UseFacts,
    /// Block being built.
    block: usize,
    /// Constructor spans collapsed for this build.
    spans: &'w [ConstructorSpan],
    /// Trees found so far.
    folding: BlockFolding,
}

impl TreeBuilder<'_> {
    /// Folds every expression tree of one sequence of items ending in a block exit.
    fn walk(&mut self, items: &[Item<'_>], exit: &BlockExit) {
        let mut stack = OperandStack::new(items);
        self.fold_operands(&mut stack, None, &exit_slots(exit));

        // Consume the rest as free roots.
        while let Some(item) = stack.pop() {
            match item {
                Item::Instr(_, instr) => {
                    self.fold_operands(&mut stack, Some(instr), &instr_slots(instr))
                }
                Item::Constructor { table, members } => self.fold_constructor(*table, members),
            }
        }
    }

    /// Folds the operand trees of every initializer inside one constructor.
    ///
    /// The initializers are the only statements between the table definition
    /// and the end of the constructor, so their trees never reach outside it.
    fn fold_constructor(&mut self, table: ValueId, members: &[Item<'_>]) {
        let mut stack = OperandStack::new(members);
        while let Some(item) = stack.pop() {
            match item {
                Item::Instr(_, instr) if instr.defined_value() == Some(table) => {}
                Item::Instr(_, instr) => {
                    let slots = initializer_slots(instr, table);
                    self.fold_operands(&mut stack, Some(instr), &slots);
                }
                Item::Constructor { table, members } => self.fold_constructor(*table, members),
            }
        }
    }

    /// Folds the operands of one node, popping their definitions off the stack.
    ///
    /// `node` is the consuming instruction, or `None` for a block exit.
    fn fold_operands(
        &mut self,
        stack: &mut OperandStack<'_, '_>,
        node: Option<&Instr>,
        slots: &[Slot],
    ) {
        if let Some(Instr::Binary {
            out,
            op: BinOp::Lt | BinOp::Lte,
            lhs,
            rhs,
        }) = node
            && !self.is_folded(*rhs)
            && !self.can_fold_top(stack, *rhs)
            && self.can_fold_top(stack, *lhs)
        {
            // `a > b` compiles to `lt b, a` with `a` evaluated first.
            let mirrored = [Slot::eager(*rhs), Slot::eager(*lhs)];
            self.fold_operands(stack, None, &mirrored);
            if self.is_folded(*rhs) {
                self.folding.mirrored.insert(*out);
            }
            return;
        }

        if let Some(Instr::Call { function, args, .. }) = node
            && self.can_fold_top_pack(stack, *args)
            && let Some(Item::Instr(_, pack @ Instr::MakePack { .. })) = stack.top(0)
            && stack
                .top(1)
                .is_some_and(|item| item.defined_value() == Some(*function))
            && self.is_candidate(*function)
            && self.is_import(stack, 1)
        {
            // Luau loads a builtin through its import after evaluating the
            // arguments of a fast call. Imports are pure, so the order is
            // unobservable and the call keeps its source shape.
            stack.pop();
            self.folding.packs.insert(*args);
            self.folding.values.insert(*function);
            self.fold_top(stack);
            self.fold_operands(stack, Some(pack), &instr_slots(pack));
            return;
        }

        for slot in slots.iter().rev() {
            match *slot {
                Slot::Value(value, eval) => {
                    if self.is_folded(value) {
                        continue;
                    }
                    if eval == Eval::Eager && self.can_fold_top(stack, value) {
                        self.folding.values.insert(value);
                        self.fold_top(stack);
                    }
                }
                Slot::Pack(pack) => {
                    if self.can_fold_top_pack(stack, pack) {
                        self.folding.packs.insert(pack);
                        self.fold_top(stack);
                    }
                }
            }
        }
    }

    /// Pops the top item and folds it into the node being built.
    fn fold_top(&mut self, stack: &mut OperandStack<'_, '_>) {
        let Some(item) = stack.pop() else {
            return;
        };
        match item {
            Item::Instr(_, instr) => self.fold_operands(stack, Some(instr), &instr_slots(instr)),
            Item::Constructor { table, members } => {
                let initializers: Vec<_> = constructor_initializers(members, *table)
                    .into_iter()
                    .map(|index| (self.block, index))
                    .collect();
                self.folding
                    .initializers
                    .extend(initializers.iter().copied());
                self.folding.constructors.insert(*table, initializers);
                self.fold_constructor(*table, members);
            }
        }
    }

    /// Returns whether the item `depth` below the top is a pure import chain.
    ///
    /// An import is a global read, optionally followed by reads of constant
    /// string fields, which Luau resolves once when the closure is created.
    fn is_import(&self, stack: &OperandStack<'_, '_>, depth: usize) -> bool {
        // TODO: Preserve imports in FIR and resolve them lazily, or mark the
        // resulting instructions as "import-originated"?
        match stack.top(depth) {
            Some(Item::Instr(_, Instr::GetGlobal { .. })) => true,
            Some(Item::Instr(_, Instr::GetTable { table, key, .. })) => {
                self.facts.string_constants.contains(key)
                    && self.facts.is_candidate(*table)
                    && stack
                        .top(depth + 1)
                        .is_some_and(|item| item.defined_value() == Some(*table))
                    && self.is_import(stack, depth + 1)
            }
            _ => false,
        }
    }

    /// Returns whether a value is folded, including floating values.
    fn is_folded(&self, value: ValueId) -> bool {
        self.facts.floating.contains(&value) || self.folding.values.contains(&value)
    }

    /// Returns whether a value has one use outside of its own constructor.
    fn is_candidate(&self, value: ValueId) -> bool {
        let internal = self
            .spans
            .iter()
            .find(|span| span.table == value)
            .map_or(0, |span| span.initializers);
        let uses = self.facts.value_uses.get(&value).copied();
        uses.and_then(|u| u.checked_sub(internal)) == Some(1)
            && !self.facts.pinned_values.contains(&value)
    }

    /// Returns whether the top item can fold into `value`'s use.
    fn can_fold_top(&self, stack: &OperandStack<'_, '_>, value: ValueId) -> bool {
        let Some(item) = stack.top(0) else {
            return false;
        };
        if item.defined_value() != Some(value) || !self.is_candidate(value) {
            return false;
        }

        // A projection is only an expression together with its pack.
        match item {
            Item::Instr(_, Instr::Project { pack, .. }) => {
                stack
                    .top(1)
                    .is_some_and(|item| item.defined_pack() == Some(*pack))
                    && self.facts.is_pack_candidate(*pack)
            }
            _ => true,
        }
    }

    /// Returns whether the top item can fold into `pack`'s use.
    fn can_fold_top_pack(&self, stack: &OperandStack<'_, '_>, pack: PackId) -> bool {
        stack
            .top(0)
            .is_some_and(|item| item.defined_pack() == Some(pack))
            && self.facts.is_pack_candidate(pack)
    }
}

/// Stack of the items not yet folded, with the latest one on top.
struct OperandStack<'a, 'f> {
    /// Items with a position in the evaluation order.
    items: &'a [Item<'f>],
    /// Number of items still on the stack.
    len: usize,
}

impl<'a, 'f> OperandStack<'a, 'f> {
    /// Creates a new stack holding every item.
    fn new(items: &'a [Item<'f>]) -> Self {
        Self {
            items,
            len: items.len(),
        }
    }

    /// Returns the item `depth` below the top.
    #[inline]
    fn top(&self, depth: usize) -> Option<&'a Item<'f>> {
        self.len
            .checked_sub(depth + 1)
            .map(|index| &self.items[index])
    }

    /// Removes and returns the top item.
    #[inline]
    fn pop(&mut self) -> Option<&'a Item<'f>> {
        let item = self.top(0)?;
        self.len -= 1;
        Some(item)
    }
}

/// Returns the block indices of a constructor's initializing statements in order.
fn constructor_initializers(members: &[Item<'_>], table: ValueId) -> Vec<usize> {
    members
        .iter()
        .filter_map(|member| match member {
            Item::Instr(index, Instr::SetTable { table: target, .. })
            | Item::Instr(index, Instr::SetList { table: target, .. })
                if *target == table =>
            {
                Some(*index)
            }
            _ => None,
        })
        .collect()
}

/// Returns the operands of an initializer other than the table it initializes.
fn initializer_slots(instr: &Instr, table: ValueId) -> SmallVec<[Slot; 3]> {
    match instr {
        Instr::SetTable {
            table: target,
            key,
            value,
        } if *target == table => smallvec![Slot::eager(*key), Slot::eager(*value),],
        Instr::SetList {
            table: target,
            values,
            ..
        } if *target == table => smallvec![Slot::Pack(*values)],
        _ => instr_slots(instr),
    }
}

/// Returns the operands of an instruction in evaluation order.
fn instr_slots(instr: &Instr) -> SmallVec<[Slot; 3]> {
    match instr {
        Instr::Const { .. }
        | Instr::GetGlobal { .. }
        | Instr::NewTable { .. }
        | Instr::VarArgs { .. }
        | Instr::LoadCell { .. }
        | Instr::Closure { .. }
        | Instr::OpenCell { .. } => SmallVec::new(),
        Instr::Copy { value, .. }
        | Instr::SetGlobal { value, .. }
        | Instr::Unary { value, .. }
        | Instr::StoreCell { value, .. } => smallvec![Slot::eager(*value)],
        Instr::GetTable { table, key, .. } => smallvec![Slot::eager(*table), Slot::eager(*key)],
        Instr::SetTable { table, key, value } => {
            smallvec![Slot::eager(*table), Slot::eager(*key), Slot::eager(*value)]
        }
        Instr::Binary { lhs, op, rhs, .. } => match op {
            BinOp::And | BinOp::Or => smallvec![Slot::eager(*lhs), Slot::lazy(*rhs)],
            _ => smallvec![Slot::eager(*lhs), Slot::eager(*rhs)],
        },
        Instr::Concat { operands, .. } => operands.iter().copied().map(Slot::eager).collect(),
        Instr::Select {
            condition,
            then_value,
            else_value,
            ..
        } => smallvec![
            Slot::eager(*condition),
            Slot::lazy(*then_value),
            Slot::lazy(*else_value),
        ],
        Instr::MakePack { head, tail, .. } => head
            .iter()
            .copied()
            .map(Slot::eager)
            .chain(tail.map(Slot::Pack))
            .collect(),
        Instr::Project { pack, .. } => smallvec![Slot::Pack(*pack)],
        Instr::Call { function, args, .. } => smallvec![Slot::eager(*function), Slot::Pack(*args)],
        Instr::MethodCall { object, args, .. } => {
            smallvec![Slot::eager(*object), Slot::Pack(*args)]
        }
        Instr::SetList { table, values, .. } => smallvec![Slot::eager(*table), Slot::Pack(*values)],
    }
}

/// Returns the operands of a block exit in evaluation order.
fn exit_slots(exit: &BlockExit) -> SmallVec<[Slot; 3]> {
    match exit {
        BlockExit::Branch { condition, .. } => smallvec![Slot::eager(*condition)],
        BlockExit::NumericFor {
            start, end, step, ..
        } => smallvec![Slot::eager(*start), Slot::eager(*end), Slot::eager(*step)],
        BlockExit::GenericFor { values, .. } => values.iter().copied().map(Slot::eager).collect(),
        BlockExit::Return(pack) => smallvec![Slot::Pack(*pack)],
        _ => SmallVec::new(),
    }
}
