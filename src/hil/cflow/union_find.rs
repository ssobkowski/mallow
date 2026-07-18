use std::{collections::HashMap, hash::Hash};

/// A structure that groups items into sets and merges them.
pub(crate) struct UnionFind<T> {
    /// Points each item to its parent.
    parent: HashMap<T, T>,
}

impl<T: Copy + Hash + Eq> UnionFind<T> {
    /// Makes a new empty set of items, each in its own group.
    pub fn new() -> Self {
        Self {
            parent: HashMap::new(),
        }
    }

    /// Finds the group leader for `item` and speeds up future lookups.
    #[must_use]
    pub fn find(&mut self, item: T) -> T {
        let p = *self.parent.entry(item).or_insert(item);
        if p == item {
            p
        } else {
            let root = self.find(p);
            self.parent.insert(item, root);
            root
        }
    }

    /// Joins two groups together, keeping `a`'s leader as the new leader.
    pub fn union(&mut self, a: T, b: T) {
        let root_a = self.find(a);
        let root_b = self.find(b);
        if root_a != root_b {
            self.parent.insert(root_b, root_a);
        }
    }
}
