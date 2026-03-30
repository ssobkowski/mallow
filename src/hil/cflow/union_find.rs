use std::{collections::HashMap, hash::Hash};

pub struct UnionFind<T> {
    parent: HashMap<T, T>,
}

impl<T: Copy + Hash + Eq> UnionFind<T> {
    pub fn new() -> Self {
        Self {
            parent: HashMap::new(),
        }
    }

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

    pub fn union(&mut self, a: T, b: T) {
        let root_a = self.find(a);
        let root_b = self.find(b);
        if root_a != root_b {
            self.parent.insert(root_b, root_a);
        }
    }
}
