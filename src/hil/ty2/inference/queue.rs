use std::{
    collections::{HashSet, VecDeque},
    hash::Hash,
};

/// Deduplicating FIFO work queue for inference variables.
#[derive(Debug)]
pub(super) struct WorkQueue<T> {
    /// Elements waiting to be processed.
    pending: VecDeque<T>,
    /// Membership set mirroring `pending`.
    members: HashSet<T>,
}

impl<T: Copy + Eq + Hash> WorkQueue<T> {
    /// Creates a new, empty work queue.
    pub fn new() -> Self {
        Self {
            pending: VecDeque::new(),
            members: HashSet::new(),
        }
    }

    /// Returns whether the queue contains the given element.
    pub fn contains(&self, x: T) -> bool {
        self.members.contains(&x)
    }

    /// Enqueues `variable` unless it is already pending.
    pub fn push(&mut self, variable: T) {
        if self.members.insert(variable) {
            self.pending.push_back(variable);
        }
    }

    /// Pops the next variable in FIFO order.
    pub fn pop(&mut self) -> Option<T> {
        let variable = self.pending.pop_front()?;
        self.members.remove(&variable);
        Some(variable)
    }
}
