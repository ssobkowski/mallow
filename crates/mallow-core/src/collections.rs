//! Hash collections using the Fx hasher, plus a bitset for dense integer keys.

use std::fmt;
use std::marker::PhantomData;

use id_arena::Id;
pub(crate) use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// A key that maps to a small dense integer.
pub(crate) trait Index: Copy {
    fn index(self) -> usize;
}

impl Index for usize {
    fn index(self) -> usize {
        self
    }
}

impl<K: Index> Index for &K {
    fn index(self) -> usize {
        (*self).index()
    }
}

impl<T> Index for Id<T> {
    fn index(self) -> usize {
        Id::index(&self)
    }
}

/// A set of integer-like keys backed by a growable bitset.
///
/// Iteration (available for `usize` keys) is in ascending order.
pub(crate) struct IndexSet<K> {
    words: Vec<u64>,
    _key: PhantomData<fn() -> K>,
}

impl<K> Clone for IndexSet<K> {
    fn clone(&self) -> Self {
        Self {
            words: self.words.clone(),
            _key: PhantomData,
        }
    }
}

impl<K> Default for IndexSet<K> {
    fn default() -> Self {
        Self {
            words: Vec::new(),
            _key: PhantomData,
        }
    }
}

impl<K> PartialEq for IndexSet<K> {
    fn eq(&self, other: &Self) -> bool {
        let (short, long) = if self.words.len() <= other.words.len() {
            (&self.words, &other.words)
        } else {
            (&other.words, &self.words)
        };
        short == &long[..short.len()] && long[short.len()..].iter().all(|&w| w == 0)
    }
}

impl<K> Eq for IndexSet<K> {}

impl<K: Index> IndexSet<K> {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Adds `key`, returning whether it was newly inserted.
    pub(crate) fn insert(&mut self, key: K) -> bool {
        let i = key.index();
        let (word, bit) = (i / 64, 1u64 << (i % 64));
        if word >= self.words.len() {
            self.words.resize(word + 1, 0);
        }
        let new = self.words[word] & bit == 0;
        self.words[word] |= bit;
        new
    }

    /// Removes `key`, returning whether it was present.
    pub(crate) fn remove(&mut self, key: impl Index) -> bool {
        let i = key.index();
        match self.words.get_mut(i / 64) {
            Some(word) => {
                let bit = 1u64 << (i % 64);
                let had = *word & bit != 0;
                *word &= !bit;
                had
            }
            None => false,
        }
    }

    pub(crate) fn contains(&self, key: impl Index) -> bool {
        let i = key.index();
        self.words
            .get(i / 64)
            .is_some_and(|word| word & (1u64 << (i % 64)) != 0)
    }

    pub(crate) fn len(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.words.iter().all(|&w| w == 0)
    }

    /// Returns the keys of `self` that are not in `other`.
    pub(crate) fn difference(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (a, b) in out.words.iter_mut().zip(&other.words) {
            *a &= !b;
        }
        out
    }
}

impl IndexSet<usize> {
    /// Iterates the keys in ascending order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.words.iter().enumerate().flat_map(|(w, &word)| {
            let mut word = word;
            std::iter::from_fn(move || {
                (word != 0).then(|| {
                    let bit = word.trailing_zeros() as usize;
                    word &= word - 1;
                    w * 64 + bit
                })
            })
        })
    }
}

impl<'a> IntoIterator for &'a IndexSet<usize> {
    type Item = usize;
    type IntoIter = Box<dyn Iterator<Item = usize> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
}

impl IntoIterator for IndexSet<usize> {
    type Item = usize;
    type IntoIter = std::vec::IntoIter<usize>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter().collect::<Vec<_>>().into_iter()
    }
}

impl<K: Index> Extend<K> for IndexSet<K> {
    fn extend<I: IntoIterator<Item = K>>(&mut self, iter: I) {
        for key in iter {
            self.insert(key);
        }
    }
}

impl<'a, K: Index + 'a> Extend<&'a K> for IndexSet<K> {
    fn extend<I: IntoIterator<Item = &'a K>>(&mut self, iter: I) {
        self.extend(iter.into_iter().copied());
    }
}

impl<K: Index> FromIterator<K> for IndexSet<K> {
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        let mut set = Self::new();
        set.extend(iter);
        set
    }
}

impl fmt::Debug for IndexSet<usize> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}
