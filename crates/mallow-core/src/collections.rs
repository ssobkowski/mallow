//! Hash collections using the Fx hasher, plus a bitset for dense integer keys.

use std::marker::PhantomData;
use std::{fmt, iter::FusedIterator};

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

    /// Adds every key of `other`.
    pub(crate) fn union_with(&mut self, other: &Self) {
        if other.words.len() > self.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        for (a, b) in self.words.iter_mut().zip(&other.words) {
            *a |= b;
        }
    }

    /// Returns the keys of `self` that are not in `other`.
    pub(crate) fn difference(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (a, b) in out.words.iter_mut().zip(&other.words) {
            *a &= !b;
        }
        out
    }

    /// Returns an iterator over the set bits.
    pub(crate) fn iter(&self) -> IndexSetIter<'_> {
        IndexSetIter::new(&self.words)
    }
}

pub struct IndexSetIter<'a> {
    words: &'a [u64],
    idx: usize,
    cur: u64,
}

impl<'a> IndexSetIter<'a> {
    fn new(words: &'a [u64]) -> Self {
        Self {
            words,
            idx: 0,
            cur: words.first().copied().unwrap_or(0),
        }
    }
}

impl Iterator for IndexSetIter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while self.cur == 0 {
            self.idx += 1;
            self.cur = *self.words.get(self.idx)?;
        }
        let bit = self.cur.trailing_zeros() as usize;
        self.cur &= self.cur - 1;
        Some(self.idx * 64 + bit)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rest: usize = self
            .words
            .get(self.idx + 1..)
            .unwrap_or(&[])
            .iter()
            .map(|w| w.count_ones() as usize)
            .sum();
        let n = self.cur.count_ones() as usize + rest;
        (n, Some(n))
    }
}

impl ExactSizeIterator for IndexSetIter<'_> {}
impl FusedIterator for IndexSetIter<'_> {}

pub struct IndexSetIntoIter {
    words: Box<[u64]>,
    idx: usize,
    cur: u64,
}

impl Iterator for IndexSetIntoIter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while self.cur == 0 {
            self.idx += 1;
            self.cur = *self.words.get(self.idx)?;
        }
        let bit = self.cur.trailing_zeros() as usize;
        self.cur &= self.cur - 1;
        Some(self.idx * 64 + bit)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rest: usize = self
            .words
            .get(self.idx + 1..)
            .unwrap_or(&[])
            .iter()
            .map(|w| w.count_ones() as usize)
            .sum();
        let n = self.cur.count_ones() as usize + rest;
        (n, Some(n))
    }
}

impl FusedIterator for IndexSetIntoIter {}

impl<'a> IntoIterator for &'a IndexSet<usize> {
    type Item = usize;
    type IntoIter = IndexSetIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl IntoIterator for IndexSet<usize> {
    type Item = usize;
    type IntoIter = IndexSetIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        let words = self.words.into_boxed_slice();
        let cur = words.first().copied().unwrap_or(0);
        IndexSetIntoIter { words, idx: 0, cur }
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

impl<K: Index> fmt::Debug for IndexSet<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

/// A map from integer-like keys to values, stored in a vector indexed by key.
///
/// Intended for arena ids, whose indices are small and dense. Iteration is in
/// ascending key order.
pub(crate) struct IndexMap<K, V> {
    slots: Vec<Option<(K, V)>>,
    len: usize,
}

impl<K, V> Default for IndexMap<K, V> {
    fn default() -> Self {
        Self {
            slots: Vec::new(),
            len: 0,
        }
    }
}

impl<K: Clone, V: Clone> Clone for IndexMap<K, V> {
    fn clone(&self) -> Self {
        Self {
            slots: self.slots.clone(),
            len: self.len,
        }
    }
}

impl<K: Index + fmt::Debug, V: fmt::Debug> fmt::Debug for IndexMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Index, V> IndexMap<K, V> {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Creates an empty map with room for keys below `capacity`.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: Vec::with_capacity(capacity),
            len: 0,
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn slot_mut(&mut self, index: usize) -> &mut Option<(K, V)> {
        if index >= self.slots.len() {
            self.slots.resize_with(index + 1, || None);
        }
        &mut self.slots[index]
    }

    pub(crate) fn insert(&mut self, key: K, value: V) -> Option<V> {
        let slot = self.slot_mut(key.index());
        let old = slot.replace((key, value));
        if old.is_none() {
            self.len += 1;
        }
        old.map(|(_, value)| value)
    }

    pub(crate) fn get(&self, key: impl Index) -> Option<&V> {
        self.slots
            .get(key.index())?
            .as_ref()
            .map(|(_, value)| value)
    }

    pub(crate) fn contains_key(&self, key: impl Index) -> bool {
        self.get(key).is_some()
    }

    pub(crate) fn remove(&mut self, key: impl Index) -> Option<V> {
        let old = self.slots.get_mut(key.index())?.take();
        if old.is_some() {
            self.len -= 1;
        }
        old.map(|(_, value)| value)
    }

    pub(crate) fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        Entry { map: self, key }
    }

    pub(crate) fn iter(&self) -> IndexMapIter<'_, K, V> {
        IndexMapIter {
            slots: self.slots.iter(),
        }
    }

    pub(crate) fn iter_mut(&mut self) -> impl Iterator<Item = (&K, &mut V)> {
        self.slots
            .iter_mut()
            .flatten()
            .map(|(key, value)| (&*key, value))
    }

    pub(crate) fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(key, _)| key)
    }

    pub(crate) fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, value)| value)
    }

    pub(crate) fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.iter_mut().map(|(_, value)| value)
    }
}

/// A view into a single [`IndexMap`] slot.
pub(crate) struct Entry<'a, K, V> {
    map: &'a mut IndexMap<K, V>,
    key: K,
}

impl<'a, K: Index, V> Entry<'a, K, V> {
    pub(crate) fn or_insert_with(self, make: impl FnOnce() -> V) -> &'a mut V {
        let IndexMap { slots, len } = self.map;
        let index = self.key.index();
        if index >= slots.len() {
            slots.resize_with(index + 1, || None);
        }
        let slot = &mut slots[index];
        if slot.is_none() {
            *len += 1;
        }
        &mut slot.get_or_insert_with(|| (self.key, make())).1
    }

    pub(crate) fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }
}

impl<K: Index, V, I: Index> std::ops::Index<I> for IndexMap<K, V> {
    type Output = V;

    fn index(&self, key: I) -> &V {
        self.get(key).expect("key present in map")
    }
}

/// Iterator over the entries of an [`IndexMap`] in ascending key order.
pub(crate) struct IndexMapIter<'a, K, V> {
    slots: std::slice::Iter<'a, Option<(K, V)>>,
}

impl<'a, K, V> Iterator for IndexMapIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.slots.find_map(|slot| slot.as_ref().map(|(key, value)| (key, value)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.slots.size_hint().1)
    }
}

impl<K, V> FusedIterator for IndexMapIter<'_, K, V> {}

impl<'a, K: Index, V> IntoIterator for &'a IndexMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = IndexMapIter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K, V> IntoIterator for IndexMap<K, V> {
    type Item = (K, V);
    type IntoIter = std::iter::Flatten<std::vec::IntoIter<Option<(K, V)>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.slots.into_iter().flatten()
    }
}

impl<K: Index, V> Extend<(K, V)> for IndexMap<K, V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<K: Index, V> FromIterator<(K, V)> for IndexMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut map = Self::new();
        map.extend(iter);
        map
    }
}
