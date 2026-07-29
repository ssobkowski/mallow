use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::hash::Hash;
use std::ops::Index;

/// Represents a single lexical scope, tracking variable names and
/// their associated values (if any).
#[derive(Debug, Clone)]
pub struct Scope<K: Hash + Eq, V> {
    variables: HashMap<K, V>,
}

impl<K: Hash + Eq, V> Default for Scope<K, V> {
    fn default() -> Self {
        Self {
            variables: HashMap::new(),
        }
    }
}

impl<K: Hash + Eq, V> Scope<K, V> {
    /// Creates a new empty scope.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a variable to the scope.
    #[inline]
    pub fn declare(&mut self, name: K, value: V) {
        self.variables.insert(name, value);
    }

    /// Gets a variable from the scope, if it exists.
    #[inline]
    #[must_use]
    pub fn get(&self, name: &K) -> Option<&V> {
        self.variables.get(name)
    }

    /// Gets a mutable reference to a variable in the scope, if it exists.
    #[inline]
    pub fn get_mut(&mut self, name: &K) -> Option<&mut V> {
        self.variables.get_mut(name)
    }

    /// Returns whether the scope contains a variable with the given name.
    #[inline]
    #[must_use]
    pub fn contains(&self, name: &K) -> bool {
        self.variables.contains_key(name)
    }

    /// Returns an [Entry] for the given name.
    #[inline]
    pub fn entry(&mut self, name: K) -> Entry<'_, K, V> {
        self.variables.entry(name)
    }
}

impl<K: Hash + Eq, V> Index<&K> for Scope<K, V> {
    type Output = V;

    fn index(&self, name: &K) -> &Self::Output {
        self.variables.index(name)
    }
}

#[derive(Debug, Clone)]
pub struct Scopes<K: Hash + Eq, V> {
    scopes: Vec<Scope<K, V>>,
}

impl<K: Hash + Eq, V> Default for Scopes<K, V> {
    fn default() -> Self {
        Self { scopes: Vec::new() }
    }
}

impl<K: Hash + Eq, V> Scopes<K, V> {
    /// Creates a new scope manager with no scopes.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Pushes a new scope onto the stack.
    #[inline]
    pub fn push_scope(&mut self) -> &mut Scope<K, V> {
        self.scopes.push_mut(Scope::new())
    }

    /// Gets the current scope mutably, if it exists.
    #[inline]
    pub fn top_scope_mut(&mut self) -> Option<&mut Scope<K, V>> {
        self.scopes.last_mut()
    }

    /// Returns an iterator over the scopes from innermost to outermost.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Scope<K, V>> {
        self.scopes.iter().rev()
    }

    /// Pops the current scope from the stack.
    #[inline]
    pub fn pop_scope(&mut self) -> Option<Scope<K, V>> {
        self.scopes.pop()
    }

    /// Declares a variable in the current scope. Returns false if no scope exists.
    #[inline]
    pub fn declare(&mut self, name: K, value: V) -> bool {
        if let Some(scope) = self.top_scope_mut() {
            scope.declare(name, value);
            true
        } else {
            false
        }
    }

    /// Returns whether the given name is declared in the current
    /// scope or any parent scopes.
    #[inline]
    pub fn contains(&self, name: &K) -> bool {
        self.iter().any(|s| s.contains(name))
    }

    /// Returns the value of the given name, if it is declared in the current
    /// scope or any parent scopes.
    #[inline]
    pub fn get(&self, name: &K) -> Option<&V> {
        self.iter().find_map(|s| s.get(name))
    }
}
