use std::collections::HashMap;
use std::hash::Hash;

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

    /// Creates a new scope with the given variables.
    #[inline]
    pub fn with_vars(vars: impl IntoIterator<Item = (K, V)>) -> Self {
        Self {
            variables: vars.into_iter().collect(),
        }
    }

    /// Adds a variable to the scope.
    #[inline]
    pub fn declare(&mut self, name: K, value: V) {
        self.variables.insert(name, value);
    }

    /// Adds multiple variables to the scope.
    #[inline]
    pub fn declare_many(&mut self, iter: impl IntoIterator<Item = (K, V)>) {
        self.variables.extend(iter);
    }

    /// Gets a variable from the scope, if it exists.
    #[inline]
    #[must_use]
    pub fn get(&self, name: &K) -> Option<&V> {
        self.variables.get(name)
    }

    /// Gets a variable from the scope mutably, if it exists.
    #[inline]
    #[must_use]
    pub fn get_mut(&mut self, name: &K) -> Option<&mut V> {
        self.variables.get_mut(name)
    }

    /// Returns whether the scope contains a variable with the given name.
    #[inline]
    #[must_use]
    pub fn contains(&self, name: &K) -> bool {
        self.variables.contains_key(name)
    }

    /// Updates a variable in the scope, if it exists.
    ///
    /// # Returns
    /// Whether a variable with the given name was found and updated.
    #[inline]
    #[must_use]
    pub fn set(&mut self, name: &K, value: V) -> bool {
        if let Some(v) = self.variables.get_mut(name) {
            *v = value;
            true
        } else {
            false
        }
    }

    /// Removes a variable from this scope entirely.
    ///
    /// # Returns
    /// Whether a variable with the given name was found and removed.
    #[inline]
    #[must_use]
    pub fn remove(&mut self, name: &K) -> bool {
        self.variables.remove(name).is_some()
    }
}

#[derive(Debug, Clone)]
pub struct ScopeManager<K: Hash + Eq, V> {
    scopes: Vec<Scope<K, V>>,
}

impl<K: Hash + Eq, V> Default for ScopeManager<K, V> {
    fn default() -> Self {
        Self { scopes: Vec::new() }
    }
}

impl<K: Hash + Eq, V> ScopeManager<K, V> {
    /// Creates a new scope manager with no scopes.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Pushes a new scope onto the stack.
    #[inline]
    pub fn push_scope(&mut self) -> &mut Scope<K, V> {
        self.scopes.push(Scope::new());
        self.scopes.last_mut().expect("scope was just pushed")
    }

    /// Pushes a scope onto the stack with the given variables.
    #[inline]
    pub fn push_scope_with(&mut self, vars: impl IntoIterator<Item = (K, V)>) -> &mut Scope<K, V> {
        self.scopes.push(Scope::with_vars(vars));
        self.scopes.last_mut().expect("scope was just pushed")
    }

    /// Gets the current scope, if it exists.
    #[inline]
    pub fn top_scope(&self) -> Option<&Scope<K, V>> {
        self.scopes.last()
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

    /// Returns an iterator over the scopes from innermost to outermost, allowing mutation.
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Scope<K, V>> {
        self.scopes.iter_mut().rev()
    }

    /// Pops the current scope from the stack.
    #[inline]
    pub fn pop_scope(&mut self) -> Option<Scope<K, V>> {
        self.scopes.pop()
    }

    /// Returns the current lexical scope depth.
    #[inline]
    pub fn len(&self) -> usize {
        self.scopes.len()
    }

    /// Returns whether the scope manager has no scopes.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.scopes.is_empty()
    }

    /// Declares a variable in the current scope. Returns false if no scope exists.
    #[inline]
    #[must_use]
    pub fn declare_var(&mut self, name: K, value: V) -> bool {
        if let Some(scope) = self.top_scope_mut() {
            scope.declare(name, value);
            true
        } else {
            false
        }
    }

    /// Returns a variable from the current scope, if it exists.
    /// If one cannot be found in the current scope, it will search
    /// parent scopes until it finds one or exhausts all scopes.
    #[must_use]
    pub fn get_var(&self, name: &K) -> Option<&V> {
        self.iter().find_map(|s| s.get(name))
    }

    /// Updates the nearest visible binding. Returns false if not found.
    pub fn set_var(&mut self, name: &K, value: V) -> bool {
        for scope in self.iter_mut() {
            if let Some(v) = scope.get_mut(name) {
                *v = value;
                return true;
            }
        }
        false
    }

    /// Removes the nearest matching variable from visible scopes.
    #[inline]
    pub fn remove_var(&mut self, name: &K) -> bool {
        self.iter_mut().any(|s| s.remove(name))
    }
}
