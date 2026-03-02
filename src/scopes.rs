use crate::ast::{Expr, Identifier};

#[derive(Debug, Clone)]
pub struct Var {
    pub name: Identifier,
    pub value: Option<Expr>,
}

impl Var {
    /// Creates a new variable with the given name and value.
    #[inline]
    pub fn new(name: Identifier, value: Option<Expr>) -> Self {
        Var { name, value }
    }
}

#[derive(Debug, Clone)]
pub struct Scope {
    variables: Vec<Var>,
}

impl Scope {
    /// Creates a new empty scope.
    #[inline]
    pub fn new() -> Self {
        Scope {
            variables: Vec::new(),
        }
    }

    /// Adds a variable to the scope.
    #[inline]
    pub fn add_var(&mut self, var: Var) {
        self.variables.push(var);
    }

    /// Adds multiple variables to the scope.
    #[inline]
    pub fn add_vars<T: IntoIterator<Item = Var>>(&mut self, iter: T) {
        self.variables.extend(iter);
    }

    /// Updates a variable in the scope, if it exists.
    /// If it does not exist, it will be added to the scope.
    #[inline]
    pub fn update_var(&mut self, var: Var) {
        if let Some(existing_var) = self.variables.iter_mut().find(|v| v.name == var.name) {
            *existing_var = var;
        } else {
            self.add_var(var);
        }
    }

    /// Clears the tracked value for a variable in this scope.
    #[inline]
    pub fn kill_var(&mut self, name: &Identifier) -> bool {
        if let Some(existing_var) = self.variables.iter_mut().find(|v| v.name == *name) {
            existing_var.value = None;
            true
        } else {
            false
        }
    }

    /// Removes a variable from this scope entirely.
    #[inline]
    pub fn remove_var(&mut self, name: &Identifier) -> bool {
        let len_before = self.variables.len();
        self.variables.retain(|var| var.name != *name);
        self.variables.len() != len_before
    }

    /// Clears aliases that depend on the given identifier.
    #[inline]
    pub fn invalidate_references_to(&mut self, name: &Identifier) {
        for var in &mut self.variables {
            if matches!(var.value.as_ref(), Some(Expr::Name(alias)) if alias == name) {
                var.value = None;
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ScopeManager {
    scopes: Vec<Scope>,
}

impl ScopeManager {
    /// Creates a new scope manager with no scopes.
    #[inline]
    pub fn new() -> Self {
        ScopeManager { scopes: Vec::new() }
    }

    /// Pushes a new scope onto the stack.
    #[inline]
    pub fn push_scope(&mut self) -> &mut Scope {
        let scope = Scope::new();
        self.scopes.push(scope);
        self.scopes.last_mut().unwrap()
    }

    /// Pushes a scope onto the stack with the given variables.
    #[inline]
    pub fn push_scope_with(&mut self, vars: Vec<Var>) {
        self.scopes.push(Scope { variables: vars });
    }

    /// Gets the current scope, if it exists.
    #[inline]
    pub fn top_scope(&mut self) -> Option<&mut Scope> {
        self.scopes.last_mut()
    }

    /// Returns whether the current scope already contains the given name.
    #[inline]
    pub fn current_scope_has(&self, name: &Identifier) -> bool {
        self.scopes
            .last()
            .is_some_and(|scope| scope.variables.iter().any(|var| var.name == *name))
    }

    /// Pops the current scope from the stack.
    #[inline]
    pub fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// Returns the current lexical scope depth.
    #[inline]
    pub fn len(&self) -> usize {
        self.scopes.len()
    }

    /// Returns a variable from the current scope, if it exists.
    /// If one cannot be found in the current scope, it will search
    /// parent scopes until it finds one or exhausts all scopes.
    pub fn get_var(&self, name: &Identifier) -> Option<&Var> {
        for scope in self.scopes.iter().rev() {
            if let Some(var) = scope.variables.iter().find(|var| var.name == *name) {
                return Some(var);
            }
        }
        None
    }

    /// Updates the nearest visible variable with the given name.
    /// Returns whether a visible variable was found.
    pub fn update_var(&mut self, var: Var) -> bool {
        for scope in self.scopes.iter_mut().rev() {
            if scope
                .variables
                .iter()
                .any(|existing| existing.name == var.name)
            {
                scope.update_var(var);
                return true;
            }
        }
        false
    }

    /// Clears the tracked value for the nearest matching variable.
    pub fn kill_var(&mut self, name: &Identifier) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.kill_var(name) {
                return;
            }
        }
    }

    /// Removes the nearest matching variable from visible scopes.
    pub fn remove_var(&mut self, name: &Identifier) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.remove_var(name) {
                return;
            }
        }
    }

    /// Clears aliases that depend on the given identifier in any visible scope.
    pub fn invalidate_references_to(&mut self, name: &Identifier) {
        for scope in self.scopes.iter_mut().rev() {
            scope.invalidate_references_to(name);
        }
    }
}
