use crate::ast::{Expr, Identifier};

#[derive(Debug, Clone)]
pub struct Var {
    name: Identifier,
    value: Option<Expr>,
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
    pub fn push_scope(&mut self) {
        self.scopes.push(Scope {
            variables: Vec::new(),
        });
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

    /// Pops the current scope from the stack.
    #[inline]
    pub fn pop_scope(&mut self) {
        self.scopes.pop();
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
}
