use std::marker::PhantomData;

use crate::{HashMap, symbol::Symbol};

pub struct ModuleScopes<B, T> {
    pub bodies: Vec<Body<B, T>>,
}

pub struct Body<B, T> {
    pub data: B,
    scopes: Vec<Scope<T>>,
}

impl<B, T> Body<B, T> {
    fn new(data: B) -> Self {
        Self { data, scopes: vec![Scope::default()] }
    }
}

pub struct Scope<T> {
    pub variables: HashMap<Symbol, T>,
}

impl<T> Scope<T> {
    pub fn insert(&mut self, var: Symbol, data: T) -> Option<T> {
        self.variables.insert(var, data)
    }
    pub fn extend(&mut self, other: Scope<T>) {
        self.variables.extend(other.variables);
    }
}

impl<T> Default for Scope<T> {
    fn default() -> Self {
        Self { variables: HashMap::default() }
    }
}

impl<B, T> ModuleScopes<B, T> {
    pub fn new(body: B) -> Self {
        Self { bodies: vec![Body::new(body)] }
    }
    fn raw_body(&self) -> &Body<B, T> {
        self.bodies.last().unwrap()
    }
    fn raw_body_mut(&mut self) -> &mut Body<B, T> {
        self.bodies.last_mut().unwrap()
    }
    pub fn body(&self) -> &B {
        &self.raw_body().data
    }
    pub fn body_mut(&mut self) -> &mut B {
        &mut self.raw_body_mut().data
    }
    pub fn push_body(&mut self, body: B) -> BodyToken {
        self.bodies.push(Body { data: body, scopes: vec![Scope::default()] });
        BodyToken { __priv: PhantomData }
    }
    #[expect(clippy::needless_pass_by_value)]
    pub fn pop_body(&mut self, token: BodyToken) -> B {
        _ = token;
        self.bodies.pop().unwrap().data
    }
    pub fn push_scope(&mut self) -> ScopeToken {
        self.raw_body_mut().scopes.push(Scope::default());
        ScopeToken { __priv: PhantomData }
    }
    #[expect(clippy::needless_pass_by_value)]
    pub fn pop_scope(&mut self, token: ScopeToken) -> Scope<T> {
        _ = token;
        self.raw_body_mut().scopes.pop().unwrap()
    }
    #[expect(unused)]
    pub fn scope(&self) -> &Scope<T> {
        self.raw_body().scopes.last().unwrap()
    }
    pub fn scope_mut(&mut self) -> &mut Scope<T> {
        self.raw_body_mut().scopes.last_mut().unwrap()
    }
    pub fn get(&self, key: Symbol) -> Option<&T> {
        // FIXME: should only use last body
        self.bodies
            .iter()
            .rev()
            .find_map(|body| body.scopes.iter().rev().find_map(|scope| scope.variables.get(&key)))
        // self.raw_body().scopes.iter().rev().find_map(|scope| scope.variables.get(&key))
    }
    #[expect(unused)]
    pub fn get_mut(&mut self, key: Symbol) -> Option<&mut T> {
        // FIXME: should only use last body
        self.bodies.iter_mut().rev().find_map(|body| {
            body.scopes.iter_mut().rev().find_map(|scope| scope.variables.get_mut(&key))
        })
        // self.raw_body_mut().scopes.iter_mut().rev().find_map(|scope| scope.variables.get_mut(&key))
    }
    pub fn available_names(&self) -> impl Iterator<Item = Symbol> {
        self.raw_body().scopes.iter().rev().flat_map(|scope| scope.variables.keys()).copied()
    }
}

#[must_use]
pub struct ScopeToken {
    __priv: PhantomData<()>,
}

#[must_use]
pub struct BodyToken {
    __priv: PhantomData<()>,
}
