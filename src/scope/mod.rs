use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use index_vec::IndexVec;

use crate::{HashMap, define_id, symbol::Symbol};

pub struct Global<B, T> {
    module_storage: IndexVec<ModuleId, ModuleScopes<B, T>>,
    root: ModuleId,
    current: ModuleId,
}

pub struct ModuleScopes<B, T> {
    #[expect(unused)]
    pub name: Symbol,
    pub parent: Option<ModuleId>,
    pub modules: HashMap<Symbol, ModuleId>,
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

impl<B, T> Global<B, T> {
    pub fn new(body: B) -> Self {
        let root = ModuleScopes::new("crate".into(), None, body);
        let mut module_storage = IndexVec::new();
        let root = module_storage.push(root);
        Self { module_storage, root, current: root }
    }
    pub fn current(&self) -> &ModuleScopes<B, T> {
        &self.module_storage[self.current]
    }
    pub fn current_mut(&mut self) -> &mut ModuleScopes<B, T> {
        &mut self.module_storage[self.current]
    }
    pub fn push_module(&mut self, name: Symbol, body: B) -> ModuleToken {
        let module = self.module_storage.push(ModuleScopes::new(name, Some(self.current), body));
        self.modules.insert(name, module);
        self.current = module;
        ModuleToken { __priv: PhantomData }
    }
    pub fn pop_module(&mut self, _: ModuleToken) {
        let parent = self.module_storage[self.current].parent.unwrap();
        self.current = parent;
    }

    pub fn get_path(&self, path: impl IntoIterator<Item = impl AsRef<Symbol>>) -> Option<&T> {
        let (module, last) = self.get_module(path);
        module.get(last)
    }

    pub fn get_module(
        &self,
        path: impl IntoIterator<Item = impl AsRef<Symbol>>,
    ) -> (&ModuleScopes<B, T>, Symbol) {
        let path = path.into_iter().map(|s| *s.as_ref());
        let fully_qualified = path;
        self.get_module_inner(fully_qualified)
    }
    fn get_module_inner(
        &self,
        mut iter: impl Iterator<Item = Symbol>,
    ) -> (&ModuleScopes<B, T>, Symbol) {
        let Some(mut last) = iter.next() else { unreachable!() };
        let mut current_module = self.current();

        for next in iter {
            // FIXME: remove hack
            let next_module = match current_module.modules.get(&last) {
                Some(id) => *id,
                None => self.root,
            };
            current_module = &self.module_storage[next_module];
            last = next;
        }
        (current_module, last)
    }
}

impl<B, T> ModuleScopes<B, T> {
    pub fn new(name: Symbol, parent: Option<ModuleId>, body: B) -> Self {
        Self { name, parent, bodies: vec![Body::new(body)], modules: HashMap::default() }
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
    pub fn pop_body(&mut self, _: BodyToken) -> B {
        self.bodies.pop().unwrap().data
    }
    pub fn push_scope(&mut self) -> ScopeToken {
        self.raw_body_mut().scopes.push(Scope::default());
        ScopeToken { __priv: PhantomData }
    }
    pub fn pop_scope(&mut self, _: ScopeToken) -> Scope<T> {
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

#[must_use]
pub struct ModuleToken {
    __priv: PhantomData<()>,
}

define_id!(pub ModuleId);

impl<B, T> Deref for Global<B, T> {
    type Target = ModuleScopes<B, T>;
    fn deref(&self) -> &Self::Target {
        self.current()
    }
}

impl<B, T> DerefMut for Global<B, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.current_mut()
    }
}
