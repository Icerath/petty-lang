use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut, Index, IndexMut},
};

use index_vec::IndexVec;

use crate::{HashMap, define_id, symbol::Symbol};

pub struct Global<B, Var, Ty> {
    pub module_storage: IndexVec<ModuleId, ModuleScopes<B, Var, Ty>>,
    #[expect(unused)]
    root: ModuleId,
    pub current: ModuleId,
}

pub struct ModuleScopes<B, Var, Ty> {
    #[expect(unused)]
    pub name: Symbol,
    pub parent: Option<ModuleId>,
    pub modules: HashMap<Symbol, ModuleId>,
    pub bodies: Vec<Body<B, Var, Ty>>,
}

pub struct Body<B, Var, Ty> {
    pub data: B,
    pub scopes: Vec<Scope<Var, Ty>>,
}

impl<B, Var, Ty> Body<B, Var, Ty> {
    fn new(data: B) -> Self {
        Self { data, scopes: vec![Scope::default()] }
    }
}

pub struct Scope<Var, Ty> {
    pub variables: HashMap<Symbol, Var>,
    pub types: HashMap<Symbol, Ty>,
}

impl<Var, Ty> Scope<Var, Ty> {
    pub fn insert(&mut self, symbol: Symbol, var: Var) -> Option<Var> {
        self.variables.insert(symbol, var)
    }
    pub fn insert_ty(&mut self, symbol: Symbol, ty: Ty) -> Option<Ty> {
        self.types.insert(symbol, ty)
    }
    pub fn extend(&mut self, other: Scope<Var, Ty>) {
        self.variables.extend(other.variables);
        self.types.extend(other.types);
    }
    pub fn extend_ref(&mut self, other: &Scope<Var, Ty>)
    where
        Var: Clone,
        Ty: Clone,
    {
        self.variables.extend(other.variables.iter().map(|(a, b)| (*a, b.clone())));
        self.types.extend(other.types.iter().map(|(a, b)| (*a, b.clone())));
    }
}

impl<Var, Ty> Default for Scope<Var, Ty> {
    fn default() -> Self {
        Self { variables: HashMap::default(), types: HashMap::default() }
    }
}

impl<B, Var, Ty> Global<B, Var, Ty> {
    pub fn new(body: B) -> Self {
        let root = ModuleScopes::new("crate".into(), None, body);
        let mut module_storage = IndexVec::new();
        let root = module_storage.push(root);
        Self { module_storage, root, current: root }
    }
    pub fn current(&self) -> &ModuleScopes<B, Var, Ty> {
        &self.module_storage[self.current]
    }
    pub fn current_mut(&mut self) -> &mut ModuleScopes<B, Var, Ty> {
        &mut self.module_storage[self.current]
    }
    pub fn push_module(&mut self, name: Symbol, body: B) -> (ModuleToken, ModuleId) {
        let module = self.module_storage.push(ModuleScopes::new(name, Some(self.current), body));
        self.modules.insert(name, module);
        self.current = module;
        (ModuleToken { __priv: PhantomData }, module)
    }
    pub fn pop_module(&mut self, _: ModuleToken) {
        let parent = self.module_storage[self.current].parent.unwrap();
        self.current = parent;
    }

    pub fn get_path(
        &self,
        path: impl IntoIterator<Item = impl AsRef<Symbol>>,
    ) -> Result<Option<&Var>, (ModuleId, Symbol)> {
        let (module, last) = self.get_module(path)?;
        Ok(self[module].get(last))
    }

    pub fn get_type_path(
        &self,
        path: impl IntoIterator<Item = impl AsRef<Symbol>>,
    ) -> Result<Option<&Ty>, (ModuleId, Symbol)> {
        let (module, last) = self.get_module(path)?;
        Ok(self[module].get_ty(last))
    }

    pub fn get_module(
        &self,
        path: impl IntoIterator<Item = impl AsRef<Symbol>>,
    ) -> Result<(ModuleId, Symbol), (ModuleId, Symbol)> {
        self.get_module_with(path, self.current)
    }
    pub fn get_module_with(
        &self,
        path: impl IntoIterator<Item = impl AsRef<Symbol>>,
        current: ModuleId,
    ) -> Result<(ModuleId, Symbol), (ModuleId, Symbol)> {
        let path = path.into_iter().map(|s| *s.as_ref());
        let fully_qualified = path;
        self.get_module_inner(fully_qualified, current)
    }
    fn get_module_inner(
        &self,
        mut iter: impl Iterator<Item = Symbol>,
        mut current_module: ModuleId,
    ) -> Result<(ModuleId, Symbol), (ModuleId, Symbol)> {
        let Some(mut last) = iter.next() else { unreachable!() };

        for next in iter {
            let Some(next_module) = self[current_module].modules.get(&last) else {
                return Err((current_module, last));
            };
            current_module = *next_module;
            last = next;
        }
        Ok((current_module, last))
    }
}

impl<B, Var, Ty> ModuleScopes<B, Var, Ty> {
    pub fn new(name: Symbol, parent: Option<ModuleId>, body: B) -> Self {
        Self { name, parent, bodies: vec![Body::new(body)], modules: HashMap::default() }
    }
    fn raw_body(&self) -> &Body<B, Var, Ty> {
        self.bodies.last().unwrap()
    }
    fn raw_body_mut(&mut self) -> &mut Body<B, Var, Ty> {
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
    pub fn pop_scope(&mut self, _: ScopeToken) -> Scope<Var, Ty> {
        self.raw_body_mut().scopes.pop().unwrap()
    }
    pub fn scope(&self) -> &Scope<Var, Ty> {
        self.raw_body().scopes.last().unwrap()
    }
    pub fn scope_mut(&mut self) -> &mut Scope<Var, Ty> {
        self.raw_body_mut().scopes.last_mut().unwrap()
    }
    pub fn get(&self, key: Symbol) -> Option<&Var> {
        // FIXME: should only use last body
        self.bodies
            .iter()
            .rev()
            .find_map(|body| body.scopes.iter().rev().find_map(|scope| scope.variables.get(&key)))
        // self.raw_body().scopes.iter().rev().find_map(|scope| scope.variables.get(&key))
    }
    pub fn get_ty(&self, key: Symbol) -> Option<&Ty> {
        self.bodies
            .iter()
            .rev()
            .find_map(|body| body.scopes.iter().rev().find_map(|scope| scope.types.get(&key)))
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

impl<B, Var, Ty> Deref for Global<B, Var, Ty> {
    type Target = ModuleScopes<B, Var, Ty>;
    fn deref(&self) -> &Self::Target {
        self.current()
    }
}

impl<B, Var, Ty> DerefMut for Global<B, Var, Ty> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.current_mut()
    }
}

impl<B, Var, Ty> Index<ModuleId> for Global<B, Var, Ty> {
    type Output = ModuleScopes<B, Var, Ty>;
    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.module_storage[index]
    }
}

impl<B, Var, Ty> IndexMut<ModuleId> for Global<B, Var, Ty> {
    fn index_mut(&mut self, index: ModuleId) -> &mut Self::Output {
        &mut self.module_storage[index]
    }
}
