use std::{cell::Cell, fmt, rc::Rc};

use super::{Allocation, Value};

#[derive(Clone, Default)]
pub struct Array {
    inner: Rc<Cell<Vec<Allocation>>>,
}

impl Array {
    fn with<T>(&self, f: impl FnOnce(&mut Vec<Allocation>) -> T) -> T {
        let mut inner = self.inner.take();
        let out = f(&mut inner);
        self.inner.set(inner);
        out
    }
    pub fn with_capacity(cap: usize) -> Self {
        Self { inner: Rc::new(Cell::new(Vec::with_capacity(cap))) }
    }
    pub fn capacity(&self) -> usize {
        self.with(|vec| vec.capacity())
    }
    pub fn get(&self, index: usize) -> Option<Allocation> {
        self.with(|array| array.get(index).cloned())
    }
    #[expect(clippy::needless_pass_by_value)]
    pub fn extend(&self, value: Value, count: usize) {
        self.with(|array| {
            array.extend(std::iter::repeat_with(|| value.clone().into()).take(count));
        });
    }
    pub fn push(&self, value: Value) {
        self.with(|vec| vec.push(value.into()));
    }
    pub fn pop(&self) -> Value {
        self.with(|vec| vec.pop().unwrap().clone_raw())
    }
    pub fn len(&self) -> usize {
        self.with(|vec| vec.len())
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn for_each(&self, f: impl FnMut(&mut Allocation)) {
        self.with(|vec| vec.iter_mut().for_each(f));
    }
}

impl fmt::Debug for Array {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.with(|array| array.fmt(f))
    }
}

impl FromIterator<Allocation> for Array {
    fn from_iter<I: IntoIterator<Item = Allocation>>(iter: I) -> Self {
        Self { inner: Rc::new(Cell::new(iter.into_iter().collect())) }
    }
}
