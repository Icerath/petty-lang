use std::{cell::Cell, fmt, rc::Rc};

use super::Value;

#[derive(Clone, Default)]
pub struct Array {
    inner: Rc<Cell<Vec<Value>>>,
}

impl Array {
    fn with<T>(&self, f: impl FnOnce(&mut Vec<Value>) -> T) -> T {
        let mut inner = self.inner.take();
        let out = f(&mut inner);
        self.inner.set(inner);
        out
    }
    pub fn get(&self, index: usize) -> Option<Value> {
        self.with(|array| array.get(index).cloned())
    }
    pub fn set(&self, index: usize, value: Value) {
        self.with(|array| array[index] = value);
    }
    pub fn extend(&self, value: Value, count: usize) {
        self.with(|array| array.extend(std::iter::repeat_n(value, count)));
    }
}

impl fmt::Debug for Array {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.with(|array| array.fmt(f))
    }
}
