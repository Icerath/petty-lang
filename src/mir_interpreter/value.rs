use std::{
    cell::{RefCell, RefMut},
    ops::Range,
    rc::Rc,
};

use arcstr::ArcStr;

use super::array::Array;
use crate::mir::BodyId;

#[derive(Debug, Clone)]
pub struct Allocation {
    inner: Rc<RefCell<Value>>,
}

impl Allocation {
    pub fn borrow(&self) -> RefMut<Value> {
        self.inner.borrow_mut()
    }
    pub fn clone_raw(&self) -> Value {
        self.inner.borrow().clone()
    }
}

impl From<Value> for Allocation {
    fn from(value: Value) -> Self {
        Self { inner: Rc::new(RefCell::new(value)) }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Unit,
    Array(Array),
    Bool(bool),
    Int(i64),
    Range(Box<Range<i64>>),
    Char(char),
    Str(ArcStr),
    Fn(BodyId),
    Struct(Array),
    Ref(Allocation),
}

macro_rules! value {
    ($ty:ident, $value: expr) => {{
        match $value {
            Value::$ty(out) => out,
            other => unreachable!("expected {}, found {other:?}", stringify!($ty)),
        }
    }};
}

impl Value {
    pub fn unwrap_bool(&mut self) -> bool {
        *value!(Bool, self)
    }
    pub fn unwrap_int(&mut self) -> i64 {
        *value!(Int, self)
    }
    pub fn unwrap_int_usize(&mut self) -> usize {
        let int = self.unwrap_int();
        int.try_into().unwrap_or_else(|_| panic!("{int}"))
    }
    pub fn unwrap_char(&mut self) -> char {
        *value!(Char, self)
    }
    pub fn unwrap_str(&mut self) -> ArcStr {
        value!(Str, self).clone()
    }
    pub fn unwrap_range(&mut self) -> Range<i64> {
        match self {
            Value::Range(out) => Range::clone(out),
            other => unreachable!("expected {}, found {other:?}", stringify!($ty)),
        }
    }
    pub fn unwrap_range_usize(&mut self) -> Range<usize> {
        let range = self.unwrap_range();
        usize::try_from(range.start).unwrap()..usize::try_from(range.end).unwrap()
    }
    pub fn unwrap_fn(&mut self) -> BodyId {
        *value!(Fn, self)
    }
    pub fn unwrap_array(&mut self) -> Array {
        value!(Array, self).clone()
    }
    pub fn unwrap_struct(&mut self) -> Array {
        value!(Struct, self).clone()
    }
}

impl Allocation {
    pub fn unwrap_array(&mut self) -> Array {
        self.borrow().unwrap_array()
    }
}
