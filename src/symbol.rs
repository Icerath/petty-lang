use std::{fmt, ops::Deref};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol {
    inner: symbol_table::GlobalSymbol,
}

impl Symbol {
    pub fn as_str(self) -> &'static str {
        self.inner.as_str()
    }
}

impl AsRef<Symbol> for Symbol {
    fn as_ref(&self) -> &Symbol {
        self
    }
}

impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Self { inner: value.into() }
    }
}

impl From<String> for Symbol {
    fn from(value: String) -> Self {
        Self { inner: value.into() }
    }
}

impl From<&String> for Symbol {
    fn from(value: &String) -> Self {
        Self { inner: value.into() }
    }
}

impl PartialEq<&str> for Symbol {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl Deref for Symbol {
    type Target = str;
    fn deref(&self) -> &'static str {
        self.as_str()
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}
