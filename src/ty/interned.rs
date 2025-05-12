use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::Deref,
    ptr,
};

pub struct Interned<'a, T>(pub &'a T);

impl<T: fmt::Debug> fmt::Debug for Interned<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> Clone for Interned<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Interned<'_, T> {}

impl<T> PartialEq for Interned<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

impl<T> Eq for Interned<'_, T> {}

impl<T: PartialOrd> PartialOrd for Interned<'_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if ptr::eq(self.0, other.0) { Some(Ordering::Equal) } else { self.0.partial_cmp(other.0) }
    }
}

impl<T: Ord> Ord for Interned<'_, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        if ptr::eq(self.0, other.0) { Ordering::Equal } else { self.0.cmp(other.0) }
    }
}

impl<T> Hash for Interned<'_, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        ptr::hash(self.0, state);
    }
}

impl<T> Deref for Interned<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.0
    }
}
