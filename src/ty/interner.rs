use std::{
    cell::{Cell, RefCell},
    mem,
};

use super::{Ty, TyKind};
use crate::HashSet;

#[derive(Default)]
pub struct TyInterner {
    // drop artificial statics first.
    set: RefCell<HashSet<&'static TyKind<'static>>>,
    allocator: typed_arena::Arena<TyKind<'static>>,
    cache_hits: Cell<usize>,
}

impl TyInterner {
    pub fn len(&self) -> usize {
        self.allocator.len()
    }
    pub fn cache_hits(&self) -> usize {
        self.cache_hits.get()
    }
    pub fn intern<'tcx>(&'tcx self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        let mut set = self.set.borrow_mut();
        if let Some(&ty) = set.get(&kind) {
            self.cache_hits.set(self.cache_hits.get() + 1);
            return ty;
        }
        let kind = unsafe { mem::transmute::<TyKind<'_>, TyKind<'static>>(kind) };
        let ty = self.allocator.alloc(kind);
        let ty = unsafe { mem::transmute::<Ty<'_>, Ty<'static>>(ty) };
        set.insert(ty);
        ty
    }
}
