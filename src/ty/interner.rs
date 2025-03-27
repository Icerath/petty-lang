use super::{Ty, TyKind};
use crate::HashSet;
use std::{cell::RefCell, mem};

pub struct TyInterner {
    inner: Inner,
}

#[derive(Default)]
struct Inner {
    // drop artificial statics first.
    set: RefCell<HashSet<&'static TyKind<'static>>>,
    allocator: typed_arena::Arena<TyKind<'static>>,
}

impl Default for TyInterner {
    fn default() -> Self {
        let inner = Inner::default();
        Self { inner }
    }
}

impl TyInterner {
    pub fn intern<'tcx>(&'tcx self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        self.inner.intern(kind)
    }
}

impl Inner {
    fn intern<'tcx>(&'tcx self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        let mut set = self.set.borrow_mut();
        if let Some(&ty) = set.get(&kind) {
            return ty;
        }
        let kind = unsafe { mem::transmute::<TyKind<'_>, TyKind<'static>>(kind) };
        let ty = self.allocator.alloc(kind);
        let ty = unsafe { mem::transmute::<Ty<'_>, Ty<'static>>(ty) };
        set.insert(ty);
        ty
    }
}
