use std::{cell::RefCell, collections::HashSet, mem};

use super::{Ty, TyCtx, TyKind};

pub struct TyInterner {
    // drop artificial statics first.
    common: CommonTypes<'static>,
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
        let common = CommonTypes::init(&inner);
        let common = unsafe { mem::transmute::<CommonTypes<'_>, CommonTypes<'static>>(common) };

        Self { common, inner }
    }
}

impl TyInterner {
    pub fn intern<'tcx>(&'tcx self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        self.inner.intern(kind)
    }
}

impl Inner {
    fn intern<'tcx>(&'tcx self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        if let Some(ty) = self.set.borrow().get(&kind) {
            return Ty { kind: ty };
        }
        let kind = unsafe { mem::transmute::<TyKind<'_>, TyKind<'static>>(kind) };
        let ty = Ty { kind: self.allocator.alloc(kind) };
        let ty = unsafe { mem::transmute::<Ty<'_>, Ty<'static>>(ty) };
        self.set.borrow_mut().insert(ty.kind);
        ty
    }
}

macro_rules! common {
    [$($name: ident : $kind: ident),* $(,)?] => {
        struct CommonTypes<'tcx> {
            $($name: Ty<'tcx>),*
        }

        impl<'tcx> CommonTypes<'tcx> {
            fn init(intern: &'tcx Inner) -> Self {
                CommonTypes {
                    $($name: intern.intern(TyKind::$kind)),*
                }
            }
        }

        impl<'tcx> TyCtx<'tcx> {
            $(pub const fn $name(&self) -> Ty<'tcx> {
                self.interner.common.$name
            })*
        }
    };
}

common![
    unit: Unit,
    bool: Bool,
    int: Int,
    char: Char,
    str: Str,
    never: Never,
];
