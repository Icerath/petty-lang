use std::{cell::RefCell, collections::HashMap, mem};

use super::{Ty, TyCtx, TyKind};

pub struct TyInterner {
    // drop artificial statics first.
    common: CommonTypes<'static>,
    inner: Inner,
}

#[derive(Default)]
struct Inner {
    // drop artificial statics first.
    set: RefCell<HashMap<TyKind<'static>, Ty<'static>>>,
    allocator: bumpalo::Bump,
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
            return *ty;
        }
        let ty = Ty { kind: self.allocator.alloc(kind.clone()) };
        let ty = unsafe { mem::transmute::<Ty<'_>, Ty<'static>>(ty) };
        let kind = unsafe { mem::transmute::<TyKind<'_>, TyKind<'static>>(kind) };
        self.set.borrow_mut().insert(kind, ty);
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
                self.interner.$name()
            })*
        }

        impl TyInterner {
            $(const fn $name(&self) -> Ty<'_> {
                self.common.$name
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
