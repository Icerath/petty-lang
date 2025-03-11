mod common;

use std::{cell::RefCell, fmt, hash::Hash, rc::Rc};

use common::CommonTypes;
use index_vec::IndexVec;
use thin_vec::ThinVec;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ty {
    kind: Rc<TyKind>,
}

impl Ty {
    pub fn kind(&self) -> &TyKind {
        &self.kind
    }
}

impl From<TyKind> for Ty {
    fn from(kind: TyKind) -> Self {
        Self { kind: Rc::new(kind) }
    }
}

index_vec::define_index_type! {
    pub struct TyVid = u32;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyKind {
    Unit,
    Bool,
    Int,
    Char,
    Str,
    Range,
    RangeInclusive,
    Array(Ty),
    Function { params: ThinVec<Ty>, ret: Ty },
    Infer(TyVid),
}

#[derive(Default, Debug)]
pub struct TyCtx {
    inner: RefCell<TyCtxInner>,
    common: CommonTypes,
}

impl TyCtx {
    pub fn new_infer(&self) -> Ty {
        self.inner.borrow_mut().new_infer()
    }
    pub fn infer_shallow(&self, ty: &Ty) -> Ty {
        self.inner.borrow().infer_shallow(ty)
    }
    pub fn infer_deep(&self, ty: &Ty) -> Ty {
        self.inner.borrow().infer_deep(ty)
    }
    pub fn eq(&self, lhs: &Ty, rhs: &Ty) {
        self.inner.borrow_mut().eq(lhs, rhs);
    }
}

#[derive(Default, Debug)]
struct TyCtxInner {
    subs: IndexVec<TyVid, Ty>,
}

impl TyCtxInner {
    fn new_infer(&mut self) -> Ty {
        Ty::from(TyKind::Infer(self.vid()))
    }

    fn vid(&mut self) -> TyVid {
        let id = self.subs.next_idx();
        self.subs.push(Ty::from(TyKind::Infer(id)))
    }

    fn infer_shallow(&self, ty: &Ty) -> Ty {
        match *ty.kind() {
            TyKind::Infer(var) if self.subs[var] == *ty => panic!("Failed to infer"),
            TyKind::Infer(var) => self.infer_shallow(&self.subs[var]),
            _ => ty.clone(),
        }
    }

    fn infer_deep(&self, ty: &Ty) -> Ty {
        let ty = self.infer_shallow(ty);
        match ty.kind() {
            TyKind::Array(of) => TyKind::Array(self.infer_deep(of)).into(),
            _ => ty.clone(),
        }
    }

    fn eq(&mut self, lhs: &Ty, rhs: &Ty) {
        match (lhs.kind(), rhs.kind()) {
            (TyKind::Infer(l), TyKind::Infer(r)) if l == r => {}
            (TyKind::Infer(var), _) => self.insert(*var, rhs),
            (_, TyKind::Infer(var)) => self.insert(*var, lhs),
            (TyKind::Array(lhs), TyKind::Array(rhs)) => self.eq(lhs, rhs),
            (lhs, rhs) => assert_eq!(lhs, rhs),
        }
    }

    fn insert(&mut self, var: TyVid, ty: &Ty) {
        if let Some(sub) = self.subs.get(var).cloned() {
            if let &TyKind::Infer(sub) = sub.kind() {
                if sub == var {
                    self.subs[var] = ty.clone();
                }
            }
            self.eq(ty, &sub);
            return;
        }
        assert!(!self.occurs_in(var, ty), "Infinite type: {var:?} - {ty:?}");
        self.subs[var] = ty.clone();
    }

    fn occurs_in(&self, this: TyVid, ty: &Ty) -> bool {
        match ty.kind() {
            &TyKind::Infer(var) => {
                if let Some(sub) = self.subs.get(var) {
                    if *sub.kind() != TyKind::Infer(var) {
                        return self.occurs_in(var, sub);
                    }
                }
                this == var
            }
            _ => false,
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.kind, f)
    }
}
