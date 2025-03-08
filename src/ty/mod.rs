mod common;

use std::{fmt, hash::Hash, rc::Rc};

use common::CommonTypes;
use thin_vec::ThinVec;

#[derive(Default, Debug)]
pub struct TyCtx {
    subs: Vec<Ty>,
    common: CommonTypes,
}

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TyVid {
    index: u32,
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

impl TyCtx {
    pub fn new_infer(&mut self) -> Ty {
        Ty::from(TyKind::Infer(self.vid()))
    }

    pub fn vid(&mut self) -> TyVid {
        let id = TyVid { index: self.subs.len() as u32 };
        self.subs.push(Ty::from(TyKind::Infer(id)));
        id
    }

    pub fn infer(&self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Infer(var) => self.infer(self.subs.get(var.index as usize).unwrap()),
            _ => ty.clone(),
        }
    }

    pub fn eq(&mut self, lhs: &Ty, rhs: &Ty) {
        match (lhs.kind(), rhs.kind()) {
            (TyKind::Infer(l), TyKind::Infer(r)) if l == r => {}
            (TyKind::Infer(var), _) => self.insert(*var, rhs),
            (_, TyKind::Infer(var)) => self.insert(*var, lhs),
            (TyKind::Array(lhs), TyKind::Array(rhs)) => self.eq(lhs, rhs),
            (lhs, rhs) => assert_eq!(lhs, rhs),
        }
    }

    fn insert(&mut self, var: TyVid, ty: &Ty) {
        if let Some(sub) = self.subs.get(var.index as usize).cloned() {
            self.eq(ty, &sub);
            return;
        }
        assert!(!self.occurs_in(var, ty), "Infinite type: {var:?} - {ty:?}");
        self.subs[var.index as usize] = ty.clone();
    }

    fn occurs_in(&self, this: TyVid, ty: &Ty) -> bool {
        match ty.kind() {
            TyKind::Infer(var) => {
                if let Some(sub) = self.subs.get(var.index as usize) {
                    if *sub.kind() != TyKind::Infer(*var) {
                        return self.occurs_in(*var, sub);
                    }
                }
                this == *var
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
