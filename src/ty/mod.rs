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
    Never,
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
    #[track_caller]
    pub fn eq(&self, lhs: &Ty, rhs: &Ty) {
        self.inner.borrow_mut().eq(lhs, rhs);
    }
    pub fn subtype(&self, lhs: &Ty, rhs: &Ty) {
        self.inner.borrow_mut().subtype(lhs, rhs);
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

    #[track_caller]
    fn eq(&mut self, lhs: &Ty, rhs: &Ty) {
        self.try_eq(lhs, rhs).unwrap();
    }

    fn try_eq(&mut self, lhs: &Ty, rhs: &Ty) -> Result<(), [Ty; 2]> {
        match (lhs.kind(), rhs.kind()) {
            (TyKind::Infer(l), TyKind::Infer(r)) if l == r => Ok(()),
            (TyKind::Infer(var), _) => self.insertl(*var, rhs),
            (_, TyKind::Infer(var)) => self.insertr(lhs, *var),
            (TyKind::Array(lhs), TyKind::Array(rhs)) => self.try_eq(lhs, rhs),
            (lhs, rhs) if lhs == rhs => Ok(()),
            (..) => Err([lhs.clone(), rhs.clone()]),
        }
    }

    /// Says that `lhs` must be a subtype of `rhs`.
    /// never is a subtype of everything.
    #[track_caller]
    fn subtype(&mut self, lhs: &Ty, rhs: &Ty) {
        let Err([lhs, rhs]) = self.try_eq(lhs, rhs) else { return };
        assert!(lhs.kind() == &TyKind::Never, "expected `{rhs}`, found `{lhs}`",);
    }

    fn insertl(&mut self, var: TyVid, ty: &Ty) -> Result<(), [Ty; 2]> {
        self.insert_inner(var, ty, true)
    }

    fn insertr(&mut self, ty: &Ty, var: TyVid) -> Result<(), [Ty; 2]> {
        self.insert_inner(var, ty, false)
    }

    fn insert_inner(&mut self, var: TyVid, ty: &Ty, is_left: bool) -> Result<(), [Ty; 2]> {
        if let Some(sub) = self.subs.get(var).cloned() {
            if let &TyKind::Infer(sub) = sub.kind() {
                if sub == var {
                    self.subs[var] = ty.clone();
                }
            }
            return if is_left { self.try_eq(&sub, ty) } else { self.try_eq(ty, &sub) };
        }
        assert!(!self.occurs_in(var, ty), "Infinite type: {var:?} - {ty:?}");
        self.subs[var] = ty.clone();
        Ok(())
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

impl fmt::Display for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "bool"),
            Self::Char => write!(f, "char"),
            Self::Int => write!(f, "int"),
            Self::Str => write!(f, "str"),
            Self::Unit => write!(f, "()"),
            Self::Never => write!(f, "!"),
            Self::Range => write!(f, "Range"),
            Self::RangeInclusive => write!(f, "RangeInclusive"),
            Self::Array(of) => write!(f, "[{of}]"),
            Self::Function { params, ret } => {
                write!(f, "fn")?;
                let mut debug_tuple = f.debug_tuple("");
                for param in params {
                    debug_tuple.field(param);
                }
                debug_tuple.finish()?;
                write!(f, " -> {ret}")
            }
            Self::Infer(var) => write!(f, "infer<{}>", var.index()),
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind().fmt(f)
    }
}
