mod interner;

use std::{cell::RefCell, fmt, hash::Hash};

use index_vec::IndexVec;
pub use interner::TyInterner;
use thin_vec::ThinVec;

use crate::symbol::Symbol;

pub type Ty<'tcx> = &'tcx TyKind<'tcx>;

#[expect(dead_code)]
impl TyKind<'_> {
    pub const fn is_never(&self) -> bool {
        matches!(self, Self::Never)
    }
    pub const fn is_unit(&self) -> bool {
        matches!(self, Self::Unit)
    }
    pub const fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }
    pub const fn is_int(&self) -> bool {
        matches!(self, Self::Int)
    }
    pub const fn is_char(&self) -> bool {
        matches!(self, Self::Char)
    }
    pub const fn is_str(&self) -> bool {
        matches!(self, Self::Str)
    }
    pub const fn is_range(&self) -> bool {
        matches!(self, Self::Range)
    }
    pub const fn is_array(&self) -> bool {
        matches!(*self, TyKind::Array(..))
    }
}

index_vec::define_index_type! {
    pub struct TyVid = u32;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

index_vec::define_index_type! {
    pub struct StructId = u32;
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyKind<'tcx> {
    Never,
    Unit,
    Bool,
    Int,
    Char,
    Str,
    Range,
    RangeInclusive,
    Array(Ty<'tcx>),
    Function { params: ThinVec<Ty<'tcx>>, ret: Ty<'tcx> },
    Struct { id: StructId, fields: ThinVec<Ty<'tcx>> },
    Infer(TyVid),
}

pub struct TyCtx<'tcx> {
    inner: RefCell<TyCtxInner<'tcx>>,
    interner: &'tcx TyInterner,
}

impl<'tcx> TyCtx<'tcx> {
    pub fn new(interner: &'tcx TyInterner) -> Self {
        Self { inner: RefCell::default(), interner }
    }
    pub fn new_struct(&self, name: Symbol, fields: ThinVec<Ty<'tcx>>) -> Ty<'tcx> {
        self.intern(self.inner.borrow_mut().new_struct(name, fields))
    }
    pub fn intern(&self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        self.interner.intern(kind)
    }
    pub fn new_infer(&self) -> Ty<'tcx> {
        self.inner.borrow_mut().new_infer(self.interner)
    }
    pub fn infer_shallow(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.inner.borrow().infer_shallow(ty)
    }
    pub fn infer_deep(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.inner.borrow().infer_deep(ty, self.interner)
    }
    #[track_caller]
    pub fn eq(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) {
        self.inner.borrow_mut().eq(lhs, rhs);
    }
    #[track_caller]
    pub fn try_subtype(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        self.inner.borrow_mut().subtype(lhs, rhs)
    }
}

#[derive(Default, Debug)]
struct TyCtxInner<'tcx> {
    subs: IndexVec<TyVid, Ty<'tcx>>,
    struct_names: IndexVec<StructId, Symbol>,
}

impl<'tcx> TyCtxInner<'tcx> {
    fn new_struct(&mut self, name: Symbol, fields: ThinVec<Ty<'tcx>>) -> TyKind<'tcx> {
        let id = self.struct_names.push(name);
        TyKind::Struct { id, fields }
    }

    fn new_infer(&mut self, intern: &'tcx TyInterner) -> Ty<'tcx> {
        intern.intern(TyKind::Infer(self.vid(intern)))
    }

    fn vid(&mut self, intern: &'tcx TyInterner) -> TyVid {
        let id = self.subs.next_idx();
        self.subs.push(intern.intern(TyKind::Infer(id)))
    }

    fn infer_shallow(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        match *ty {
            TyKind::Infer(var) if self.subs[var] == ty => panic!("Failed to infer"),
            TyKind::Infer(var) => self.infer_shallow(self.subs[var]),
            _ => ty,
        }
    }

    fn infer_deep(&self, ty: Ty<'tcx>, intern: &'tcx TyInterner) -> Ty<'tcx> {
        let ty = self.infer_shallow(ty);
        match *ty {
            TyKind::Array(of) => intern.intern(TyKind::Array(self.infer_deep(of, intern))),
            _ => ty,
        }
    }

    #[track_caller]
    fn eq(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) {
        self.try_eq(lhs, rhs).unwrap();
    }

    fn try_eq(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        match (lhs, rhs) {
            (TyKind::Infer(l), TyKind::Infer(r)) if l == r => Ok(()),
            (TyKind::Infer(var), _) => self.insertl(*var, rhs),
            (_, TyKind::Infer(var)) => self.insertr(lhs, *var),
            (TyKind::Array(lhs), TyKind::Array(rhs)) => self.try_eq(lhs, rhs),
            (lhs, rhs) if lhs == rhs => Ok(()),
            (..) => Err([lhs, rhs]),
        }
    }

    /// Says that `lhs` must be a subtype of `rhs`.
    /// never is a subtype of everything.
    #[track_caller]
    fn subtype(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        let Err([lhs, rhs]) = self.try_eq(lhs, rhs) else { return Ok(()) };
        if lhs.is_never() { Ok(()) } else { Err([lhs, rhs]) }
    }

    fn insertl(&mut self, var: TyVid, ty: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        self.insert_inner(var, ty, true)
    }

    fn insertr(&mut self, ty: Ty<'tcx>, var: TyVid) -> Result<(), [Ty<'tcx>; 2]> {
        self.insert_inner(var, ty, false)
    }

    fn insert_inner(
        &mut self,
        var: TyVid,
        ty: Ty<'tcx>,
        is_left: bool,
    ) -> Result<(), [Ty<'tcx>; 2]> {
        if let Some(&sub) = self.subs.get(var) {
            if let TyKind::Infer(sub) = *sub {
                if sub == var {
                    self.subs[var] = ty;
                }
            }
            return if is_left { self.try_eq(sub, ty) } else { self.try_eq(ty, sub) };
        }
        assert!(!self.occurs_in(var, ty), "Infinite type: {var:?} - {ty:?}");
        self.subs[var] = ty;
        Ok(())
    }

    fn occurs_in(&self, this: TyVid, ty: Ty<'tcx>) -> bool {
        match *ty {
            TyKind::Infer(var) => {
                if let Some(&sub) = self.subs.get(var) {
                    if *sub != TyKind::Infer(var) {
                        return self.occurs_in(var, sub);
                    }
                }
                this == var
            }
            _ => false,
        }
    }
}

impl fmt::Display for TyKind<'_> {
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
            Self::Struct { .. } => write!(f, "struct"),
        }
    }
}
