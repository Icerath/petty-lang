mod generic_range;
mod interner;

use std::{cell::RefCell, collections::HashMap, fmt, hash::Hash};

pub use generic_range::GenericRange;
use index_vec::IndexVec;
pub use interner::TyInterner;
use thin_vec::ThinVec;

use crate::{define_id, symbol::Symbol};

pub type Ty<'tcx> = &'tcx TyKind<'tcx>;

impl<'tcx> TyKind<'tcx> {
    pub fn replace_generics(
        &'tcx self,
        tcx: &'tcx TyCtx<'tcx>,
        mut f: impl FnMut(GenericId) -> TyVid + Copy,
    ) -> Ty<'tcx> {
        match *self {
            Self::Generic(id) => tcx.intern(TyKind::Infer(f(id))),
            Self::Array(ty) => tcx.intern(TyKind::Array(ty.replace_generics(tcx, f))),
            Self::Function(Function { ref params, ret, .. }) => {
                let params = params.iter().map(|param| param.replace_generics(tcx, f)).collect();
                let ret = ret.replace_generics(tcx, f);
                let func = Function { params, ret, generics: GenericRange::EMPTY };
                tcx.intern(TyKind::Function(func))
            }
            Self::Struct { .. } => todo!(),
            Self::Infer(..) => unreachable!(),
            Self::Unit
            | Self::Bool
            | Self::Char
            | Self::Int
            | Self::Never
            | Self::Range
            | Self::RangeInclusive
            | Self::Str => self,
        }
    }
}

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

define_id!(pub TyVid = u32);
define_id!(pub GenericId = u32);
define_id!(pub StructId = u32);

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
    Function(Function<'tcx>),
    Struct { id: StructId, fields: ThinVec<Ty<'tcx>> },
    Generic(GenericId),
    Infer(TyVid),
}

// TODO: We shouldn't actually need to keep track of a function's generics.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Function<'tcx> {
    pub params: ThinVec<Ty<'tcx>>,
    pub generics: GenericRange,
    pub ret: Ty<'tcx>,
}

impl<'tcx> Function<'tcx> {
    pub fn caller(&self, tcx: &'tcx TyCtx<'tcx>) -> (Vec<Ty<'tcx>>, Ty<'tcx>) {
        let map: HashMap<_, _> = self.generics.iter().map(|id| (id, tcx.new_vid())).collect();
        let f = |id| map[&id];
        let params = self.params.iter().map(|param| param.replace_generics(tcx, f)).collect();
        let ret = self.ret.replace_generics(tcx, f);
        (params, ret)
    }
}

pub struct TyCtx<'tcx> {
    inner: RefCell<TyCtxInner<'tcx>>,
    interner: &'tcx TyInterner,
}

impl<'tcx> TyCtx<'tcx> {
    pub fn new(interner: &'tcx TyInterner) -> Self {
        Self { inner: RefCell::default(), interner }
    }
    pub fn new_generics(&self, generics: &[Symbol]) -> GenericRange {
        let mut inner = self.inner.borrow_mut();
        let mut iter = generics.iter();
        let Some(start) = iter.next() else { return GenericRange::EMPTY };
        let start = inner.new_generic(*start);
        iter.for_each(|generic| _ = inner.new_generic(*generic));
        GenericRange { start, len: generics.len().try_into().unwrap() }
    }
    pub fn generic_symbol(&self, id: GenericId) -> Symbol {
        self.inner.borrow_mut().generic_names[id]
    }
    pub fn new_struct(&self, name: Symbol, fields: ThinVec<Ty<'tcx>>) -> Ty<'tcx> {
        self.intern(self.inner.borrow_mut().new_struct(name, fields))
    }
    pub fn intern(&self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        self.interner.intern(kind)
    }
    pub fn new_vid(&self) -> TyVid {
        self.inner.borrow_mut().vid(self.interner)
    }
    pub fn new_infer(&self) -> Ty<'tcx> {
        self.interner.intern(TyKind::Infer(self.new_vid()))
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
    pub fn try_eq(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        self.inner.borrow_mut().try_eq(lhs, rhs)
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
    generic_names: IndexVec<GenericId, Symbol>,
}

impl<'tcx> TyCtxInner<'tcx> {
    fn new_struct(&mut self, name: Symbol, fields: ThinVec<Ty<'tcx>>) -> TyKind<'tcx> {
        let id = self.struct_names.push(name);
        TyKind::Struct { id, fields }
    }

    fn new_generic(&mut self, symbol: Symbol) -> GenericId {
        self.generic_names.push(symbol)
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
            Self::Function(Function { params, generics, ret }) => {
                _ = generics; // todo;
                write!(f, "fn")?;
                let mut debug_tuple = f.debug_tuple("");
                for param in params {
                    debug_tuple.field(param);
                }
                debug_tuple.finish()?;
                write!(f, " -> {ret}")
            }
            Self::Infer(var) => write!(f, "infer<{}>", var.index()),
            Self::Generic(id) => write!(f, "<generic {id:?}>"),
            Self::Struct { .. } => write!(f, "struct"),
        }
    }
}
