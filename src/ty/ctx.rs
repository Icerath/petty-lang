use std::{cell::RefCell, collections::BTreeMap};

use index_vec::IndexVec;

use super::{
    Function, GenericId, GenericRange, Interned, Struct, Ty, TyInterner, TyKey, TyKind, TyVid,
    kind::StructId,
};
use crate::{ast::Ident, symbol::Symbol};

#[derive(Debug)]
pub struct TyCtx<'tcx> {
    pub(crate) inner: RefCell<TyCtxInner<'tcx>>,
    pub(crate) interner: TyInterner<'tcx>,
}

impl<'tcx> TyCtx<'tcx> {
    pub fn new(interner: TyInterner<'tcx>) -> Self {
        Self { inner: RefCell::default(), interner }
    }
    pub fn new_generics(&self, generics: &[Ident]) -> GenericRange {
        let mut inner = self.inner.borrow_mut();
        let mut iter = generics.iter();
        let Some(start) = iter.next() else { return GenericRange::EMPTY };
        let start = inner.new_generic(start.symbol);
        iter.for_each(|generic| _ = inner.new_generic(generic.symbol));
        GenericRange { start, len: generics.len().try_into().unwrap() }
    }
    pub fn generic_symbol(&self, id: GenericId) -> Symbol {
        self.inner.borrow_mut().generic_names[id]
    }
    pub fn new_struct(
        &self,
        name: Symbol,
        generics: GenericRange,
        fields: Vec<(Symbol, Ty<'tcx>)>,
    ) -> Ty<'tcx> {
        Interned(
            self.interner.intern_new(self.inner.borrow_mut().new_struct(name, generics, fields)),
        )
    }
    pub fn add_method(&self, ty: Ty<'tcx>, name: Symbol, func: Function<'tcx>) {
        let func = self.intern(TyKind::Function(func));
        self.inner.borrow_mut().add_method(ty, name, func);
    }
    pub fn get_method(&self, ty: Ty<'tcx>, name: Symbol) -> Option<&'tcx Function<'tcx>> {
        let ty = self.inner.borrow().get_method(ty, name)?;
        let TyKind::Function(func) = ty.0 else { unreachable!() };
        Some(func)
    }
    pub fn struct_name(&self, id: StructId) -> Symbol {
        self.inner.borrow().struct_names[id]
    }
    pub fn intern(&self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        #[cfg(debug_assertions)]
        match kind {
            TyKind::Unit
            | TyKind::Never
            | TyKind::Bool
            | TyKind::Int
            | TyKind::Char
            | TyKind::Str
            | TyKind::Range
            | TyKind::Infer(..) => unreachable!(),
            _ => {}
        }
        Interned(self.interner.intern(kind))
    }
    pub fn new_infer(&self) -> Ty<'tcx> {
        self.inner.borrow_mut().new_infer(self.interner)
    }
    pub fn try_infer_shallow<'a>(&self, ty: Ty<'a>) -> Result<Ty<'a>, Ty<'a>>
    where
        'tcx: 'a,
    {
        self.inner.borrow().try_infer_shallow(ty)
    }
    #[cfg_attr(debug_assertions, track_caller)]
    pub fn infer_shallow(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.try_infer_shallow(ty).expect("Failed to Infer")
    }
    #[cfg_attr(debug_assertions, track_caller)]
    pub fn infer_deep(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.inner.borrow().try_infer_deep(ty, self.interner).expect("Failed to Infer")
    }
    pub fn try_infer_deep(&self, ty: Ty<'tcx>) -> Result<Ty<'tcx>, Ty<'tcx>> {
        self.inner.borrow().try_infer_deep(ty, self.interner)
    }
    pub fn eq(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        self.inner.borrow_mut().eq(lhs, rhs)
    }
    pub fn sub(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        self.inner.borrow_mut().sub(lhs, rhs)
    }
}

#[derive(Default, Debug)]
pub(crate) struct TyCtxInner<'tcx> {
    pub(crate) subs: IndexVec<TyVid, Ty<'tcx>>,
    pub(crate) struct_names: IndexVec<StructId, Symbol>,
    pub(crate) generic_names: IndexVec<GenericId, Symbol>,
    pub(crate) methods: BTreeMap<(TyKey<'tcx>, Symbol), Ty<'tcx>>,
}

impl<'tcx> TyCtxInner<'tcx> {
    fn add_method(&mut self, ty: Ty<'tcx>, name: Symbol, method: Ty<'tcx>) {
        self.methods.insert((TyKey(ty), name), method);
    }
    fn get_method(&self, ty: Ty<'tcx>, name: Symbol) -> Option<Ty<'tcx>> {
        self.methods.get(&(TyKey(ty), name)).copied()
    }

    fn new_struct(
        &mut self,
        name: Symbol,
        generics: GenericRange,
        fields: Vec<(Symbol, Ty<'tcx>)>,
    ) -> TyKind<'tcx> {
        let id = self.struct_names.push(name);
        TyKind::Struct(Box::new(Struct { id, generics, fields }))
    }

    fn new_generic(&mut self, symbol: Symbol) -> GenericId {
        self.generic_names.push(symbol)
    }

    fn new_infer(&mut self, intern: TyInterner<'tcx>) -> Ty<'tcx> {
        let id = self.subs.next_idx();
        let ty = Interned(intern.insert_arena(TyKind::Infer(id)));
        self.subs.push(ty);
        ty
    }

    fn try_infer_shallow(&self, ty: Ty<'tcx>) -> Result<Ty<'tcx>, Ty<'tcx>> {
        match *ty {
            TyKind::Infer(var) if self.subs[var] == ty => Err(ty),
            TyKind::Infer(var) => self.try_infer_shallow(self.subs[var]).map_err(|_| ty),
            _ => Ok(ty),
        }
    }

    fn try_infer_deep(&self, ty: Ty<'tcx>, intern: TyInterner<'tcx>) -> Result<Ty<'tcx>, Ty<'tcx>> {
        macro_rules! intern {
            ($inner: expr) => {
                Interned(intern.intern($inner))
            };
        }

        let inferred = self.try_infer_shallow(ty)?;
        Ok(match inferred.0 {
            TyKind::Array(of) => {
                intern!(TyKind::Array(self.try_infer_deep(*of, intern).map_err(|_| ty)?))
            }
            TyKind::Ref(of) => {
                intern!(TyKind::Ref(self.try_infer_deep(*of, intern).map_err(|_| ty)?))
            }
            TyKind::Function(Function { params, ret }) => {
                let params = params
                    .iter()
                    .map(|param| self.try_infer_deep(*param, intern))
                    .collect::<Result<_, _>>()?;

                let ret = self.try_infer_deep(*ret, intern)?;
                intern!(TyKind::Function(Function { params, ret }))
            }
            TyKind::Struct(strct) => {
                //  { id, generics, symbols, fields }
                let fields = strct
                    .fields
                    .iter()
                    .map(|(name, field)| self.try_infer_deep(*field, intern).map(|ty| (*name, ty)))
                    .collect::<Result<_, _>>()?;

                intern!(TyKind::Struct(Box::new(Struct {
                    id: strct.id,
                    generics: strct.generics,
                    fields
                })))
            }
            _ => inferred,
        })
    }

    #[expect(clippy::match_same_arms)]
    fn eq(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        match (lhs.0, rhs.0) {
            (lhs, rhs) if lhs == rhs => Ok(()),
            (TyKind::Poison, _) | (_, TyKind::Poison) => Ok(()),
            (TyKind::Infer(l), TyKind::Infer(r)) if l == r => Ok(()),
            (TyKind::Infer(var), _) => self.insertl(*var, rhs),
            (_, TyKind::Infer(var)) => self.insertr(lhs, *var),
            (TyKind::Array(lhs), TyKind::Array(rhs)) => self.eq(*lhs, *rhs),
            (TyKind::Ref(lhs), TyKind::Ref(rhs)) => self.eq(*lhs, *rhs),
            (TyKind::Function(lhs), TyKind::Function(rhs)) => {
                assert_eq!(lhs.params.len(), rhs.params.len());
                lhs.params.iter().zip(&rhs.params).try_for_each(|(l, r)| self.eq(*l, *r))?;
                self.eq(lhs.ret, rhs.ret)
            }
            (TyKind::Struct(l_struct), TyKind::Struct(r_struct)) => {
                if l_struct.id != r_struct.id {
                    return Err([lhs, rhs]);
                }
                for ((_, lhs), (_, rhs)) in l_struct.fields.iter().zip(&r_struct.fields) {
                    self.eq(*lhs, *rhs)?;
                }
                Ok(())
            }
            (..) => Err([lhs, rhs]),
        }
    }

    /// Says that `lhs` must be a subtype of `rhs`.
    /// never is a subtype of everything.
    fn sub(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Result<(), [Ty<'tcx>; 2]> {
        let Err([lhs, rhs]) = self.eq(lhs, rhs) else { return Ok(()) };
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
            return if is_left { self.eq(sub, ty) } else { self.eq(ty, sub) };
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
