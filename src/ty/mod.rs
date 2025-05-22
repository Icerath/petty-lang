mod generic_range;
mod interned;
mod kind;

use std::{cell::RefCell, cmp::Ordering, collections::BTreeMap, hash::Hash};

pub use generic_range::GenericRange;
use index_vec::IndexVec;
pub use interned::Interned;
pub use kind::TyKind;
use petty_intern::Interner;
use thin_vec::ThinVec;

type TyInterner<'tcx> = &'tcx Interner<TyKind<'tcx>>;

use crate::{HashMap, ast::Identifier, define_id, symbol::Symbol};

pub type Ty<'tcx> = Interned<'tcx, TyKind<'tcx>>;

static NEVER: TyKind = TyKind::Never;
static UNIT: TyKind = TyKind::Unit;
static BOOL: TyKind = TyKind::Bool;
static INT: TyKind = TyKind::Int;
static CHAR: TyKind = TyKind::Char;
static STR: TyKind = TyKind::Str;
static RANGE: TyKind = TyKind::Range;
static POISON: TyKind = TyKind::Poison;

impl Ty<'_> {
    pub const NEVER: Self = Self(&NEVER);
    pub const UNIT: Self = Self(&UNIT);
    pub const BOOL: Self = Self(&BOOL);
    pub const INT: Self = Self(&INT);
    pub const CHAR: Self = Self(&CHAR);
    pub const STR: Self = Self(&STR);
    pub const RANGE: Self = Self(&RANGE);
    pub const POISON: Self = Self(&POISON);
}

define_id!(pub TyVid = u32);
define_id!(pub GenericId = u32);
define_id!(pub StructId = u32);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Struct<'tcx> {
    pub id: StructId,
    pub generics: GenericRange,
    pub fields: Vec<(Symbol, Ty<'tcx>)>,
}

impl<'tcx> Struct<'tcx> {
    pub fn field_ty(&self, target: Symbol) -> Option<Ty<'tcx>> {
        self.fields.iter().find_map(|&(field, ty)| (field == target).then_some(ty))
    }
    pub fn field_names(&self) -> impl Iterator<Item = Symbol> {
        self.fields.iter().map(|(name, _)| *name)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct Function<'tcx> {
    pub params: ThinVec<Ty<'tcx>>,
    pub ret: Ty<'tcx>,
}

impl<'tcx> Function<'tcx> {
    pub fn caller(&self, tcx: &'tcx TyCtx<'tcx>) -> Self {
        let mut map = HashMap::default();
        self.generics(&mut |id| _ = map.entry(id).or_insert_with(|| tcx.new_infer()));
        let f = |id| map[&id];
        let params = self.params.iter().map(|param| param.replace_generics(tcx, f)).collect();
        let ret = self.ret.replace_generics(tcx, f);
        Self { params, ret }
    }
    pub fn generics(&self, f: &mut impl FnMut(GenericId)) {
        self.params.iter().for_each(|param| param.generics(f));
        self.ret.generics(f);
    }
}

#[derive(Debug)]
pub struct TyCtx<'tcx> {
    inner: RefCell<TyCtxInner<'tcx>>,
    interner: TyInterner<'tcx>,
}

impl<'tcx> TyCtx<'tcx> {
    pub fn new(interner: TyInterner<'tcx>) -> Self {
        Self { inner: RefCell::default(), interner }
    }
    pub fn new_generics(&self, generics: &[Identifier]) -> GenericRange {
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
    #[track_caller]
    pub fn infer_shallow(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.try_infer_shallow(ty).expect("Failed to Infer")
    }
    #[track_caller]
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
struct TyCtxInner<'tcx> {
    subs: IndexVec<TyVid, Ty<'tcx>>,
    struct_names: IndexVec<StructId, Symbol>,
    generic_names: IndexVec<GenericId, Symbol>,
    methods: BTreeMap<(TyKey<'tcx>, Symbol), Ty<'tcx>>,
}

#[derive(Debug)]
pub struct TyKey<'tcx>(pub Ty<'tcx>);

impl PartialOrd for TyKey<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TyKey<'_> {
    #[expect(clippy::match_same_arms)]
    fn cmp(&self, other: &Self) -> Ordering {
        use TyKind as T;
        match (self.0.0, other.0.0) {
            (T::Generic(_), _) | (_, T::Generic(_)) => Ordering::Equal,
            (&T::Array(lhs), &T::Array(rhs)) => TyKey(lhs).cmp(&TyKey(rhs)),
            (&T::Ref(lhs), &T::Ref(rhs)) => TyKey(lhs).cmp(&TyKey(rhs)),
            (&T::Ref(ref_), _) => TyKey(ref_).cmp(&TyKey(other.0)),
            (_, &T::Ref(ref_)) => TyKey(self.0).cmp(&TyKey(ref_)),
            _ => self.0.cmp(&other.0),
        }
    }
}

impl PartialEq for TyKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for TyKey<'_> {}

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

impl Ty<'_> {
    pub fn fully_deref(self) -> Self {
        let mut ty = self;
        while let TyKind::Ref(of) = ty.0 {
            ty = *of;
        }
        ty
    }
    pub fn ref_depth(self) -> usize {
        let mut depth = 0;
        let mut ty = self;
        while let TyKind::Ref(of) = ty.0 {
            ty = *of;
            depth += 1;
        }
        depth
    }
}
