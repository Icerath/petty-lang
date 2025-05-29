mod generic_range;
mod interned;
mod kind;

use std::{cmp::Ordering, hash::Hash};

pub use ctx::TyCtx;
pub use generic_range::GenericRange;
pub use interned::Interned;
pub use kind::{Function, Struct, StructId, TyKind};
use petty_intern::Interner;

type TyInterner<'tcx> = &'tcx Interner<TyKind<'tcx>>;

use crate::define_id;

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

mod ctx;

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
            (T::Struct(lhs), T::Struct(rhs)) => {
                if lhs.id != rhs.id || lhs.generics.len == 0 {
                    return lhs.id.cmp(&rhs.id);
                }
                let lhs = lhs.fields.iter().map(|(_, ty)| TyKey(*ty));
                let rhs = rhs.fields.iter().map(|(_, ty)| TyKey(*ty));
                lhs.cmp(rhs)
            }
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
