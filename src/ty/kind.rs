use std::fmt;

use thin_vec::ThinVec;

use super::{Function, GenericId, StructId, Ty, TyCtx, TyVid};

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

impl<'tcx> TyKind<'tcx> {
    pub fn generics(&self, f: &mut impl FnMut(GenericId)) {
        match *self {
            Self::Generic(id) => f(id),
            Self::Array(ty) => ty.generics(f),
            Self::Function(ref func) => func.generics(f),
            Self::Struct { ref fields, .. } => {
                // this seems wrong.
                fields.iter().for_each(|field| field.generics(f));
            }
            Self::Infer(..)
            | Self::Unit
            | Self::Bool
            | Self::Char
            | Self::Int
            | Self::Never
            | Self::Range
            | Self::RangeInclusive
            | Self::Str => {}
        }
    }

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
                let func = Function { params, ret };
                tcx.intern(TyKind::Function(func))
            }
            Self::Struct { ref fields, id } => {
                let fields = fields.iter().map(|field| field.replace_generics(tcx, f)).collect();
                tcx.intern(Self::Struct { id, fields })
            }
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
            Self::Function(Function { params, ret }) => {
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
