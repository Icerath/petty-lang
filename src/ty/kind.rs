use std::fmt;

use thin_vec::ThinVec;

use super::{Function, GenericId, StructId, Ty, TyCtx, TyVid};
use crate::symbol::Symbol;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyKind<'tcx> {
    Never,
    Unit,
    Bool,
    Int,
    Char,
    Str,
    Range,
    Array(Ty<'tcx>),
    Function(Function<'tcx>),
    Struct { id: StructId, symbols: ThinVec<Symbol>, fields: ThinVec<Ty<'tcx>> },
    Generic(GenericId),
    Infer(TyVid),
    Ref(Ty<'tcx>),
}

impl<'tcx> TyKind<'tcx> {
    pub fn generics(&self, f: &mut impl FnMut(GenericId)) {
        match *self {
            Self::Generic(id) => f(id),
            Self::Array(ty) | Self::Ref(ty) => ty.generics(f),
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
            Self::Ref(ty) => tcx.intern(TyKind::Ref(ty.replace_generics(tcx, f))),
            Self::Array(ty) => tcx.intern(TyKind::Array(ty.replace_generics(tcx, f))),
            Self::Function(Function { ref params, ret, .. }) => {
                let params = params.iter().map(|param| param.replace_generics(tcx, f)).collect();
                let ret = ret.replace_generics(tcx, f);
                tcx.intern(TyKind::Function(Function { params, ret }))
            }
            Self::Struct { ref fields, ref symbols, id } => {
                let fields = fields.iter().map(|field| field.replace_generics(tcx, f)).collect();
                tcx.intern(Self::Struct { id, symbols: symbols.clone(), fields })
            }
            Self::Infer(..) => unreachable!(),
            Self::Unit
            | Self::Bool
            | Self::Char
            | Self::Int
            | Self::Never
            | Self::Range
            | Self::Str => self,
        }
    }
}

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

impl TyCtx<'_> {
    pub fn display(&self, ty: Ty) -> impl fmt::Display {
        struct Display<'a, 'b, 'c>(&'a TyCtx<'b>, Ty<'c>);
        impl fmt::Display for Display<'_, '_, '_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let Self(tcx, ty) = self;
                match ty {
                    TyKind::Bool => write!(f, "bool"),
                    TyKind::Char => write!(f, "char"),
                    TyKind::Int => write!(f, "int"),
                    TyKind::Str => write!(f, "str"),
                    TyKind::Unit => write!(f, "()"),
                    TyKind::Never => write!(f, "!"),
                    TyKind::Range => write!(f, "Range"),
                    TyKind::Array(of) => write!(f, "[{}]", tcx.display(of)),
                    TyKind::Ref(of) => write!(f, "&{}", tcx.display(of)),
                    TyKind::Function(Function { params, ret }) => {
                        write!(f, "fn(")?;
                        for (i, param) in params.iter().enumerate() {
                            let prefix = if i == 0 { "" } else { ", " };
                            write!(f, "{prefix}{}", tcx.display(param))?;
                        }
                        write!(f, ")")?;
                        write!(f, " -> {}", tcx.display(ret))
                    }
                    TyKind::Infer(_) => write!(f, "_"),
                    TyKind::Generic(id) => write!(f, "{}", tcx.generic_symbol(*id)),
                    TyKind::Struct { id, .. } => write!(f, "{}", tcx.struct_name(*id)),
                }
            }
        }
        Display(self, ty)
    }
}
