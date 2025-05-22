use std::fmt;

use super::{Function, GenericId, Struct, Ty, TyCtx, TyVid};

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
    Struct(Box<Struct<'tcx>>),
    Generic(GenericId),
    Infer(TyVid),
    Ref(Ty<'tcx>),
    Poison,
}

impl<'tcx> Ty<'tcx> {
    pub fn generics(self, f: &mut impl FnMut(GenericId)) {
        match *self.0 {
            TyKind::Generic(id) => f(id),
            TyKind::Array(ty) | TyKind::Ref(ty) => ty.generics(f),
            TyKind::Function(ref func) => func.generics(f),
            TyKind::Struct(ref strct) => strct.generics.iter().for_each(f),
            TyKind::Poison
            | TyKind::Infer(..)
            | TyKind::Unit
            | TyKind::Bool
            | TyKind::Char
            | TyKind::Int
            | TyKind::Never
            | TyKind::Range
            | TyKind::Str => {}
        }
    }

    pub fn replace_generics(
        self,
        tcx: &'tcx TyCtx<'tcx>,
        mut f: impl FnMut(GenericId) -> Ty<'tcx> + Copy,
    ) -> Ty<'tcx> {
        match *self.0 {
            TyKind::Generic(id) => f(id),
            TyKind::Ref(ty) => tcx.intern(TyKind::Ref(ty.replace_generics(tcx, f))),
            TyKind::Array(ty) => tcx.intern(TyKind::Array(ty.replace_generics(tcx, f))),
            TyKind::Function(Function { ref params, ret, .. }) => {
                let params = params.iter().map(|param| param.replace_generics(tcx, f)).collect();
                let ret = ret.replace_generics(tcx, f);
                tcx.intern(TyKind::Function(Function { params, ret }))
            }
            TyKind::Struct(ref strct) => {
                if strct.generics.len == 0 {
                    self
                } else {
                    let fields = strct
                        .fields
                        .iter()
                        .map(|(name, ty)| (*name, ty.replace_generics(tcx, f)))
                        .collect();
                    tcx.intern(TyKind::Struct(Box::new(Struct {
                        id: strct.id,
                        fields,
                        generics: strct.generics,
                    })))
                }
            }
            TyKind::Infer(..) => unreachable!(),
            TyKind::Poison
            | TyKind::Unit
            | TyKind::Bool
            | TyKind::Char
            | TyKind::Int
            | TyKind::Never
            | TyKind::Range
            | TyKind::Str => self,
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
    pub const fn is_poison(&self) -> bool {
        matches!(*self, TyKind::Poison)
    }
}

impl<'tcx> TyCtx<'tcx> {
    pub fn display<'a>(&self, ty: Ty<'a>) -> impl fmt::Display
    where
        'tcx: 'a,
    {
        struct Display<'a, 'b, 'c>(&'a TyCtx<'b>, Ty<'c>);
        impl fmt::Display for Display<'_, '_, '_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let Self(tcx, ty) = self;
                match ty.0 {
                    TyKind::Poison => write!(f, "<poisoned>"),
                    TyKind::Bool => write!(f, "bool"),
                    TyKind::Char => write!(f, "char"),
                    TyKind::Int => write!(f, "int"),
                    TyKind::Str => write!(f, "str"),
                    TyKind::Unit => write!(f, "()"),
                    TyKind::Never => write!(f, "!"),
                    TyKind::Range => write!(f, "Range"),
                    TyKind::Array(of) => write!(f, "[{}]", tcx.display(*of)),
                    TyKind::Ref(of) => write!(f, "&{}", tcx.display(*of)),
                    TyKind::Function(Function { params, ret }) => {
                        write!(f, "fn(")?;
                        for (i, param) in params.iter().enumerate() {
                            let prefix = if i == 0 { "" } else { ", " };
                            write!(f, "{prefix}{}", tcx.display(*param))?;
                        }
                        write!(f, ")")?;
                        write!(f, " -> {}", tcx.display(*ret))
                    }
                    TyKind::Infer(_) => write!(f, "_"),
                    TyKind::Generic(id) => write!(f, "{}", tcx.generic_symbol(*id)),
                    TyKind::Struct(strct) => {
                        write!(f, "{}", tcx.struct_name(strct.id))?;
                        write!(f, "<")?;
                        for (i, (_, field)) in strct.fields.iter().enumerate() {
                            let sep = if i != 0 { ", " } else { "" };
                            write!(f, "{sep}{}", tcx.display(*field))?;
                        }
                        write!(f, ">")
                    }
                }
            }
        }
        let ty = self.try_infer_shallow(ty).unwrap_or(ty);
        Display(self, ty)
    }
}
