use std::fmt;

use thin_vec::ThinVec;

use super::{GenericId, GenericRange, Ty, TyCtx, TyVid};
use crate::{HashMap, define_id, symbol::Symbol};

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
            TyKind::Struct(ref strct) if strct.generics.len == 0 => {}
            TyKind::Struct(ref strct) => strct.fields.iter().for_each(|(_, ty)| ty.generics(f)),
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
        f: &mut impl FnMut(GenericId) -> Ty<'tcx>,
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
    pub fn field_index(&self, target: Symbol) -> Option<usize> {
        self.fields.iter().position(|&(name, _)| target == name)
    }
    pub fn infer_generics(&self, tcx: &'tcx TyCtx<'tcx>) -> Self {
        let mut map = HashMap::default();
        let new_fields = self
            .fields
            .iter()
            .map(|&(name, ty)| {
                (
                    name,
                    ty.replace_generics(tcx, &mut |id| {
                        *map.entry(id).or_insert_with(|| tcx.new_infer())
                    }),
                )
            })
            .collect();

        Self { id: self.id, generics: self.generics, fields: new_fields }
    }
    pub fn caller(&self, tcx: &'tcx TyCtx<'tcx>) -> (Ty<'tcx>, &'tcx Self) {
        let strct = self.infer_generics(tcx);
        let ty = tcx.intern(TyKind::Struct(Box::new(strct)));
        let TyKind::Struct(strct) = ty.0 else { unreachable!() };
        (ty, strct)
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
        let mut f = |id| map[&id];
        let params = self.params.iter().map(|param| param.replace_generics(tcx, &mut f)).collect();
        let ret = self.ret.replace_generics(tcx, &mut f);
        Self { params, ret }
    }
    pub fn generics(&self, f: &mut impl FnMut(GenericId)) {
        self.params.iter().for_each(|param| param.generics(f));
        self.ret.generics(f);
    }
}
