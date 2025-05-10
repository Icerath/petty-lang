use thin_vec::ThinVec;

use super::Lowering;
use crate::{
    mir::{BinaryOp, Constant, Operand, Place, RValue, Terminator, UnaryOp},
    symbol::Symbol,
    ty::{Ty, TyKind},
};

impl Lowering<'_, '_, '_> {
    pub fn try_intrinsic(&mut self, ty: Option<Ty>, ident: Symbol) -> bool {
        let Some(rvalue) = Self::intrinsic_rvalue(&ident, ty, &[]) else { return false };
        let local = self.assign_new(rvalue);
        self.finish_with(Terminator::Return(Operand::Place(Place::local(local))));
        true
    }
    // will return a RValue::Call if this fails
    pub fn try_call_intrinsic(
        &mut self,
        function: Operand,
        ty: Option<Ty>,
        args: ThinVec<Operand>,
    ) -> Result<RValue, RValue> {
        macro_rules! bail {
            () => {
                return Err(RValue::Call { function, args })
            };
        }

        let Operand::Constant(Constant::Func(body)) = function else { bail!() };
        let true = self.mir.bodies[body].auto else { bail!() };
        let Some(ident) = self.mir.bodies[body].name else { bail!() };

        match Self::intrinsic_rvalue(&ident, ty, &args) {
            Some(rvalue) => Ok(rvalue),
            None => bail!(),
        }
    }

    fn intrinsic_rvalue(name: &str, ty: Option<Ty>, args: &[Operand]) -> Option<RValue> {
        macro_rules! arg {
            ($n: literal) => {
                args.get($n).cloned().unwrap_or(Operand::arg($n))
            };
        }

        macro_rules! unary {
            ($name: ident) => {
                RValue::Unary { op: UnaryOp::$name, operand: arg!(0) }
            };
        }
        macro_rules! binary {
            ($name: ident) => {
                RValue::Binary { lhs: arg!(0), op: BinaryOp::$name, rhs: arg!(1) }
            };
        }
        Some(match (ty, name) {
            (Some(TyKind::Str), "len") => unary!(StrLen),
            (Some(TyKind::Str), "find") => binary!(StrFind),
            (Some(TyKind::Str), "rfind") => binary!(StrRFind),
            (Some(TyKind::Int), "chr") => unary!(Chr),
            (Some(TyKind::Char), "ord") => unary!(Ord),
            (None, "__strjoin") => unary!(StrJoin),
            (None, "__printstr") => unary!(Print),
            (None, "__arraylen") => unary!(ArrayLen),
            (None, "__arraypush") => binary!(ArrayPush),
            (None, "__arraypop") => unary!(ArrayPop),
            _ => return None,
        })
    }
}
