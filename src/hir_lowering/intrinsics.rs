use thin_vec::ThinVec;

use super::Lowering;
use crate::{
    mir::{BinaryOp, Constant, Operand, Place, RValue, Terminator, UnaryOp},
    symbol::Symbol,
};

impl Lowering<'_, '_> {
    pub fn try_instrinsic(&mut self, ident: Symbol) -> bool {
        let Some(rvalue) = Self::intrinsic_rvalue(&ident, &[]) else { return false };
        let local = self.assign_new(rvalue);
        self.finish_with(Terminator::Return(Operand::Place(Place::local(local))));
        true
    }
    // will return a RValue::Call if this fails
    pub fn try_call_intrinsic(
        &mut self,
        function: Operand,
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

        match Self::intrinsic_rvalue(&ident, &args) {
            Some(rvalue) => Ok(rvalue),
            None => bail!(),
        }
    }

    fn intrinsic_rvalue(name: &str, args: &[Operand]) -> Option<RValue> {
        macro_rules! arg {
            ($n: literal) => {
                args.get($n).cloned().unwrap_or(Operand::arg($n))
            };
        }

        macro_rules! unary {
            ($name: ident) => {
                RValue::UnaryExpr { op: UnaryOp::$name, operand: arg!(0) }
            };
        }
        macro_rules! binary {
            ($name: ident) => {
                RValue::BinaryExpr { lhs: arg!(0), op: BinaryOp::$name, rhs: arg!(1) }
            };
        }
        Some(match name {
            "strlen" => unary!(StrLen),
            "str_find" => binary!(StrFind),
            "str_rfind" => binary!(StrRFind),
            "println" => unary!(Println),
            "chr" => unary!(Chr),
            "print" => unary!(Print),
            "len" => unary!(ArrayLen),
            "push" => binary!(ArrayPush),
            "pop" => binary!(ArrayPop),
            _ => return None,
        })
    }
}
