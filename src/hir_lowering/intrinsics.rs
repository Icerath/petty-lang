use super::Lowering;
use crate::{
    mir::{BinaryOp, Operand, Place, RValue, Terminator, UnaryOp},
    symbol::Symbol,
};

impl Lowering<'_, '_> {
    pub fn try_instrinsic(&mut self, ident: Symbol) -> bool {
        macro_rules! unary {
            ($name: ident) => {
                RValue::UnaryExpr { op: UnaryOp::$name, operand: Operand::arg(0) }
            };
        }

        macro_rules! binary {
            ($name: ident) => {
                RValue::BinaryExpr {
                    lhs: Operand::arg(0),
                    op: BinaryOp::$name,
                    rhs: Operand::arg(1),
                }
            };
        }

        let rvalue = match ident.as_str() {
            "strlen" => unary!(StrLen),
            "str_find" => binary!(StrFind),
            "str_rfind" => binary!(StrRFind),
            "println" => unary!(Println),
            "chr" => unary!(Chr),
            "print" => unary!(Print),
            "len" => unary!(ArrayLen),
            "push" => binary!(ArrayPush),
            "pop" => binary!(ArrayPop),
            _ => return false,
        };
        let local = self.assign_new(rvalue);
        self.finish_with(Terminator::Return(Operand::Place(Place::local(local))));
        true
    }
}
