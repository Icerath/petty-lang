use crate::{
    mir::{BinaryOp, Operand, RValue, Statement, Terminator, UnaryOp},
    symbol::Symbol,
};

use super::Lowering;

impl Lowering<'_> {
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
            "int_to_str" => unary!(IntToStr),
            "print" => unary!(StrPrint),
            "chr" => unary!(Chr),
            "print_char" => unary!(PrintChar),
            _ => return false,
        };
        let place = self.new_place();
        self.current().stmts.push(Statement::Assign { place, rvalue });
        self.finish_with(Terminator::Return(Operand::Place(place)));
        true
    }
}
