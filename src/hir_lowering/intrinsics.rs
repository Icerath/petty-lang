use super::Lowering;
use crate::{
    mir::{BinaryOp, Operand, Place, RValue, Statement, Terminator, UnaryOp},
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
            "int_to_str" => unary!(IntToStr),
            "print" => unary!(StrPrint),
            "chr" => unary!(Chr),
            "print_char" => unary!(PrintChar),
            _ => return false,
        };
        self.mir.num_intrinsics += 1;
        let local = self.new_local();
        self.current().stmts.push(Statement::assign(local, rvalue));
        self.finish_with(Terminator::Return(Operand::Place(Place::local(local))));
        true
    }
}
