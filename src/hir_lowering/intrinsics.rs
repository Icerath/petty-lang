use crate::{
    mir::{Instrinsic, Operand, RValue, Statement, Terminator},
    symbol::Symbol,
};

use super::Lowering;

impl Lowering<'_> {
    pub fn try_instrinsic(&mut self, ident: Symbol) -> bool {
        let instrinsic = match ident.as_str() {
            "strlen" => Instrinsic::Strlen(Operand::arg(0)),
            "str_find" => Instrinsic::StrFind(Operand::arg(0), Operand::arg(1)),
            "str_rfind" => Instrinsic::StrRFind(Operand::arg(0), Operand::arg(1)),
            "int_to_str" => Instrinsic::IntToStr(Operand::arg(0)),
            "print" => Instrinsic::PrintStr(Operand::arg(0)),
            _ => return false,
        };
        let place = self.new_place();
        self.current()
            .stmts
            .push(Statement::Assign { place, rvalue: RValue::Instrinsic(instrinsic) });
        self.finish_with(Terminator::Return(Operand::Place(place)));
        true
    }
}
