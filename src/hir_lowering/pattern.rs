use super::Lowering;
use crate::{
    hir::{ExprId, MatchArm, Pat},
    mir::{BinaryOp, BlockId, Constant, Operand, RValue, Terminator},
};

impl Lowering<'_, '_, '_> {
    pub(super) fn lower_match(&mut self, scrutinee: ExprId, arms: &[MatchArm]) -> RValue {
        // TODO: take refs into account

        // let ty = self.ty(scrutinee);
        let scrutinee = self.lower(scrutinee);
        let output = self.new_local();
        let mut placeholders = vec![];

        for arm in arms {
            let placeholder = match self.try_pattern(scrutinee.clone(), &arm.pat) {
                Some(condition) => {
                    let condition = self.assign_new(condition);
                    let next = self.current_block() + 1;
                    Some(self.finish_with(Terminator::Branch {
                        condition: Operand::local(condition),
                        fals: BlockId::PLACEHOLDER,
                        tru: next,
                    }))
                }
                None => None,
            };
            let body = self.lower(arm.body);
            self.assign(output, body);
            placeholders.push(self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER)));
            if let Some(placeholder) = placeholder {
                let current = self.current_block();
                self.body_mut().blocks[placeholder].terminator.complete(current);
            }
        }
        let current = self.current_block();
        for placeholder in placeholders {
            self.body_mut().blocks[placeholder].terminator.complete(current);
        }
        RValue::local(output)
    }
}

impl Lowering<'_, '_, '_> {
    fn try_pattern(&mut self, scrutinee: Operand, pat: &Pat) -> Option<RValue> {
        Some(match *pat {
            Pat::Ident(ident) => {
                let ident_var = self.assign_new(scrutinee);
                self.current_mut().scope().variables.insert(ident, ident_var);

                return None;
            }
            Pat::Str(str) => {
                let rhs = Constant::Str(str.as_str().into()).into();
                RValue::Binary { lhs: scrutinee, op: BinaryOp::StrEq, rhs }
            }
            Pat::Int(int) => {
                let rhs = Constant::Int(int).into();
                RValue::Binary { lhs: scrutinee, op: BinaryOp::IntEq, rhs }
            }
            Pat::Or(..) => todo!(),
        })
    }
}
