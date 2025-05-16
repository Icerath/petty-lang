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
            macro_rules! eval_body {
                ($body: expr) => {{
                    let body = self.lower($body);
                    self.assign(output, body);
                    placeholders.push(self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER)));
                }};
            }
            macro_rules! branch {
                ($op:expr, $rhs:expr) => {{
                    let condition = self.assign_new(RValue::Binary {
                        lhs: scrutinee.clone(),
                        op: $op,
                        rhs: $rhs,
                    });
                    let next = self.current_block() + 1;
                    let placeholder = self.finish_with(Terminator::Branch {
                        condition: Operand::local(condition),
                        fals: BlockId::PLACEHOLDER,
                        tru: next,
                    });
                    eval_body!(arm.body);
                    let current = self.current_block();
                    self.body_mut().blocks[placeholder].terminator.complete(current);
                }};
            }
            match arm.pat {
                Pat::Ident(ident) => {
                    let ident_var = self.assign_new(scrutinee.clone());
                    self.current_mut().scope().variables.insert(ident, ident_var);

                    eval_body!(arm.body);
                }
                Pat::Str(str) => {
                    branch!(BinaryOp::StrEq, Constant::Str(str.as_str().into()).into());
                }
                Pat::Int(int) => branch!(BinaryOp::IntEq, Constant::Int(int).into()),
                Pat::Or(ref patterns) => {
                    _ = patterns;
                    todo!()
                }
            }
        }
        let current = self.current_block();
        for placeholder in placeholders {
            self.body_mut().blocks[placeholder].terminator.complete(current);
        }
        RValue::local(output)
    }
}
