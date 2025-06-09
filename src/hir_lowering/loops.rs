use std::mem;

use super::{
    BinaryOp, BlockId, Constant, ExprId, Local, Lowering, Operand, Place, RValue, Symbol,
    Terminator, UnaryOp,
};
use crate::mir::Projection;

impl Lowering<'_, '_> {
    pub fn lower_loop(
        &mut self,
        condition: impl FnOnce(&mut Self) -> Option<Local>,
        iter: impl FnOnce(&mut Self),
    ) {
        self.finish_next();
        let condition_block = self.current_block();

        let prev_loop = mem::take(&mut self.current_mut().breaks);
        self.current_mut().breaks.push(condition_block);
        let prev_continue = self.current_mut().continue_block.replace(condition_block);

        let to_fix = condition(self).map(|looping| {
            let next = self.current_block() + 1;
            self.finish_with(Terminator::Branch {
                condition: Operand::local(looping),
                fals: BlockId::PLACEHOLDER,
                tru: next,
            })
        });

        let scope_token = self.scopes.push_scope();
        iter(self);
        self.scopes.pop_scope(scope_token);

        self.finish_with(Terminator::Goto(condition_block));

        let after_block = self.current_block();
        if let Some(to_fix) = to_fix {
            self.body_mut().blocks[to_fix].terminator.complete(after_block);
        }

        let breaks = mem::replace(&mut self.current_mut().breaks, prev_loop);
        self.current_mut().continue_block = prev_continue;
        for block in breaks {
            self.body_mut().blocks[block].terminator.complete(after_block);
        }
    }

    pub fn for_loop(
        &mut self,
        ident: Symbol,
        body: &[ExprId],
        condition: impl FnOnce(&mut Self) -> Local,
        iter: impl FnOnce(&mut Self) -> Local,
    ) {
        self.lower_loop(
            |lower| Some(condition(lower)),
            |lower| {
                let ident_var = iter(lower);
                lower.insert_local(ident, ident_var);
                for expr in body {
                    lower.lower(*expr);
                }
            },
        );
    }

    pub fn range_for(&mut self, ident: Symbol, iter: ExprId, body: &[ExprId]) {
        let range = self.lower(iter);
        let lo = self.assign_new(RValue::Unary { op: UnaryOp::RangeStart, operand: range.clone() });
        let hi = self.assign_new(RValue::Unary { op: UnaryOp::RangeEnd, operand: range });

        self.for_loop(
            ident,
            body,
            |lower| {
                lower.assign_new(RValue::Binary {
                    lhs: Operand::local(lo),
                    op: BinaryOp::IntLess,
                    rhs: Operand::local(hi),
                })
            },
            |lower| {
                let ident_var = lower.assign_new(Operand::local(lo));
                lower.assign(
                    lo,
                    RValue::Binary {
                        lhs: Operand::local(lo),
                        op: BinaryOp::IntAdd,
                        rhs: Constant::Int(1).into(),
                    },
                );
                ident_var
            },
        );
    }

    pub fn array_for(&mut self, ident: Symbol, iter: ExprId, body: &[ExprId]) {
        let iter_rvalue = self.lower_rvalue(iter);
        let iter = self.assign_new(iter_rvalue);

        let lo = self.assign_new(Constant::Int(0));
        let hi = self.assign_new(RValue::Unary {
            op: UnaryOp::ArrayLen,
            operand: Operand::Ref(Place::local(iter)),
        });

        self.for_loop(
            ident,
            body,
            |lower| {
                lower.assign_new(RValue::Binary {
                    lhs: Operand::local(lo),
                    op: BinaryOp::IntLess,
                    rhs: Operand::local(hi),
                })
            },
            |lower| {
                let place = Place { local: iter, projections: vec![Projection::Index(lo)] };
                let ident_var = lower.assign_new(RValue::Use(Operand::Place(place)));
                lower.assign(
                    lo,
                    RValue::Binary {
                        lhs: Operand::local(lo),
                        op: BinaryOp::IntAdd,
                        rhs: Constant::Int(1).into(),
                    },
                );
                ident_var
            },
        );
    }
}
