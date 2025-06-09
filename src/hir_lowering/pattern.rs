use super::Lowering;
use crate::{
    hir::{self, ExprId, MatchArm, Pat},
    hir_lowering::Var,
    mir::{BinaryOp, BlockId, Constant, Operand, Projection, RValue, Terminator, UnaryOp},
    ty::{Ty, TyKind},
};

impl<'tcx> Lowering<'_, 'tcx> {
    pub(super) fn lower_match(&mut self, scrutinee: ExprId, arms: &[MatchArm<'tcx>]) -> RValue {
        // TODO: take refs into account

        let ty = self.ty(scrutinee);
        let scrutinee = self.lower(scrutinee);
        let output = self.new_local();
        let mut placeholders = vec![];

        for arm in arms {
            let placeholder = match self.try_pattern(scrutinee.clone(), ty, &arm.pat) {
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
    #[expect(clippy::too_many_lines)]
    fn try_pattern(&mut self, scrutinee: Operand, ty: Ty<'tcx>, pat: &Pat<'tcx>) -> Option<RValue> {
        Some(match *pat {
            Pat::Struct(ty, ref fields) => {
                let TyKind::Struct(strct) = ty.0 else { unreachable!() };
                let scrutinee_place = self.process_to_place(scrutinee);
                let condition_local = self.new_local();
                let mut placeholders = vec![];
                for field in fields {
                    let index = strct.field_index(field.ident).unwrap();
                    let field_ty = strct.fields[index].1;
                    let mut field_place = scrutinee_place.clone();
                    field_place.projections.push(Projection::Field(index.try_into().unwrap()));
                    let Some(condition) =
                        self.try_pattern(Operand::Place(field_place), field_ty, &field.pat)
                    else {
                        continue;
                    };
                    self.assign(condition_local, condition);
                    let next = self.current_block() + 1;
                    placeholders.push(self.finish_with(Terminator::Branch {
                        condition: Operand::local(condition_local),
                        fals: BlockId::PLACEHOLDER,
                        tru: next,
                    }));
                }
                let current = self.current_block();
                let set_condition = !placeholders.is_empty();
                for placeholder in placeholders {
                    self.body_mut().blocks[placeholder].terminator.complete(current);
                }
                if set_condition {
                    RValue::local(condition_local)
                } else {
                    return None;
                }
            }
            Pat::Wildcard => return None,
            Pat::Ident(ident) => {
                // FIXME: avoid double lookup
                let var = if let Some(&local) = self.scopes.get(ident) {
                    local
                } else {
                    let local = self.new_local();
                    self.insert_local(ident, local);
                    Var::Local(local)
                };
                let Var::Local(local) = var else { todo!() };
                self.assign(local, scrutinee);
                return None;
            }
            Pat::Expr(expr) => {
                let rhs = self.lower_rvalue(expr);
                let rhs_ty = self.ty(expr);
                self.binary_op_inner((scrutinee.into(), ty), hir::BinaryOp::Eq, (rhs, rhs_ty))
            }
            Pat::If(expr) => self.lower_rvalue(expr),
            Pat::Or(ref patterns) => {
                let mut placeholders = vec![];
                let condition_local = self.new_local();
                for pat in patterns {
                    let Some(condition) = self.try_pattern(scrutinee.clone(), ty, pat) else {
                        continue;
                    };
                    self.assign(condition_local, condition);
                    let next = self.current_block() + 1;
                    placeholders.push(self.finish_with(Terminator::Branch {
                        condition: Operand::local(condition_local),
                        fals: next,
                        tru: BlockId::PLACEHOLDER,
                    }));
                }
                let current = self.current_block();
                let set_condition = !placeholders.is_empty();
                for placeholder in placeholders {
                    self.body_mut().blocks[placeholder].terminator.complete(current);
                }
                if set_condition {
                    RValue::local(condition_local)
                } else {
                    return None;
                }
            }
            Pat::And(ref pats) => {
                let condition_local = self.new_local();
                let mut placeholders = vec![];
                for pat in pats {
                    let Some(condition) = self.try_pattern(scrutinee.clone(), ty, pat) else {
                        continue;
                    };
                    self.assign(condition_local, condition);
                    let next = self.current_block() + 1;
                    placeholders.push(self.finish_with(Terminator::Branch {
                        condition: Operand::local(condition_local),
                        fals: BlockId::PLACEHOLDER,
                        tru: next,
                    }));
                }
                let current = self.current_block();
                let set_condition = !placeholders.is_empty();
                for placeholder in placeholders {
                    self.body_mut().blocks[placeholder].terminator.complete(current);
                }
                if set_condition {
                    RValue::local(condition_local)
                } else {
                    return None;
                }
            }
            Pat::Array(ref pats) => {
                let &TyKind::Array(of) = ty.0 else { unreachable!() };
                let mut placeholders = vec![];

                let scrutinee_place = self.process_to_place(scrutinee);

                let len = self.assign_new(RValue::Unary {
                    op: UnaryOp::ArrayLen,
                    operand: Operand::Ref(scrutinee_place.clone()),
                });
                let condition_local = self.assign_new(RValue::Binary {
                    lhs: Operand::local(len),
                    op: BinaryOp::IntEq,
                    rhs: Operand::Constant(Constant::Int(pats.len().try_into().unwrap())),
                });

                let next = self.current_block() + 1;
                placeholders.push(self.finish_with(Terminator::Branch {
                    condition: Operand::local(condition_local),
                    fals: BlockId::PLACEHOLDER,
                    tru: next,
                }));

                for (index, pat) in (0u32..).zip(pats) {
                    let mut field_place = scrutinee_place.clone();
                    field_place.projections.push(Projection::ConstantIndex(index));
                    let Some(condition) = self.try_pattern(Operand::Place(field_place), of, pat)
                    else {
                        continue;
                    };
                    self.assign(condition_local, condition);
                    let next = self.current_block() + 1;
                    placeholders.push(self.finish_with(Terminator::Branch {
                        condition: Operand::local(condition_local),
                        fals: BlockId::PLACEHOLDER,
                        tru: next,
                    }));
                }
                self.finish_next();
                let current = self.current_block();
                for placeholder in placeholders {
                    self.body_mut().blocks[placeholder].terminator.complete(current);
                }
                RValue::local(condition_local)
            }
        })
    }
}
