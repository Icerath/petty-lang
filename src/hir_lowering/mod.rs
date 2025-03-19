mod intrinsics;

use std::{collections::HashMap, mem};

use crate::{
    hir::{self, ArraySeg, ExprId, ExprKind, Hir, LValue, Lit},
    mir::{
        self, Block, BlockId, Body, BodyId, Constant, Mir, Operand, Place, RValue, Statement,
        Terminator,
    },
    symbol::Symbol,
    ty::TyKind,
};

pub fn lower(hir: &Hir) -> Mir {
    let mut mir = Mir::default();
    let root_body = mir.bodies.push(Body::new(0));
    let bodies = vec![BodyInfo::new(root_body)];

    let mut lowering = Lowering { hir, mir, bodies };
    for &expr in &hir.root {
        lowering.lower(expr);
    }
    // TODO: Instead produce an error for any non-body expr in the global scope (probably before type analysis?)
    assert!(lowering.mir.bodies.first().unwrap().blocks.is_empty());
    lowering.mir
}

struct Lowering<'hir> {
    hir: &'hir Hir,
    mir: Mir,
    bodies: Vec<BodyInfo>,
}

struct BodyInfo {
    body: BodyId,
    functions: HashMap<Symbol, BodyId>,
    variables: HashMap<Symbol, Place>,
    stmts: Vec<Statement>,
    breaks: Vec<BlockId>,
}

impl BodyInfo {
    pub fn new(body: BodyId) -> Self {
        Self {
            body,
            functions: HashMap::default(),
            variables: HashMap::default(),
            stmts: vec![],
            breaks: vec![],
        }
    }
}

impl Lowering<'_> {
    fn body_ref(&self) -> &Body {
        &self.mir.bodies[self.bodies.last().unwrap().body]
    }
    fn body_mut(&mut self) -> &mut Body {
        &mut self.mir.bodies[self.bodies.last().unwrap().body]
    }
    fn current(&mut self) -> &mut BodyInfo {
        self.bodies.last_mut().unwrap()
    }
    fn finish_with(&mut self, terminator: Terminator) -> BlockId {
        let prev_block = Block { statements: mem::take(&mut self.current().stmts), terminator };
        self.body_mut().blocks.push(prev_block)
    }
    // returns the next block's id
    fn finish_next(&mut self) -> BlockId {
        let next_block = self.body_mut().blocks.next_idx() + 1;
        self.finish_with(Terminator::Goto(next_block));
        next_block
    }
    fn new_place(&mut self) -> Place {
        self.body_mut().new_place()
    }

    fn lower(&mut self, id: ExprId) -> Operand {
        let rvalue = self.lower_inner(id);
        self.process(rvalue)
    }

    fn process(&mut self, rvalue: RValue) -> Operand {
        match rvalue {
            RValue::Use(operand) => operand,
            rvalue => {
                let place = self.new_place();
                self.current().stmts.push(Statement::Assign { place, rvalue });
                Operand::Place(place)
            }
        }
    }

    #[expect(clippy::too_many_lines)]
    fn lower_inner(&mut self, id: ExprId) -> RValue {
        let expr = &self.hir.exprs[id];
        let is_unit = *expr.ty.kind() == TyKind::Unit;

        match &expr.kind {
            ExprKind::Literal(lit) => self.lit_rvalue(lit),
            ExprKind::Unary { op, expr } => {
                let operand = self.lower(*expr);
                let op = match op {
                    hir::UnaryOp::Not => mir::UnaryOp::BoolNot,
                    hir::UnaryOp::Neg => mir::UnaryOp::IntNeg,
                };
                RValue::UnaryExpr { op, operand }
            }
            ExprKind::FnDecl(decl) => {
                let hir::FnDecl { ident, params, body, .. } = &**decl;

                assert!(self.current().stmts.is_empty(), "TODO");
                let body_id = self.mir.bodies.push(Body::new(params.len()));
                self.current().functions.insert(*ident, body_id);
                self.bodies.push(BodyInfo::new(body_id));
                if self.bodies.len() == 2 && ident.as_str() == "main" {
                    self.mir.main_body = Some(body_id);
                }

                if self.bodies.len() == 2 && self.try_instrinsic(*ident) {
                } else {
                    for (i, param) in params.iter().enumerate() {
                        self.current().variables.insert(param.ident, Place::from(i));
                    }
                    let mut last = Operand::UNIT;
                    for expr in body {
                        last = self.lower(*expr);
                    }
                    self.finish_with(Terminator::Return(last));
                }
                self.bodies.pop().unwrap();
                RValue::Use(Operand::UNIT)
            }
            ExprKind::Let { ident, expr } => {
                let rvalue = self.lower_inner(*expr);
                let place = self.mir.bodies[self.bodies.last().unwrap().body].new_place();
                self.current().variables.insert(*ident, place);
                self.current().stmts.push(Statement::Assign { place, rvalue });
                RValue::Use(Operand::UNIT)
            }
            ExprKind::Return(expr) => {
                let place = self.lower(*expr);
                self.finish_with(Terminator::Return(place));
                RValue::Use(Operand::Unreachable)
            }
            ExprKind::Loop(block) => {
                let loop_block = self.finish_next();

                let prev_loop = mem::take(&mut self.current().breaks);
                for &expr in block {
                    self.lower(expr);
                }
                let after_loop = self.finish_with(Terminator::Goto(loop_block)) + 1;

                let breaks = mem::replace(&mut self.current().breaks, prev_loop);

                for block in breaks {
                    match &mut self.body_mut().blocks[block].terminator {
                        Terminator::Goto(block @ BlockId::PLACEHOLDER) => *block = after_loop,
                        _ => unreachable!(),
                    }
                }
                RValue::Use(Operand::UNIT)
            }
            ExprKind::If { arms, els } => {
                let mut jump_to_ends = Vec::with_capacity(arms.len());
                let out_place = self.new_place();
                for arm in arms {
                    let condition = self.lower(arm.condition);
                    let to_fix = self.finish_with(Terminator::Branch {
                        condition,
                        fals: BlockId::PLACEHOLDER,
                        tru: self.body_ref().blocks.next_idx() + 1,
                    });
                    let block_out = self.block_expr(&arm.body);
                    if !block_out.is_unreachable() {
                        if is_unit {
                            self.process(block_out);
                        } else {
                            self.current()
                                .stmts
                                .push(Statement::Assign { place: out_place, rvalue: block_out });
                        }
                        jump_to_ends.push(self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER)));
                    }
                    let current_block = self.body_ref().blocks.next_idx();
                    match &mut self.body_mut().blocks[to_fix].terminator {
                        Terminator::Branch { fals, .. } => *fals = current_block,
                        _ => unreachable!(),
                    }
                }
                let els_out = self.block_expr(els);
                if !els_out.is_unreachable() {
                    if is_unit {
                        self.process(els_out);
                    } else {
                        self.current()
                            .stmts
                            .push(Statement::Assign { place: out_place, rvalue: els_out });
                    }
                }

                let current = self.finish_next();
                for block in jump_to_ends {
                    match &mut self.body_mut().blocks[block].terminator {
                        Terminator::Goto(block @ BlockId::PLACEHOLDER) => *block = current,
                        _ => unreachable!(),
                    }
                }
                if is_unit {
                    RValue::Use(Operand::Constant(Constant::Unit))
                } else {
                    RValue::Use(Operand::Place(out_place))
                }
            }
            ExprKind::Assignment { lhs, expr } => {
                let rvalue = self.lower_inner(*expr);
                let (place, deref) = self.get_lvalue_place(lhs);
                let stmt = if deref {
                    Statement::DerefAssign { place, rvalue }
                } else {
                    Statement::Assign { place, rvalue }
                };
                self.current().stmts.push(stmt);
                RValue::Use(Operand::Constant(Constant::Unit))
            }
            &ExprKind::Binary { lhs, op, rhs } => {
                let ty = &self.hir.exprs[lhs].ty;
                let op = match (ty.kind(), op) {
                    (TyKind::Int, op) => match op {
                        hir::BinaryOp::Add => mir::BinaryOp::IntAdd,
                        hir::BinaryOp::Sub => mir::BinaryOp::IntSub,
                        hir::BinaryOp::Mul => mir::BinaryOp::IntMul,
                        hir::BinaryOp::Div => mir::BinaryOp::IntDiv,
                        hir::BinaryOp::Mod => mir::BinaryOp::IntMod,
                        hir::BinaryOp::Less => mir::BinaryOp::IntLess,
                        hir::BinaryOp::Greater => mir::BinaryOp::IntGreater,
                        hir::BinaryOp::LessEq => mir::BinaryOp::IntLessEq,
                        hir::BinaryOp::GreaterEq => mir::BinaryOp::IntGreaterEq,
                        hir::BinaryOp::Eq => mir::BinaryOp::IntEq,
                        hir::BinaryOp::Neq => mir::BinaryOp::IntNeq,
                        hir::BinaryOp::Range => mir::BinaryOp::IntRange,
                        hir::BinaryOp::RangeInclusive => mir::BinaryOp::IntRangeInclusive,
                    },
                    (TyKind::Char, op) => match op {
                        hir::BinaryOp::Eq => mir::BinaryOp::CharEq,
                        hir::BinaryOp::Neq => mir::BinaryOp::CharNeq,
                        _ => unreachable!("char - {op:?}"),
                    },

                    (ty, op) => unreachable!("{ty:?} - {op:?}"),
                };

                let lhs = self.lower(lhs);
                let rhs = self.lower(rhs);

                RValue::BinaryExpr { lhs, op, rhs }
            }
            ExprKind::Ident(ident) => match self.load_ident(*ident) {
                RValue::Use(operand) => RValue::Use(operand),
                rvalue => rvalue,
            },
            ExprKind::FnCall { function, args } => {
                let function = self.lower(*function);
                let args = args.iter().map(|arg| self.lower(*arg)).collect();

                RValue::Call { function, args }
            }
            ExprKind::Break => {
                let block = self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER));
                self.current().breaks.push(block);
                RValue::Use(Operand::Unreachable)
            }
            ExprKind::Index { expr, index } => {
                let lhs = self.lower(*expr);
                let rhs = self.lower(*index);
                let op = if self.hir.exprs[*expr].ty.kind() == &TyKind::Str {
                    if self.hir.exprs[*index].ty.kind() == &TyKind::Range {
                        mir::BinaryOp::StrIndexSlice
                    } else {
                        mir::BinaryOp::StrIndex
                    }
                } else if self.hir.exprs[*index].ty.kind() == &TyKind::Range {
                    mir::BinaryOp::ArrayIndexRange
                } else {
                    mir::BinaryOp::ArrayIndex
                };
                RValue::BinaryExpr { lhs, op, rhs }
            }
            ExprKind::Block(exprs) => self.block_expr(exprs),
        }
    }

    fn get_lvalue_place(&mut self, lvalue: &LValue) -> (Place, bool) {
        match lvalue {
            hir::LValue::Name(name) => (self.bodies.last().unwrap().variables[name], false),
            hir::LValue::Index { indexee, index } => {
                let rhs = self.lower(*index);
                let (place, deref) = self.get_lvalue_place(indexee);
                let new_place = self.new_place();

                let lhs = if deref { Operand::Deref(place) } else { Operand::Place(place) };
                self.current().stmts.push(Statement::Assign {
                    place: new_place,
                    rvalue: RValue::BinaryExpr { lhs, op: mir::BinaryOp::ArrayIndexRef, rhs },
                });
                (new_place, true)
            }
        }
    }

    fn block_expr(&mut self, exprs: &[ExprId]) -> RValue {
        let mut rvalue = None;
        for (i, &expr) in exprs.iter().enumerate() {
            if i == exprs.len() - 1 {
                rvalue = Some(self.lower_inner(expr));
                break;
            }
            self.lower(expr);
        }
        rvalue.unwrap_or(RValue::Use(Operand::UNIT))
    }

    fn load_ident(&self, ident: Symbol) -> RValue {
        if let Some(place) = self.bodies.last().unwrap().variables.get(&ident) {
            return RValue::Use(Operand::Place(*place));
        }
        for body in self.bodies.iter().rev() {
            if let Some(location) = body.functions.get(&ident) {
                return RValue::Use(Operand::Constant(Constant::Func(*location)));
            }
        }
        panic!();
    }

    fn lit_rvalue(&mut self, lit: &Lit) -> RValue {
        match *lit {
            Lit::Unit => RValue::Use(Operand::Constant(Constant::Unit)),
            Lit::Bool(bool) => RValue::Use(Operand::Constant(Constant::Bool(bool))),
            Lit::Int(int) => RValue::Use(Operand::Constant(Constant::Int(int))),
            Lit::Char(char) => RValue::Use(Operand::Constant(Constant::Char(char))),
            Lit::String(str) => RValue::Use(Operand::Constant(Constant::Str(str))),
            Lit::Array { ref segments } => self.lower_array_lit(segments),
            Lit::Abort => RValue::Abort,
        }
    }

    fn lower_array_lit(&mut self, segments: &[ArraySeg]) -> RValue {
        if segments.is_empty() {
            return RValue::Use(Operand::Constant(Constant::EmptyArray));
        }
        let array = self.new_place();
        let throwaway = self.new_place();
        self.current().stmts.push(Statement::Assign {
            place: array,
            rvalue: RValue::Use(Operand::Constant(Constant::EmptyArray)),
        });
        for seg in segments {
            let value = self.lower(seg.expr);
            let repeat = match seg.repeated {
                Some(repeated) => self.lower(repeated),
                None => Operand::Constant(Constant::Int(1)),
            };
            self.current().stmts.push(Statement::Assign {
                place: throwaway,
                rvalue: RValue::Extend { array, value, repeat },
            });
        }
        RValue::Use(Operand::Place(array))
    }
}
