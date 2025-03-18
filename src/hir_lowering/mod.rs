use std::{collections::HashMap, mem};

use crate::{
    hir::{self, ArraySeg, ExprId, ExprKind, Hir, LValue, Lit},
    mir::{
        self, Block, BlockId, Body, BodyId, Constant, Instrinsic, Mir, Operand, Place, RValue,
        Statement, Terminator,
    },
    symbol::Symbol,
};

pub fn lower(hir: &Hir) -> Mir {
    let mut mir = Mir::default();
    let root_body = mir.bodies.push(Body::new(0));
    let bodies = vec![BodyInfo::new(root_body)];

    let mut lowering = Lowering { hir, mir, bodies, last_loop: BlockId::PLACEHOLDER };
    for &expr in &hir.root {
        lowering.lower(expr);
    }
    lowering.mir
}

struct Lowering<'hir> {
    hir: &'hir Hir,
    mir: Mir,
    bodies: Vec<BodyInfo>,
    last_loop: BlockId,
}

struct BodyInfo {
    body: BodyId,
    functions: HashMap<Symbol, BodyId>,
    variables: HashMap<Symbol, Place>,
    current: Vec<Statement>,
}

impl BodyInfo {
    pub fn new(body: BodyId) -> Self {
        Self { body, functions: HashMap::default(), variables: HashMap::default(), current: vec![] }
    }
}

impl Lowering<'_> {
    fn body_ref(&self) -> &Body {
        &self.mir.bodies[self.bodies.last().unwrap().body]
    }
    fn body_mut(&mut self) -> &mut Body {
        &mut self.mir.bodies[self.bodies.last().unwrap().body]
    }
    fn current(&mut self) -> &mut Vec<Statement> {
        &mut self.bodies.last_mut().unwrap().current
    }
    fn finish_with(&mut self, terminator: Terminator) -> BlockId {
        let prev_block = Block { statements: mem::take(self.current()), terminator };
        self.body_mut().blocks.push(prev_block)
    }
    fn finish_next(&mut self) -> BlockId {
        let next_block = self.body_mut().blocks.next_idx() + 1;
        self.finish_with(Terminator::Goto(next_block));
        next_block
    }
    fn new_place(&mut self) -> Place {
        self.body_mut().new_place()
    }

    fn lower(&mut self, id: ExprId) -> Operand {
        match self.lower_inner(id) {
            RValue::Use(operand) => operand,
            rvalue => {
                let place = self.new_place();
                self.current().push(Statement::Assign { place, rvalue });
                Operand::Place(place)
            }
        }
    }

    #[expect(clippy::too_many_lines)]
    fn lower_inner(&mut self, id: ExprId) -> RValue {
        // FIXME: we should return an rvalue and let lower handle whether or not to assign
        let expr = &self.hir.exprs[id];
        match &expr.kind {
            ExprKind::Literal(lit) => self.lit_rvalue(lit),
            ExprKind::Unary { op, expr } => {
                let operand = self.lower(*expr);
                let op = match op {
                    hir::UnaryOp::Not => mir::UnaryOp::Not,
                    hir::UnaryOp::Neg => mir::UnaryOp::Neg,
                };
                RValue::UnaryExpr { op, operand }
            }
            ExprKind::FnDecl(decl) => {
                let hir::FnDecl { ident, params, body, .. } = &**decl;

                assert!(self.current().is_empty(), "TODO");
                let body_id = self.mir.bodies.push(Body::new(params.len()));
                self.bodies.last_mut().unwrap().functions.insert(*ident, body_id);
                self.bodies.push(BodyInfo::new(body_id));
                if self.bodies.len() == 2 && self.try_instrinsic(*ident) {
                } else {
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
                self.bodies.last_mut().unwrap().variables.insert(*ident, place);
                self.current().push(Statement::Assign { place, rvalue });
                RValue::Use(Operand::UNIT)
            }
            ExprKind::Return(expr) => {
                let place = self.lower(*expr);
                self.finish_with(Terminator::Return(place));
                RValue::Use(Operand::UNIT)
            }
            ExprKind::Loop(block) => {
                let loop_block = self.body_ref().blocks.next_idx() + 3;
                // TODO: remove extra blocks
                self.finish_with(Terminator::Goto(loop_block));
                let break_block = self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER));
                self.finish_next();

                let prev_loop = mem::replace(&mut self.last_loop, break_block);
                for &expr in block {
                    self.lower(expr);
                }
                self.last_loop = prev_loop;
                let after_loop = self.finish_with(Terminator::Goto(loop_block)) + 1;
                match &mut self.body_mut().blocks[break_block].terminator {
                    Terminator::Goto(block @ BlockId::PLACEHOLDER) => *block = after_loop,
                    _ => unreachable!(),
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
                    self.current().push(Statement::Assign {
                        place: out_place,
                        rvalue: RValue::Use(block_out),
                    });
                    jump_to_ends.push(self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER)));
                    let current_block = self.body_ref().blocks.next_idx();
                    match &mut self.body_mut().blocks[to_fix].terminator {
                        Terminator::Branch { fals, .. } => *fals = current_block,
                        _ => unreachable!(),
                    }
                }
                for &expr in els {
                    self.lower(expr);
                }
                let current = self.finish_next();
                for block in jump_to_ends {
                    match &mut self.body_mut().blocks[block].terminator {
                        Terminator::Goto(block @ BlockId::PLACEHOLDER) => *block = current,
                        _ => unreachable!(),
                    }
                }
                RValue::Use(Operand::Place(out_place))
            }
            ExprKind::Assignment { lhs, expr } => {
                let rvalue = self.lower_inner(*expr);
                let (place, deref) = self.get_lvalue_place(lhs);
                let stmt = if deref {
                    Statement::DerefAssign { place, rvalue }
                } else {
                    Statement::Assign { place, rvalue }
                };
                self.current().push(stmt);
                RValue::Use(Operand::Constant(Constant::Unit))
            }
            &ExprKind::Binary { lhs, op, rhs } => {
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
                self.finish_with(Terminator::Goto(self.last_loop));
                RValue::Use(Operand::UNIT)
            }
            ExprKind::Index { expr, index } => {
                let indexee = self.lower(*expr);
                let index = self.lower(*index);
                RValue::Index { indexee, index }
            }
            ExprKind::Block(exprs) => RValue::Use(self.block_expr(exprs)),
        }
    }

    fn get_lvalue_place(&mut self, lvalue: &LValue) -> (Place, bool) {
        match lvalue {
            hir::LValue::Name(name) => (self.bodies.last().unwrap().variables[name], false),
            hir::LValue::Index { indexee, index } => {
                let index = self.lower(*index);
                let (place, deref) = self.get_lvalue_place(indexee);
                let new_place = self.new_place();

                let inner_indexee =
                    if deref { Operand::Deref(place) } else { Operand::Place(place) };
                self.current().push(Statement::Assign {
                    place: new_place,
                    rvalue: RValue::IndexRef { indexee: inner_indexee, index },
                });
                (new_place, true)
            }
        }
    }

    fn block_expr(&mut self, exprs: &[ExprId]) -> Operand {
        let mut place = None;
        for &expr in exprs {
            place = Some(self.lower(expr));
        }
        place.unwrap_or(Operand::UNIT)
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
        self.current().push(Statement::Assign {
            place: array,
            rvalue: RValue::Use(Operand::Constant(Constant::EmptyArray)),
        });
        for seg in segments {
            let value = self.lower(seg.expr);
            let repeat = match seg.repeated {
                Some(repeated) => self.lower(repeated),
                None => Operand::Constant(Constant::Int(1)),
            };
            self.current().push(Statement::Assign {
                place: throwaway,
                rvalue: RValue::Extend { array, value, repeat },
            });
        }
        RValue::Use(Operand::Place(array))
    }

    fn try_instrinsic(&mut self, ident: Symbol) -> bool {
        let instrinsic = match ident.as_str() {
            "strlen" => Instrinsic::Strlen(Operand::arg(0)),
            "str_find" => Instrinsic::StrFind(Operand::arg(0), Operand::arg(1)),
            "str_rfind" => Instrinsic::StrRFind(Operand::arg(0), Operand::arg(1)),
            _ => return false,
        };
        let place = self.new_place();
        self.current().push(Statement::Assign { place, rvalue: RValue::Instrinsic(instrinsic) });
        self.finish_with(Terminator::Return(Operand::Place(place)));
        true
    }
}
