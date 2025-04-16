mod intrinsics;

use std::mem;

use index_vec::IndexVec;

use crate::{
    HashMap,
    hir::{self, ArraySeg, ExprId, ExprKind, Hir, Lit},
    mir::{
        self, BinaryOp, Block, BlockId, Body, BodyId, Constant, Local, Mir, Operand, Place,
        Projection, RValue, Statement, Terminator, UnaryOp,
    },
    symbol::Symbol,
    ty::{StructId, Ty, TyKind},
};

pub fn lower(hir: &Hir) -> Mir {
    let mut mir = Mir::default();
    let root_body = mir.bodies.push(Body::new(None, 0).with_auto(true));
    let bodies = vec![BodyInfo::new(root_body)];

    let mut lowering = Lowering { hir, mir, bodies, struct_display_bodies: IndexVec::default() };
    for &expr in &hir.root {
        lowering.lower(expr);
    }
    // TODO: Instead produce an error for any non-body expr in the global scope (probably before type analysis?)
    assert!(lowering.mir.bodies.first().unwrap().blocks.is_empty());
    lowering.mir
}

struct Lowering<'hir, 'tcx> {
    hir: &'hir Hir<'tcx>,
    mir: Mir,
    bodies: Vec<BodyInfo>,
    struct_display_bodies: IndexVec<StructId, Option<BodyId>>,
}

struct BodyInfo {
    body: BodyId,
    functions: HashMap<Symbol, BodyId>,
    variables: HashMap<Symbol, Local>,
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

impl Lowering<'_, '_> {
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

    fn new_local(&mut self) -> Local {
        self.body_mut().new_local()
    }

    fn lower(&mut self, id: ExprId) -> Operand {
        let rvalue = self.lower_inner(id);
        self.process(rvalue, self.hir.exprs[id].ty)
    }

    fn lower_local(&mut self, id: ExprId) -> Local {
        let rvalue = self.lower_inner(id);
        self.process_to_local(rvalue)
    }

    fn process_to_local(&mut self, rvalue: impl Into<RValue>) -> Local {
        match rvalue.into() {
            RValue::Use(Operand::Place(Place { local, projections })) if projections.is_empty() => {
                local
            }
            rvalue => self.assign_new(rvalue),
        }
    }

    fn process_to_place(&mut self, rvalue: impl Into<RValue>) -> Place {
        match rvalue.into() {
            RValue::Use(Operand::Place(place)) => place,
            rvalue => Place::local(self.assign_new(rvalue)),
        }
    }

    fn ref_of(&mut self, rvalue: RValue) -> Operand {
        match rvalue {
            RValue::Use(Operand::Place(place)) => Operand::Ref(place),
            rvalue => {
                let local = self.assign_new(rvalue);
                Operand::Ref(local.into())
            }
        }
    }

    fn process(&mut self, rvalue: RValue, ty: Ty) -> Operand {
        match rvalue {
            RValue::Use(operand) => operand,
            rvalue if ty.is_unit() => {
                let _ = self.assign_new(rvalue);
                Operand::UNIT
            }
            rvalue => Operand::Place(self.assign_new(rvalue).into()),
        }
    }

    fn assign(&mut self, place: impl Into<Place>, rvalue: impl Into<RValue>) {
        let rvalue = rvalue.into();
        let place = place.into();
        self.current().stmts.push(Statement::Assign { place, rvalue });
    }

    #[must_use]
    fn assign_new(&mut self, rvalue: impl Into<RValue>) -> Local {
        let local = self.new_local();
        self.assign(local, rvalue);
        local
    }

    #[expect(clippy::too_many_lines)]
    fn lower_inner(&mut self, id: ExprId) -> RValue {
        let expr = &self.hir.exprs[id];
        let is_unit = expr.ty.is_unit();

        match expr.kind {
            ExprKind::Unreachable => {
                let _ = self.finish_with(Terminator::Unreachable);
                RValue::UNIT
            }
            ExprKind::Abort => {
                let _ = self.finish_with(Terminator::Abort);
                RValue::UNIT
            }
            ExprKind::Field { expr, field } => {
                let local = self.lower_local(expr);
                RValue::Use(Operand::Place(Place {
                    local,
                    projections: vec![Projection::Field(field.try_into().unwrap())],
                }))
            }
            ExprKind::StructInit => {
                let body = self.current().body;
                let nparams = self.mir.bodies[body].params;
                let local =
                    self.assign_new(Constant::UninitStruct { size: nparams.try_into().unwrap() });
                for param in (0..nparams).map(Local::from) {
                    let field = Projection::Field(param.raw().into());
                    self.assign(Place { local, projections: vec![field] }, RValue::local(param));
                }
                RValue::local(local)
            }
            ExprKind::PrintStr(str) => RValue::UnaryExpr {
                op: UnaryOp::Println,
                operand: Operand::Constant(Constant::Str(str)),
            },
            ExprKind::Literal(ref lit) => self.lit_rvalue(lit),
            ExprKind::Unary { op, expr } => 'outer: {
                if let hir::UnaryOp::Ref = op {
                    break 'outer RValue::Use(self.ref_expr(expr));
                } else if let hir::UnaryOp::Deref = op {
                    let rvalue = self.lower_inner(expr);
                    break 'outer RValue::Use(self.deref_operand(rvalue));
                }
                let operand = self.lower(expr);
                let op = match op {
                    hir::UnaryOp::Not => mir::UnaryOp::BoolNot,
                    hir::UnaryOp::Neg => mir::UnaryOp::IntNeg,
                    _ => unreachable!(),
                };
                RValue::UnaryExpr { op, operand }
            }
            ExprKind::FnDecl(ref decl) => {
                let hir::FnDecl { ident, ref params, ref body, .. } = **decl;

                assert!(self.current().stmts.is_empty(), "TODO");
                let body_id = self.mir.bodies.push(Body::new(Some(ident), params.len()));
                self.current().functions.insert(ident, body_id);
                self.bodies.push(BodyInfo::new(body_id));
                if self.bodies.len() == 2 && ident == "main" {
                    self.mir.main_body = Some(body_id);
                }

                if self.bodies.len() == 2 && self.try_instrinsic(ident) {
                    let current = self.current().body;
                    self.mir.bodies[current].auto = true;
                } else {
                    for (i, param) in params.iter().enumerate() {
                        self.current().variables.insert(param.ident, Local::from(i));
                    }
                    let mut last = Operand::UNIT;
                    for &expr in body {
                        last = self.lower(expr);
                    }
                    self.finish_with(Terminator::Return(last));
                }
                self.bodies.pop().unwrap();
                RValue::Use(Operand::UNIT)
            }
            ExprKind::Let { ident, expr } => {
                let rvalue = self.lower_inner(expr);
                let local = self.assign_new(rvalue);
                self.current().variables.insert(ident, local);
                RValue::Use(Operand::UNIT)
            }
            ExprKind::Return(expr) => {
                let place = self.lower(expr);
                self.finish_with(Terminator::Return(place));
                RValue::UNIT
            }
            ExprKind::Loop(ref block) => {
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
            ExprKind::If { ref arms, ref els } => {
                let mut jump_to_ends = Vec::with_capacity(arms.len());
                let out_local = self.new_local();
                for arm in arms {
                    let condition = self.lower(arm.condition);
                    let to_fix = self.finish_with(Terminator::Branch {
                        condition,
                        fals: BlockId::PLACEHOLDER,
                        tru: self.body_ref().blocks.next_idx() + 1,
                    });
                    let block_out = self.block_expr(&arm.body);
                    if is_unit {
                        self.process(block_out, expr.ty);
                    } else {
                        self.assign(out_local, block_out);
                    }
                    jump_to_ends.push(self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER)));
                    let current_block = self.body_ref().blocks.next_idx();
                    match &mut self.body_mut().blocks[to_fix].terminator {
                        Terminator::Branch { fals, .. } => *fals = current_block,
                        _ => unreachable!(),
                    }
                }
                let els_out = self.block_expr(els);
                if is_unit {
                    self.process(els_out, expr.ty);
                } else {
                    self.assign(out_local, els_out);
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
                    RValue::local(out_local)
                }
            }
            ExprKind::Assignment { lhs, expr } => {
                let rvalue = self.lower_inner(expr);
                let place = self.lower_place(lhs);
                self.assign(place, rvalue);
                RValue::Use(Operand::Constant(Constant::Unit))
            }
            ExprKind::Binary { lhs, op, rhs } => {
                let ty = self.hir.exprs[lhs].ty;
                let lhs = self.lower_inner(lhs);
                let rhs = self.lower_inner(rhs);
                self.binary_op(lhs, op, rhs, ty)
            }
            ExprKind::Ident(ident) => match self.load_ident(ident) {
                RValue::Use(operand) => RValue::Use(operand),
                rvalue => rvalue,
            },
            ExprKind::FnCall { function, ref args } => {
                let function = self.lower(function);
                let args = args.iter().map(|arg| self.lower(*arg)).collect();

                match self.try_call_intrinsic(function, args) {
                    Ok(rvalue) | Err(rvalue) => rvalue,
                }
            }
            ExprKind::Break => {
                let block = self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER));
                self.current().breaks.push(block);
                RValue::UNIT
            }
            ExprKind::Index { expr, index } => {
                let op = if self.hir.exprs[expr].ty.is_str() {
                    if self.hir.exprs[index].ty.is_range() {
                        mir::BinaryOp::StrIndexSlice
                    } else {
                        mir::BinaryOp::StrIndex
                    }
                } else if self.hir.exprs[index].ty.is_range() {
                    mir::BinaryOp::ArrayIndexRange
                } else {
                    return self.index_array(expr, index);
                };
                let lhs = self.lower(expr);
                let rhs = self.lower(index);
                RValue::BinaryExpr { lhs, op, rhs }
            }
            ExprKind::Block(ref exprs) => self.block_expr(exprs),
        }
    }

    fn binary_op(&mut self, lhs: RValue, op: hir::BinaryOp, rhs: RValue, ty: Ty) -> RValue {
        let op = match (ty, op) {
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
            (TyKind::Str, op) => match op {
                hir::BinaryOp::Eq => mir::BinaryOp::StrEq,
                hir::BinaryOp::Neq => mir::BinaryOp::StrNeq,
                hir::BinaryOp::Add => mir::BinaryOp::StrAdd,
                _ => unreachable!("str - {op:?}"),
            },
            (TyKind::Ref(of), op) => match op {
                hir::BinaryOp::Eq => {
                    let lhs = self.deref_operand(lhs);
                    let rhs = self.deref_operand(rhs);
                    return self.binary_op(lhs.into(), op, rhs.into(), of);
                }
                _ => unreachable!("ref {of:?} - {op:?}"),
            },

            (ty, op) => unreachable!("{ty:?} - {op:?}"),
        };
        let lhs = self.process(lhs, ty);
        let rhs = self.process(rhs, ty);
        RValue::BinaryExpr { lhs, op, rhs }
    }

    fn index_array(&mut self, expr: ExprId, index: ExprId) -> RValue {
        let expr_ty = self.hir.exprs[expr].ty;

        let expr = self.lower_inner(expr);
        let expr = self.array_index_derefs(expr, expr_ty);
        let mut place = self.process_to_place(expr);
        let index_local = self.lower_local(index);
        place.projections.push(Projection::Index(index_local));
        RValue::Use(Operand::Place(place))
    }

    fn array_index_derefs(&mut self, mut rvalue: RValue, mut ty: Ty) -> RValue {
        loop {
            match ty {
                TyKind::Array(_) => return rvalue,
                TyKind::Ref(of) => {
                    ty = of;
                    rvalue = RValue::Use(self.deref_operand(rvalue));
                }
                _ => unreachable!(),
            }
        }
    }

    fn lower_place(&mut self, expr: hir::ExprId) -> Place {
        let mut projections = vec![];
        let local = self.lower_place_inner(expr, &mut projections);
        Place { local, projections }
    }

    fn lower_place_inner(&mut self, expr: hir::ExprId, proj: &mut Vec<Projection>) -> Local {
        match self.hir.exprs[expr].kind {
            ExprKind::Ident(ident) => self.current().variables[&ident],
            ExprKind::Index { expr, index } => {
                let index_local = self.lower_local(index);
                let local = self.lower_place_inner(expr, proj);
                proj.push(Projection::Index(index_local));
                local
            }
            ExprKind::Unary { op: hir::UnaryOp::Deref, expr } => {
                let local = self.lower_place_inner(expr, proj);
                proj.push(Projection::Deref);
                local
            }
            ExprKind::Unary { op: hir::UnaryOp::Ref, expr } => {
                let rvalue = self.ref_expr(expr);
                self.process_to_local(rvalue)
            }
            ExprKind::Field { expr, field } => {
                let field = field.try_into().unwrap();
                let local = self.lower_place_inner(expr, proj);
                proj.push(Projection::Field(field));
                local
            }
            _ => {
                let expr = self.lower_inner(expr);
                self.process_to_local(expr)
            }
        }
    }

    fn ref_expr(&mut self, expr: hir::ExprId) -> Operand {
        let mut place = self.lower_place(expr);
        if place.projections.last() == Some(&Projection::Deref) {
            place.projections.pop();
            Operand::Place(place)
        } else {
            Operand::Ref(place)
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
            return RValue::Use(Operand::local(*place));
        }
        let Some(location) = self.bodies.iter().rev().find_map(|body| body.functions.get(&ident))
        else {
            panic!("{ident}");
        };
        RValue::Use(Operand::Constant(Constant::Func(*location)))
    }

    fn lit_rvalue(&mut self, lit: &Lit) -> RValue {
        match *lit {
            Lit::Unit => RValue::Use(Operand::Constant(Constant::Unit)),
            Lit::Bool(bool) => RValue::Use(Operand::Constant(Constant::Bool(bool))),
            Lit::Int(int) => RValue::Use(Operand::Constant(Constant::Int(int))),
            Lit::Char(char) => RValue::Use(Operand::Constant(Constant::Char(char))),
            Lit::String(str) => RValue::Use(Operand::Constant(Constant::Str(str))),
            Lit::Array { ref segments } => self.lower_array_lit(segments),
            Lit::FStr { ref segments } => self.lower_fstrings(segments),
        }
    }

    fn lower_array_lit(&mut self, segments: &[ArraySeg]) -> RValue {
        if segments.is_empty() {
            return RValue::Use(Operand::Constant(Constant::EmptyArray { cap: 0 }));
        }
        let throwaway = self.new_local();

        let cap = {
            segments
                .iter()
                .map(|seg| match seg.repeated {
                    None => 1,
                    Some(expr) => match self.hir.exprs[expr].kind {
                        ExprKind::Literal(Lit::Int(int)) => int.try_into().unwrap(),
                        _ => 1,
                    },
                })
                .sum()
        };

        let array = self.assign_new(Constant::EmptyArray { cap });
        for seg in segments {
            let value = self.lower(seg.expr);
            let repeat = match seg.repeated {
                Some(repeated) => self.lower(repeated),
                None => Operand::Constant(Constant::Int(1)),
            };
            self.assign(throwaway, RValue::Extend { array, value, repeat });
        }
        RValue::local(array)
    }

    fn lower_fstrings(&mut self, segments: &[ExprId]) -> RValue {
        if let [single] = *segments {
            return self.format_expr(single);
        }

        let builder = self.assign_new(Constant::EmptyArray { cap: segments.len() as _ });
        for &segment in segments {
            let segment_str = self.format_expr(segment);
            let rhs = self.process(segment_str, self.hir.exprs[segment].ty);
            self.process(
                RValue::BinaryExpr {
                    lhs: Operand::Ref(Place::local(builder)),
                    op: mir::BinaryOp::ArrayPush,
                    rhs,
                },
                &TyKind::Unit,
            );
        }
        RValue::UnaryExpr { op: UnaryOp::StrJoin, operand: Operand::local(builder) }
    }

    fn format_expr(&mut self, id: ExprId) -> RValue {
        let expr = &self.hir.exprs[id];
        let rvalue = self.lower_inner(id);
        self.format_rvalue(rvalue, expr.ty)
    }

    fn format_rvalue(&mut self, rvalue: RValue, ty: Ty) -> RValue {
        if ty.is_str() {
            return rvalue;
        }
        if let TyKind::Ref(_) = ty {
            return self.format_ref(rvalue, ty);
        }
        let operand = self.process(rvalue, ty);
        match ty {
            TyKind::Infer(_) | TyKind::Str => unreachable!(),
            TyKind::Never => RValue::from(Constant::Str("!".into())),
            TyKind::Unit => RValue::from(Constant::Str("()".into())),
            TyKind::Bool => RValue::UnaryExpr { op: UnaryOp::BoolToStr, operand },
            TyKind::Int => RValue::UnaryExpr { op: UnaryOp::IntToStr, operand },
            TyKind::Char => RValue::UnaryExpr { op: UnaryOp::CharToStr, operand },
            TyKind::Struct { id, symbols, fields } => {
                self.format_struct(*id, symbols, fields, operand)
            }
            _ => todo!("{}.to_string()", ty),
        }
    }

    fn deref_operand(&mut self, rvalue: RValue) -> Operand {
        match rvalue {
            RValue::Use(Operand::Place(mut place)) => {
                place.projections.push(Projection::Deref);
                Operand::Place(place)
            }
            RValue::Use(Operand::Ref(place)) => Operand::Place(place),
            _ => {
                let local = self.assign_new(rvalue);
                Operand::Place(Place { local, projections: vec![Projection::Deref] })
            }
        }
    }

    fn format_ref(&mut self, mut rvalue: RValue, mut ty: Ty) -> RValue {
        while let TyKind::Ref(of) = ty {
            rvalue = RValue::Use(self.deref_operand(rvalue));
            ty = of;
        }
        self.format_rvalue(rvalue, ty)
    }

    fn format_struct(
        &mut self,
        id: StructId,
        symbols: &[Symbol],
        fields: &[Ty],
        val: Operand,
    ) -> RValue {
        // TODO: This should pass the struct by ref
        let body = self.generate_struct_func(id, symbols, fields);
        let ref_struct = self.ref_of(RValue::Use(val));
        RValue::Call {
            function: Operand::Constant(Constant::Func(body)),
            args: [ref_struct].into(),
        }
    }

    fn generate_struct_func(&mut self, id: StructId, symbols: &[Symbol], fields: &[Ty]) -> BodyId {
        _ = symbols;
        let previous = self.bodies.pop().unwrap(); // TODO: We should pop till further up
        let body_id = self.mir.bodies.push(Body::new(None, 1).with_auto(false));
        self.bodies.push(BodyInfo::new(body_id));
        let local = Local::from(0);

        // segments + seperators + open/close brackets
        let num_parts = fields.len() + fields.len().saturating_sub(1) + 2;

        let strings = self.assign_new(Constant::EmptyArray { cap: num_parts });

        self.process(
            RValue::BinaryExpr {
                lhs: Operand::Ref(strings.into()),
                op: BinaryOp::ArrayPush,
                rhs: Operand::Constant(Constant::Str("(".into())),
            },
            &TyKind::Unit,
        );

        for (i, ty) in (0u32..).zip(fields) {
            if i != 0 {
                self.process(
                    RValue::BinaryExpr {
                        lhs: Operand::Ref(strings.into()),
                        op: BinaryOp::ArrayPush,
                        rhs: Operand::Constant(Constant::Str(", ".into())),
                    },
                    &TyKind::Unit,
                );
            }

            let projections = vec![Projection::Deref, Projection::Field(i as _)];
            let field = RValue::Use(Operand::Place(Place { local, projections }));
            let field_str = self.format_rvalue(field, ty);
            let rhs = self.process(field_str, &TyKind::Str);
            self.process(
                RValue::BinaryExpr {
                    lhs: Operand::Ref(strings.into()),
                    op: BinaryOp::ArrayPush,
                    rhs,
                },
                &TyKind::Unit,
            );
        }

        self.process(
            RValue::BinaryExpr {
                lhs: Operand::Ref(strings.into()),
                op: BinaryOp::ArrayPush,
                rhs: Operand::Constant(Constant::Str(")".into())),
            },
            &TyKind::Unit,
        );

        let out = self.assign_new(RValue::UnaryExpr {
            op: UnaryOp::StrJoin,
            operand: Operand::local(strings),
        });
        self.finish_with(Terminator::Return(Operand::local(out)));

        if self.struct_display_bodies.len() <= id {
            self.struct_display_bodies.resize(id.index() + 1, None);
        }
        self.struct_display_bodies[id] = Some(body_id);

        self.bodies.pop();
        self.bodies.push(previous);
        body_id
    }
}
