mod intrinsics;
mod loops;
mod pattern;

use std::{collections::VecDeque, mem};

use arcstr::ArcStr;
use index_vec::IndexVec;

use crate::{
    HashMap, errors,
    hir::{self, ArraySeg, ExprId, ExprKind, FnDecl, Hir, Lit, OpAssign, Path, UseKind},
    mir::{
        self, BinaryOp, Block, BlockId, Body, BodyId, Constant, Local, Mir, Operand, Place,
        Projection, RValue, Statement, Terminator, UnaryOp,
    },
    scope::{Global, ModuleId},
    source::span::Span,
    symbol::Symbol,
    ty::{self, GenericId, Struct, StructId, Ty, TyCtx, TyKind},
};

#[derive(Clone, Copy)]
enum Var {
    Local(Local),
    Func(hir::BodyId),
}

pub fn lower<'tcx>(hir: &Hir<'tcx>, tcx: &'tcx TyCtx<'tcx>) -> Mir {
    let mut mir = Mir::default();
    let root_body = mir.bodies.push(Body::new(None, 0).with_auto(true));

    let mut lowering = Lowering {
        tcx,
        hir,
        mir,
        scopes: Global::new(BodyInfo::new(root_body)),
        struct_display_bodies: IndexVec::default(),
        array_display_bodies: HashMap::default(),
        strings: HashMap::default(),
        generic_fns: HashMap::default(),
        non_generic_fns: HashMap::default(),
        mono_generics: VecDeque::default(),
        generic_map: None,
    };
    for &expr in &hir.root {
        lowering.lower(expr);
    }
    lowering.monomorphization();
    assert!(lowering.mir.bodies.first().unwrap().blocks.is_empty());
    lowering.mir
}

struct Lowering<'hir, 'tcx> {
    tcx: &'tcx TyCtx<'tcx>,
    hir: &'hir Hir<'tcx>,
    mir: Mir,
    scopes: Global<BodyInfo, Var, ()>,
    struct_display_bodies: IndexVec<StructId, Option<BodyId>>,
    array_display_bodies: HashMap<Ty<'tcx>, BodyId>,
    strings: HashMap<Symbol, ArcStr>,
    generic_fns: HashMap<hir::BodyId, GenericFns<'tcx, 'hir>>,
    non_generic_fns: HashMap<hir::BodyId, mir::BodyId>,
    mono_generics: VecDeque<(&'hir hir::FnDecl<'tcx>, &'tcx ty::Function<'tcx>, BodyId)>,
    generic_map: Option<HashMap<GenericId, Ty<'tcx>>>,
}

#[derive(Debug)]
struct GenericFns<'tcx, 'hir> {
    decl: &'hir hir::FnDecl<'tcx>,
    impls: HashMap<&'tcx ty::Function<'tcx>, BodyId>,
}

macro_rules! str {
    ($s: literal) => {
        Constant::Str(arcstr::literal!($s)).into()
    };
    ($self:expr, $s: ident) => {
        Constant::Str($self.strings.entry($s).or_insert($s.as_str().into()).clone()).into()
    };
}

struct BodyInfo {
    id: BodyId,
    stmts: Vec<Statement>,
    breaks: Vec<BlockId>,
    continue_block: Option<BlockId>,
}

impl BodyInfo {
    pub fn new(id: BodyId) -> Self {
        Self { id, stmts: vec![], breaks: vec![], continue_block: None }
    }
}

impl<'tcx> Lowering<'_, 'tcx> {
    fn ty(&self, id: ExprId) -> Ty<'tcx> {
        self.mono(self.hir.exprs[id].ty)
    }
    fn mono(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        match ty.0 {
            TyKind::Generic(id) => self.generic_map.as_ref().unwrap()[id],
            TyKind::Array(of) => self.tcx.intern(TyKind::Array(self.mono(*of))),
            TyKind::Function(ty::Function { params, ret }) => {
                let params = params.iter().map(|param| self.mono(*param)).collect();
                let ret = self.mono(*ret);
                self.tcx.intern(TyKind::Function(ty::Function { params, ret }))
            }
            TyKind::Ref(of) => self.tcx.intern(TyKind::Ref(self.mono(*of))),
            // TyKind::Struct { .. } => todo!(),
            _ => ty,
        }
    }

    fn insert_local(&mut self, ident: Symbol, local: Local) {
        self.scopes.scope_mut().insert(ident, Var::Local(local));
    }
    fn insert_func(&mut self, ident: Symbol, func: hir::BodyId) {
        self.scopes.scope_mut().insert(ident, Var::Func(func));
    }

    fn body_ref(&self) -> &Body {
        &self.mir.bodies[self.current().id]
    }
    fn body_mut(&mut self) -> &mut Body {
        &mut self.mir.bodies[self.scopes.body().id]
    }

    fn current(&self) -> &BodyInfo {
        self.scopes.body()
    }
    fn current_mut(&mut self) -> &mut BodyInfo {
        self.scopes.body_mut()
    }

    fn finish_with(&mut self, terminator: Terminator) -> BlockId {
        let prev_block = Block { statements: mem::take(&mut self.current_mut().stmts), terminator };
        self.body_mut().blocks.push(prev_block)
    }

    fn current_block(&self) -> BlockId {
        self.body_ref().blocks.next_idx()
    }

    fn finish_next(&mut self) {
        let next_block = self.current_block() + 1;
        self.finish_with(Terminator::Goto(next_block));
    }

    fn new_local(&mut self) -> Local {
        self.body_mut().new_local()
    }

    fn lower(&mut self, id: ExprId) -> Operand {
        let rvalue = self.lower_rvalue(id);
        self.process(rvalue, self.ty(id))
    }

    fn lower_local(&mut self, id: ExprId) -> Local {
        let rvalue = self.lower_rvalue(id);
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

    fn ref_of(&mut self, rvalue: impl Into<RValue>) -> Operand {
        match rvalue.into() {
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
        self.current_mut().stmts.push(Statement::Assign { place, rvalue });
    }

    fn assign_new(&mut self, rvalue: impl Into<RValue>) -> Local {
        let local = self.new_local();
        self.assign(local, rvalue);
        local
    }

    fn lower_rvalue(&mut self, id: ExprId) -> RValue {
        let pushed_scope = match self.hir.exprs[id].kind {
            ExprKind::Use(..)
            | ExprKind::Module(..)
            | ExprKind::Match { new_scope: false, .. }
            | ExprKind::Block(..)
            | ExprKind::Let { .. }
            | ExprKind::FnDecl(..) => None,
            _ => Some(self.scopes.push_scope()),
        };
        let rvalue = self.lower_rvalue_unscoped(id);
        if let Some(scope) = pushed_scope {
            self.scopes.pop_scope(scope);
        }
        rvalue
    }

    #[expect(clippy::too_many_lines)]
    fn lower_rvalue_unscoped(&mut self, id: ExprId) -> RValue {
        let is_unit = self.ty(id).is_unit();

        match self.hir.exprs[id].kind {
            ExprKind::Use(ref use_) => {
                self.lower_use(use_, self.scopes.current);
                RValue::UNIT
            }
            ExprKind::Module(name, ref body) => {
                let body_id = self.mir.bodies.push(Body::new(None, 0).with_auto(true));
                let module_token = self.scopes.push_module(name, BodyInfo::new(body_id)).0;
                for &expr in body {
                    self.lower(expr);
                }
                self.scopes.pop_module(module_token);
                RValue::UNIT
            }
            ExprKind::ForLoop { ident, iter, ref body } => {
                match self.ty(iter).0 {
                    TyKind::Range => self.range_for(ident, iter, body),
                    TyKind::Array(..) => self.array_for(ident, iter, body),
                    _ => unreachable!(),
                }
                RValue::UNIT
            }
            ExprKind::Unreachable => {
                let _ = self.finish_with(Terminator::Unreachable);
                RValue::UNIT
            }
            ExprKind::Abort { msg } => {
                let _ = self.finish_with(Terminator::Abort { msg });
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
                let body = self.current_mut().id;
                let nparams = self.mir.bodies[body].params;
                let local =
                    self.assign_new(Constant::UninitStruct { size: nparams.try_into().unwrap() });
                for param in (0..nparams).map(Local::from) {
                    let field = Projection::Field(param.raw().into());
                    self.assign(Place { local, projections: vec![field] }, RValue::local(param));
                }
                RValue::local(local)
            }
            ExprKind::Literal(ref lit) => self.lit_rvalue(lit),
            ExprKind::FnDecl(ref decl) => {
                let hir::FnDecl { ident, for_ty, ref params, ref body, id: hir_id, .. } = **decl;

                assert!(self.current_mut().stmts.is_empty(), "TODO");

                let is_generic = decl.is_generic();

                let body_id = self
                    .mir
                    .bodies
                    .push(Body::new(Some(ident), params.len()).with_auto(is_generic));

                if is_generic {
                    self.generic_fns.insert(hir_id, GenericFns { decl, impls: HashMap::default() });
                } else {
                    self.non_generic_fns.insert(hir_id, body_id);
                }

                match for_ty {
                    Some(_) => {}
                    None => self.insert_func(ident, hir_id),
                }

                if is_generic {
                    return RValue::UNIT;
                }

                let body_token = self.scopes.push_body(BodyInfo::new(body_id));
                if self.scopes.bodies.len() == 2 && ident == "main" {
                    self.mir.main_body = Some(body_id);
                }

                if self.scopes.bodies.len() == 2 && self.try_intrinsic(for_ty, ident) {
                    let current = self.current().id;
                    self.mir.bodies[current].auto = true;
                } else {
                    for (i, param) in params.iter().enumerate() {
                        self.insert_local(param.ident, Local::from(i));
                    }
                    let mut last = Operand::UNIT;
                    for &expr in body {
                        last = self.lower(expr);
                    }
                    self.finish_with(Terminator::Return(last));
                }
                self.scopes.pop_body(body_token);
                RValue::UNIT
            }
            ExprKind::Let { ident, expr } => {
                let rvalue = self.lower_rvalue(expr);
                let local = self.assign_new(rvalue);
                self.insert_local(ident, local);
                RValue::UNIT
            }
            ExprKind::Return(expr) => {
                let place = self.lower(expr);
                self.finish_with(Terminator::Return(place));
                RValue::UNIT
            }
            ExprKind::Loop(expr) => {
                self.lower_loop(|_| None, |lower| _ = lower.lower(expr));
                RValue::UNIT
            }
            ExprKind::Match { scrutinee, ref arms, .. } => self.lower_match(scrutinee, arms),
            ExprKind::If { ref arms, els } => {
                let mut jump_to_ends = Vec::with_capacity(arms.len());
                let out_local = self.new_local();
                for arm in arms {
                    let condition = self.lower(arm.condition);
                    let to_fix = self.finish_with(Terminator::Branch {
                        condition,
                        fals: BlockId::PLACEHOLDER,
                        tru: self.current_block() + 1,
                    });
                    let block_out = self.block_expr(&arm.body);
                    if is_unit {
                        self.process(block_out, self.ty(id));
                    } else {
                        self.assign(out_local, block_out);
                    }
                    jump_to_ends.push(self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER)));
                    let current_block = self.current_block();
                    self.body_mut().blocks[to_fix].terminator.complete(current_block);
                }
                if let Some(els) = els {
                    let els_out = self.lower_rvalue(els);
                    if is_unit {
                        self.process(els_out, self.ty(id));
                    } else {
                        self.assign(out_local, els_out);
                    }
                }

                self.finish_next();
                let current = self.current_block();
                for block in jump_to_ends {
                    self.body_mut().blocks[block].terminator.complete(current);
                }
                if is_unit { RValue::UNIT } else { RValue::local(out_local) }
            }
            ExprKind::Assignment { lhs, expr } => {
                let rvalue = self.lower_rvalue(expr);
                let place = self.lower_place(lhs);
                self.assign(place, rvalue);
                RValue::UNIT
            }
            ExprKind::Binary { lhs, op, rhs } => self.binary_op(lhs, op, rhs),
            ExprKind::Unary { op, expr } => self.unary_op(op, expr),
            ExprKind::OpAssign { place, op, expr } => self.op_assign(place, op, expr),
            ExprKind::Path(ref path) => self.load_path(path, self.ty(id)),
            ExprKind::Func(body) => self.load_func(body, self.ty(id)),
            ExprKind::FnCall { function, ref args } => {
                let function = self.lower(function);

                let args = args.iter().map(|arg| self.lower(*arg)).collect();

                match self.try_call_intrinsic(function, None, args) {
                    Ok(rvalue) | Err(rvalue) => rvalue,
                }
            }
            ExprKind::Break => {
                let block = self.finish_with(Terminator::Goto(BlockId::PLACEHOLDER));
                self.current_mut().breaks.push(block);
                RValue::UNIT
            }
            ExprKind::Continue => {
                self.finish_with(Terminator::Goto(self.current().continue_block.unwrap()));
                RValue::UNIT
            }
            ExprKind::Index { expr, index, span } => {
                let index_ty = self.ty(index);
                let op = if self.ty(expr).is_str() {
                    if index_ty.is_range() {
                        mir::BinaryOp::StrIndexSlice
                    } else {
                        mir::BinaryOp::StrIndex
                    }
                } else if index_ty.is_range() {
                    mir::BinaryOp::ArrayIndexRange
                } else {
                    return self.index_array(expr, index, span);
                };
                let lhs = self.lower(expr);
                let rhs = self.lower(index);
                RValue::Binary { lhs, op, rhs }
            }
            ExprKind::Block(ref exprs) => self.block_expr(exprs),
        }
    }

    fn mono_fn(&mut self, ident: Symbol, location: hir::BodyId, ty: Ty<'tcx>) -> RValue {
        let Some(generic_fns) = self.generic_fns.get_mut(&location) else {
            return RValue::from(Constant::Func(self.non_generic_fns[&location]));
        };

        let TyKind::Function(fn_ty) = ty.0 else { unreachable!("{}", self.tcx.display(ty)) };
        let params = fn_ty.params.len();

        let mut new = false;
        let monomorphized_location = *generic_fns.impls.entry(fn_ty).or_insert_with(|| {
            new = true;
            self.mir.bodies.push(Body::new(Some(ident), params))
        });
        if new {
            self.mono_generics.push_back((generic_fns.decl, fn_ty, monomorphized_location));
        }

        RValue::from(Constant::Func(monomorphized_location))
    }

    fn unary_op(&mut self, op: crate::ast::UnaryOp, expr: ExprId) -> RValue {
        match op {
            hir::UnaryOp::Ref => RValue::Use(self.ref_expr(expr)),
            hir::UnaryOp::Deref => {
                let rvalue = self.lower_rvalue(expr);
                RValue::Use(self.deref_operand(rvalue))
            }
            hir::UnaryOp::Not => RValue::Unary { op: UnaryOp::BoolNot, operand: self.lower(expr) },
            hir::UnaryOp::Neg => RValue::Unary { op: UnaryOp::IntNeg, operand: self.lower(expr) },
        }
    }

    fn binary_op(&mut self, lhs: ExprId, op: hir::BinaryOp, rhs: ExprId) -> RValue {
        let lhs_ty = self.ty(lhs);
        let rhs_ty = self.ty(rhs);
        if let hir::BinaryOp::And | hir::BinaryOp::Or = op {
            return self.logical_op(op, lhs, rhs);
        }

        let lhs = self.lower_rvalue(lhs);
        let rhs = self.lower_rvalue(rhs);

        self.binary_op_inner((lhs, lhs_ty), op, (rhs, rhs_ty))
    }

    fn binary_op_inner(
        &mut self,
        (lhs, lhs_ty): (RValue, Ty<'tcx>),
        op: hir::BinaryOp,
        (rhs, rhs_ty): (RValue, Ty<'tcx>),
    ) -> RValue {
        let (lhs, lhs_ty) = self.fully_deref(lhs, lhs_ty);
        let (rhs, rhs_ty) = self.fully_deref(rhs, rhs_ty);

        let op = Self::get_binary_op(lhs_ty, op);
        let lhs = self.process(lhs, lhs_ty);
        let rhs = self.process(rhs, rhs_ty);
        RValue::Binary { lhs, op, rhs }
    }

    fn get_binary_op(ty: Ty, op: hir::BinaryOp) -> BinaryOp {
        match (ty.0, op) {
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
                _ => unreachable!(),
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
            (TyKind::Bool, op) => match op {
                hir::BinaryOp::Eq => mir::BinaryOp::BoolEq,
                hir::BinaryOp::Neq => mir::BinaryOp::BoolNeq,
                _ => unreachable!("bool - {op:?}"),
            },
            (ty, op) => unreachable!("{ty:?} - {op:?}",),
        }
    }

    fn logical_op(&mut self, op: hir::BinaryOp, lhs: ExprId, rhs: ExprId) -> RValue {
        let lhs_ty = self.ty(lhs);
        let rhs_ty = self.ty(rhs);

        let output = self.new_local();

        let lhs = self.lower_rvalue(lhs);
        let (lhs, _) = self.fully_deref(lhs, lhs_ty);
        self.assign(output, lhs);

        let next = self.current_block() + 1;
        let condition = Operand::local(output);
        let terminator = match op {
            hir::BinaryOp::And => {
                Terminator::Branch { condition, fals: BlockId::PLACEHOLDER, tru: next }
            }
            hir::BinaryOp::Or => {
                Terminator::Branch { condition, fals: next, tru: BlockId::PLACEHOLDER }
            }
            _ => unreachable!(),
        };
        let to_fix = self.finish_with(terminator);

        let rhs = self.lower_rvalue(rhs);
        let (rhs, _) = self.fully_deref(rhs, rhs_ty);
        self.assign(output, rhs);
        self.finish_next();

        let current_block = self.current_block();

        self.body_mut().blocks[to_fix].terminator.complete(current_block);
        RValue::local(output)
    }

    fn op_assign(&mut self, place: ExprId, op: OpAssign, expr: ExprId) -> RValue {
        let place_ty = self.ty(place);

        let operand = self.lower(expr);
        let place = self.lower_place(place);
        let op = Self::get_binary_op(place_ty, op.into());
        let rvalue = RValue::Binary { lhs: Operand::Place(place.clone()), op, rhs: operand };
        self.assign(place, rvalue);
        RValue::UNIT
    }

    fn fully_deref(&mut self, rvalue: impl Into<RValue>, mut ty: Ty<'tcx>) -> (RValue, Ty<'tcx>) {
        let mut rvalue = rvalue.into();
        while let TyKind::Ref(of) = ty.0 {
            rvalue = self.deref_operand(rvalue).into();
            ty = *of;
        }
        (rvalue, ty)
    }

    fn index_array(&mut self, expr: ExprId, index: ExprId, span: Span) -> RValue {
        let expr_ty = self.ty(expr);
        let index_ty = self.ty(index);

        let expr = self.lower_rvalue(expr);
        let (expr, _) = self.fully_deref(expr, expr_ty);
        let mut place = self.process_to_place(expr);
        let index_local = self.lower_local(index);

        self.bounds_check((index_local, index_ty), (place.clone(), index_ty), span);

        let projection = match self.hir.exprs[index].kind {
            ExprKind::Literal(Lit::Int(int)) if u32::try_from(int).is_ok() => {
                Projection::ConstantIndex(int.try_into().unwrap())
            }
            _ => Projection::Index(index_local),
        };
        place.projections.push(projection);
        RValue::Use(Operand::Place(place))
    }

    fn bounds_check(
        &mut self,
        (index, index_ty): (Local, Ty<'tcx>),
        (rhs, rhs_ty): (Place, Ty<'tcx>),
        span: Span,
    ) {
        let array_len =
            self.assign_new(RValue::Unary { op: UnaryOp::ArrayLen, operand: Operand::Ref(rhs) });
        let binary_op = self.binary_op_inner(
            (RValue::local(index), index_ty),
            hir::BinaryOp::GreaterEq,
            (RValue::local(array_len), rhs_ty),
        );
        let condition = self.process(binary_op, Ty::BOOL);
        let next = self.current_block() + 1;
        let to_fix = self.finish_with(Terminator::Branch {
            condition,
            fals: BlockId::PLACEHOLDER,
            tru: next,
        });

        let error_report = errors::error("index out of bounds", [(span, "index out of bounds")]);
        let error_str = format!("{error_report:?}").into();
        self.finish_with(Terminator::Abort { msg: error_str });

        let current = self.current_block();
        self.body_mut().blocks[to_fix].terminator.complete(current);
    }

    fn read_path(&self, path: &Path) -> Local {
        let Some(ident) = path.single() else { panic!() };
        self.read_ident(ident)
    }

    fn read_ident(&self, ident: Symbol) -> Local {
        if let Var::Local(local) = self.scopes.get(ident).unwrap() { *local } else { panic!() }
    }

    fn lower_place(&mut self, expr: hir::ExprId) -> Place {
        let mut projections = vec![];
        let local = self.lower_place_inner(expr, &mut projections);
        Place { local, projections }
    }

    fn lower_place_inner(&mut self, expr: hir::ExprId, proj: &mut Vec<Projection>) -> Local {
        match self.hir.exprs[expr].kind {
            ExprKind::Path(ref path) => self.read_path(path),
            ExprKind::Index { expr, index, span } => {
                let index_rvalue = self.lower_rvalue(index);

                let const_index = match index_rvalue {
                    RValue::Use(Operand::Constant(Constant::Int(int))) => {
                        Some(int.try_into().unwrap())
                    }
                    _ => None,
                };
                let index_local = self.process_to_local(index_rvalue);

                let local = self.lower_place_inner(expr, proj);
                let mut expr_ty = self.ty(expr);
                while let TyKind::Ref(of) = expr_ty.0 {
                    expr_ty = *of;
                    proj.push(Projection::Deref);
                }

                self.bounds_check(
                    (index_local, self.ty(index)),
                    (Place { local, projections: proj.clone() }, expr_ty),
                    span,
                );

                let projection = match const_index {
                    Some(index) => Projection::ConstantIndex(index),
                    _ => Projection::Index(index_local),
                };
                proj.push(projection);
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
                let expr = self.lower_rvalue(expr);
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
        let scope_token = self.scopes.push_scope();
        let mut rvalue = None;
        for (i, &expr) in exprs.iter().enumerate() {
            if i == exprs.len() - 1 {
                rvalue = Some(self.lower_rvalue(expr));
            } else {
                self.lower(expr);
            }
        }
        self.scopes.pop_scope(scope_token);
        rvalue.unwrap_or(RValue::UNIT)
    }

    fn load_path(&mut self, path: &Path, ty: Ty<'tcx>) -> RValue {
        match *self.scopes.get_path(&path.segments).unwrap().unwrap() {
            Var::Local(local) => RValue::local(local),
            Var::Func(location) => self.mono_fn(path.last(), location, ty),
        }
    }

    fn load_func(&mut self, body: hir::BodyId, ty: Ty<'tcx>) -> RValue {
        self.mono_fn("".into(), body.index().into(), ty)
    }

    fn lit_rvalue(&mut self, lit: &Lit) -> RValue {
        match *lit {
            Lit::Unit => RValue::UNIT,
            Lit::Bool(bool) => RValue::from(Constant::Bool(bool)),
            Lit::Int(int) => RValue::from(Constant::Int(int)),
            Lit::Char(char) => RValue::from(Constant::Char(char)),
            Lit::String(str) => str!(self, str),
            Lit::Array { ref segments } => self.lower_array_lit(segments),
            Lit::FStr { ref segments } => self.lower_fstrings(segments),
        }
    }

    fn lower_array_lit(&mut self, segments: &[ArraySeg]) -> RValue {
        if segments.is_empty() {
            return RValue::from(Constant::EmptyArray { cap: 0 });
        }

        let mut mir_segments = Vec::with_capacity(segments.len());
        for hir::ArraySeg { expr, repeated } in segments {
            let elem = self.lower(*expr);
            let repeated = repeated.map(|repeat| self.lower(repeat));
            mir_segments.push((elem, repeated));
        }
        RValue::BuildArray(mir_segments)
    }

    fn lower_fstrings(&mut self, segments: &[ExprId]) -> RValue {
        if let [single] = *segments {
            return self.format_expr(single);
        }

        let mut mir_segments = vec![];
        for &segment in segments {
            let seg_rvalue = self.format_expr(segment);
            mir_segments.push(self.process(seg_rvalue, Ty::STR));
        }
        RValue::StrJoin(mir_segments)
    }

    fn format_expr(&mut self, id: ExprId) -> RValue {
        let rvalue = self.lower_rvalue(id);
        self.format_rvalue(rvalue, self.ty(id))
    }

    fn format_rvalue(&mut self, rvalue: impl Into<RValue>, ty: Ty<'tcx>) -> RValue {
        let (rvalue, ty) = self.fully_deref(rvalue, ty);

        if ty.is_str() {
            return rvalue;
        }

        let operand = self.process(rvalue, ty);

        match ty.0 {
            TyKind::Poison
            | TyKind::Generic(_)
            | TyKind::Ref(_)
            | TyKind::Infer(_)
            | TyKind::Str => {
                unreachable!("{ty:?}");
            }
            TyKind::Never => str!("!"),
            TyKind::Unit => str!("()"),
            TyKind::Bool => RValue::Unary { op: UnaryOp::BoolToStr, operand },
            TyKind::Int => RValue::Unary { op: UnaryOp::IntToStr, operand },
            TyKind::Char => RValue::Unary { op: UnaryOp::CharToStr, operand },
            TyKind::Range => RValue::Unary { op: UnaryOp::RangeToStr, operand },
            TyKind::Struct(strct) => self.format_struct(strct, operand),
            TyKind::Array(of) => self.format_array(*of, operand),
            TyKind::Function(..) => {
                RValue::from(Constant::Str(self.tcx.display(ty).to_string().into()))
            }
        }
    }

    fn deref_operand(&mut self, rvalue: impl Into<RValue>) -> Operand {
        match rvalue.into() {
            RValue::Use(Operand::Place(mut place)) => {
                place.projections.push(Projection::Deref);
                Operand::Place(place)
            }
            RValue::Use(Operand::Ref(place)) => Operand::Place(place),
            rvalue => {
                let local = self.assign_new(rvalue);
                Operand::Place(Place { local, projections: vec![Projection::Deref] })
            }
        }
    }

    fn format_array(&mut self, of: Ty<'tcx>, val: Operand) -> RValue {
        let body = self.generate_array_func(of);
        let ref_array = self.ref_of(val);
        RValue::Call { function: Constant::Func(body).into(), args: [ref_array].into() }
    }

    fn format_struct(&mut self, strct: &Struct<'tcx>, val: Operand) -> RValue {
        let body = self.generate_struct_func(strct);
        let ref_struct = self.ref_of(val);
        RValue::Call {
            function: Operand::Constant(Constant::Func(body)),
            args: [ref_struct].into(),
        }
    }

    fn generate_array_func(&mut self, ty: Ty<'tcx>) -> BodyId {
        if let Some(body) = self.array_display_bodies.get(&ty) {
            return *body;
        }
        let body_id =
            self.mir.bodies.push(Body::new(Some("format_array".into()), 1).with_auto(true));
        let body_token = self.scopes.push_body(BodyInfo::new(body_id));

        self.array_display_bodies.insert(ty, body_id);

        let out = self.format_array_inner(ty, Local::from(0));
        self.finish_with(Terminator::Return(out));

        self.scopes.pop_body(body_token);
        body_id
    }

    // `array` must point to `&[T])`
    fn format_array_inner(&mut self, ty: Ty<'tcx>, array: Local) -> Operand {
        let strings = self.assign_new(Constant::EmptyArray { cap: 0 });

        let len = self
            .assign_new(RValue::Unary { op: UnaryOp::ArrayLen, operand: Operand::local(array) });

        let index = self.assign_new(Constant::Int(0));

        self.lower_loop(
            |lower| {
                Some(lower.assign_new(RValue::Binary {
                    lhs: Operand::local(index),
                    op: BinaryOp::IntLess,
                    rhs: Operand::local(len),
                }))
            },
            |lower| {
                let elem = Place {
                    local: array,
                    projections: vec![Projection::Deref, Projection::Index(index)],
                };

                let formatted_elem = lower.format_rvalue(Operand::Place(elem), ty);
                let rhs = lower.process(formatted_elem, Ty::STR);

                lower.assign_new(RValue::Binary {
                    lhs: Operand::Ref(Place::local(strings)),
                    op: BinaryOp::ArrayPush,
                    rhs,
                });

                lower.assign(
                    index,
                    RValue::Binary {
                        lhs: Operand::local(index),
                        op: BinaryOp::IntAdd,
                        rhs: Constant::Int(1).into(),
                    },
                );
            },
        );

        let out = self.assign_new(RValue::Unary {
            op: UnaryOp::ArrayStrFmt,
            operand: Operand::local(strings),
        });

        Operand::local(out)
    }

    fn generate_struct_func(&mut self, strct: &Struct<'tcx>) -> BodyId {
        if let Some(Some(body)) = self.struct_display_bodies.get(strct.id) {
            return *body;
        }
        let body_id = self.mir.bodies.push(Body::new(None, 1).with_auto(true));
        let body_token = self.scopes.push_body(BodyInfo::new(body_id));

        if self.struct_display_bodies.len() <= strct.id {
            self.struct_display_bodies.resize(strct.id.index() + 1, None);
        }
        self.struct_display_bodies[strct.id] = Some(body_id);

        let mut segments = vec![str!("(")];
        for (i, (_, ty)) in (0u32..).zip(&strct.fields) {
            if i != 0 {
                segments.push(str!(", "));
            }
            let projections = vec![Projection::Deref, Projection::Field(i as _)];
            let field = Operand::Place(Place { local: Local::from(0), projections });
            let field_str = self.format_rvalue(field, *ty);
            segments.push(Operand::local(self.assign_new(field_str)));
        }
        segments.push(str!(")"));

        let segments = segments.into_iter().map(|operand| (operand, None)).collect();
        let strings = self.assign_new(RValue::BuildArray(segments));

        let out = self
            .assign_new(RValue::Unary { op: UnaryOp::StrJoin, operand: Operand::local(strings) });
        self.finish_with(Terminator::Return(Operand::local(out)));

        self.scopes.pop_body(body_token);
        body_id
    }

    pub fn monomorphization(&mut self) {
        while let Some(new_impl) = self.mono_generics.pop_front() {
            let (decl, fn_ty, body_id) = new_impl;
            self.generic_map = Some(produce_generic_map(decl, fn_ty));
            let hir::FnDecl { ident, for_ty, ref body, ref params, .. } = *decl;

            let body_token = self.scopes.push_body(BodyInfo::new(body_id));

            if self.scopes.bodies.len() == 2 && self.try_intrinsic(for_ty, ident) {
                let current = self.current().id;
                self.mir.bodies[current].auto = true;
            } else {
                for (i, param) in params.iter().enumerate() {
                    self.insert_local(param.ident, Local::from(i));
                }
                let mut last = Operand::UNIT;
                for &expr in body {
                    last = self.lower(expr);
                }
                self.finish_with(Terminator::Return(last));
            }
            self.scopes.pop_body(body_token);
        }
    }

    fn lower_use(&mut self, use_: &hir::Use, current: ModuleId) {
        let (module, last) = self.scopes.get_module_with(&use_.path.segments, current).unwrap();
        let Some(kind) = &use_.kind else {
            if let Some(&module) = self.scopes[module].modules.get(&last) {
                self.scopes.modules.insert(last, module);
            }
            if let Some(&var) = self.scopes[module].scope().variables.get(&last) {
                self.scopes.scope_mut().insert(last, var);
            }

            return;
        };

        let module = *self.scopes[module].modules.get(&last).unwrap();
        match kind {
            UseKind::Block(imports) => {
                for use_ in imports {
                    self.lower_use(use_, module);
                }
            }
            UseKind::Wildcard => {
                let [module, current] = self
                    .scopes
                    .module_storage
                    .as_mut_vec()
                    .get_disjoint_mut([module.index(), current.index()])
                    .unwrap();
                assert!(module.bodies.len() == 1);
                let body = &module.bodies[0];
                let scope = body.scopes.last().unwrap().variables.iter().map(|(s, t)| (*s, *t));
                let current_body = current.bodies.last_mut().unwrap();
                current_body.scopes.last_mut().unwrap().variables.extend(scope);
                current.modules.extend(&module.modules);
            }
        }
    }
}

fn produce_generic_map<'tcx>(
    generic: &FnDecl<'tcx>,
    mono: &ty::Function<'tcx>,
) -> HashMap<GenericId, Ty<'tcx>> {
    let generic = generic.params.iter().map(|param| param.ty).chain([generic.ret]);
    let mono = mono.params.iter().copied().chain([mono.ret]);
    generic_map_inner(generic, mono)
}

fn generic_map_inner<'tcx>(
    generic: impl IntoIterator<Item = Ty<'tcx>>,
    mono: impl IntoIterator<Item = Ty<'tcx>>,
) -> HashMap<GenericId, Ty<'tcx>> {
    let mut map = HashMap::default();
    for (generic, mono) in generic.into_iter().zip(mono) {
        generic_map_ty(generic, mono, &mut map);
    }
    map
}

// TODO: replace with some kind of iterator through a type
fn generic_map_ty<'tcx>(
    generic: Ty<'tcx>,
    mono: Ty<'tcx>,
    into: &mut HashMap<GenericId, Ty<'tcx>>,
) {
    match (generic.0, mono.0) {
        (TyKind::Generic(id), _) => _ = into.insert(*id, mono),
        (TyKind::Function(generic), TyKind::Function(mono)) => {
            generic.params.iter().zip(&mono.params).for_each(|(&g, &m)| generic_map_ty(g, m, into));
            generic_map_ty(generic.ret, mono.ret, into);
        }
        (TyKind::Struct(lhs), TyKind::Struct(rhs)) => {
            for ((_, generic), (_, mono)) in lhs.fields.iter().zip(&rhs.fields) {
                generic_map_ty(*generic, *mono, into);
            }
        }
        (TyKind::Array(generic), TyKind::Array(mono))
        | (TyKind::Ref(generic), TyKind::Ref(mono)) => generic_map_ty(*generic, *mono, into),
        _ => {}
    }
}
