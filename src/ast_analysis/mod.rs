mod errors;

use std::{ops::Index, path::Path};

use index_vec::IndexVec;
use miette::{Error, Result};

use crate::{
    HashMap,
    ast::{
        self, Ast, BinOpKind, BinaryOp, Block, BlockId, ExprId, ExprKind, FnDecl, Identifier, Impl,
        Lit, Pat, PatArg, PatKind, Trait, TypeId, UnaryOp,
    },
    span::Span,
    symbol::Symbol,
    ty::{Function, GenericRange, Interned, Ty, TyCtx, TyKind},
};

#[derive(Default, Debug)]
pub struct TyInfo<'tcx> {
    pub expr_tys: IndexVec<ExprId, Ty<'tcx>>,
    pub type_ids: IndexVec<TypeId, Ty<'tcx>>,
    pub struct_types: HashMap<Span, Ty<'tcx>>,
    pub method_types: HashMap<ExprId, Ty<'tcx>>,
    pub struct_pat_types: HashMap<Span, Ty<'tcx>>,
}

impl<'tcx> Index<TypeId> for TyInfo<'tcx> {
    type Output = Ty<'tcx>;
    fn index(&self, index: TypeId) -> &Self::Output {
        &self.type_ids[index]
    }
}

#[derive(Debug)]
struct Body<'tcx> {
    ty_names: HashMap<Symbol, Ty<'tcx>>,
    ret: Ty<'tcx>,
    scopes: Vec<Scope<'tcx>>,
    loops: usize,
}

#[derive(Debug)]
struct Infer {
    out: Result<(), ()>,
}

impl Infer {
    fn then<'tcx>(self, ty: impl FnOnce() -> Ty<'tcx>) -> Ty<'tcx> {
        match self.out {
            Ok(()) => ty(),
            Err(()) => Ty::POISON,
        }
    }
}

impl<'tcx> Body<'tcx> {
    pub fn scope(&mut self) -> &mut Scope<'tcx> {
        self.scopes.last_mut().unwrap()
    }
    pub fn insert_var(
        &mut self,
        ident: Identifier,
        ty: Ty<'tcx>,
        kind: Var,
    ) -> Option<(Ty<'tcx>, Var)> {
        self.scope().variables.insert(ident.symbol, (ty, kind))
    }
}

#[derive(Debug, Default)]
struct Scope<'tcx> {
    variables: HashMap<Symbol, (Ty<'tcx>, Var)>,
}

#[derive(Debug, Clone, Copy)]
enum Var {
    Let,
    Const,
}

impl<'tcx> Body<'tcx> {
    pub fn new(ret: Ty<'tcx>) -> Self {
        Self { ty_names: HashMap::default(), ret, scopes: vec![Scope::default()], loops: 0 }
    }
}

struct Collector<'src, 'ast, 'tcx> {
    ty_info: TyInfo<'tcx>,
    bodies: Vec<Body<'tcx>>,
    ast: &'ast Ast,
    tcx: &'tcx TyCtx<'tcx>,
    src: &'src str,
    path: Option<&'src Path>,
    within_const: bool,
    fn_generics: GenericRange,
    impl_generics: GenericRange,
    // the generics created by preanalyze impl/fndecl
    produced_generics: HashMap<ExprId, GenericRange>,
    errors: Vec<Error>,
}

fn setup_ty_info<'tcx>(ast: &Ast) -> TyInfo<'tcx> {
    let shared = Ty::UNIT;
    TyInfo {
        struct_pat_types: HashMap::default(),
        expr_tys: std::iter::repeat_n(shared, ast.exprs.len()).collect(),
        type_ids: std::iter::repeat_n(shared, ast.types.len()).collect(),
        method_types: HashMap::default(),
        struct_types: HashMap::default(),
    }
}

pub fn analyze<'tcx>(
    file: Option<&Path>,
    src: &str,
    ast: &Ast,
    tcx: &'tcx TyCtx<'tcx>,
) -> Result<TyInfo<'tcx>, Vec<Error>> {
    let ty_info = setup_ty_info(ast);
    let body = global_body();
    let mut collector = Collector {
        path: file,
        src,
        ty_info,
        ast,
        tcx,
        bodies: vec![body],
        within_const: false,
        fn_generics: GenericRange::EMPTY,
        impl_generics: GenericRange::EMPTY,
        produced_generics: HashMap::default(),
        errors: vec![],
    };
    let top_level_exprs = ast.top_level.iter().copied().collect();
    let top_level = ast::Block { span: Span::ZERO, stmts: top_level_exprs, is_expr: false };
    collector.analyze_body_with(&top_level, Body::new(Ty::NEVER)).map_err(|err| vec![err])?;

    if !collector.errors.is_empty() {
        return Err(collector.errors);
    }

    let mut ty_info = std::mem::take(&mut collector.ty_info);
    for (expr, ty) in std::iter::zip(&ast.exprs, &mut ty_info.expr_tys) {
        *ty = tcx.try_infer_deep(*ty).map_err(|ty| vec![collector.cannot_infer(ty, expr.span)])?;
    }
    ty_info.type_ids.iter_mut().for_each(|ty| *ty = tcx.infer_deep(*ty));
    ty_info.method_types.values_mut().for_each(|ty| *ty = tcx.infer_deep(*ty));
    ty_info.struct_types.values_mut().for_each(|ty| *ty = tcx.infer_deep(*ty));
    ty_info.struct_pat_types.values_mut().for_each(|ty| *ty = tcx.infer_deep(*ty));

    Ok(ty_info)
}

fn global_body<'tcx>() -> Body<'tcx> {
    let mut body = Body::new(Ty::NEVER);
    let common = [("bool", Ty::BOOL), ("int", Ty::INT), ("char", Ty::CHAR), ("str", Ty::STR)]
        .map(|(name, ty)| (Symbol::from(name), ty));
    body.ty_names.extend(common);
    body
}

impl<'tcx> Collector<'_, '_, 'tcx> {
    fn analyze_body_with(
        &mut self,
        block: &ast::Block,
        mut body: Body<'tcx>,
    ) -> Result<(Ty<'tcx>, Body<'tcx>)> {
        // look for structs/enums first.
        for id in &block.stmts {
            let ExprKind::Struct { ident, generics, fields } = &self.ast.exprs[*id].kind else {
                continue;
            };
            let generics = self.tcx.new_generics(generics);
            self.impl_generics = generics;

            let (fields, params) = fields
                .iter()
                .map(|field| {
                    let ty = self.read_ast_ty(field.ty);
                    ((field.ident.symbol, ty), ty)
                })
                .collect();
            let struct_ty = self.tcx.new_struct(ident.symbol, generics, fields);
            self.current().ty_names.insert(ident.symbol, struct_ty);
            self.ty_info.struct_types.insert(ident.span, struct_ty);

            body.insert_var(
                *ident,
                self.tcx.intern(TyKind::Function(Function { params, ret: struct_ty })),
                Var::Const,
            );
        }

        for &id in &block.stmts {
            match &self.ast.exprs[id].kind {
                ExprKind::FnDecl(func) => self.preanalyze_fndecl(&mut body, func, id)?,
                ExprKind::Impl(impl_) => {
                    let generics = self.tcx.new_generics(&impl_.generics);
                    self.impl_generics = generics;
                    self.produced_generics.insert(id, self.impl_generics);
                    let ty = self.read_ast_ty_with(impl_.ty, None);
                    for &method_id in &impl_.methods {
                        let ExprKind::FnDecl(func) = &self.ast.exprs[method_id].kind else {
                            unreachable!()
                        };
                        self.preanalyze_method(&body, ty, func, method_id);
                    }
                }
                _ => {}
            }
        }
        self.bodies.push(body);
        let out = self.analyze_block_inner(block)?;
        Ok((out, self.bodies.pop().unwrap()))
    }

    fn preanalyze_fndecl(
        &mut self,
        body: &mut Body<'tcx>,
        fndecl: &FnDecl,
        id: ExprId,
    ) -> Result<()> {
        let FnDecl { ident, generics, params, ret, .. } = fndecl;
        self.fn_generics = self.tcx.new_generics(generics);
        self.produced_generics.insert(id, self.fn_generics);
        let ret = match ret {
            Some(ret) => self.read_ast_ty(*ret),
            None => Ty::UNIT,
        };
        let params = params
            .iter()
            .map(|param| {
                if let Some(param_ty) = param.ty {
                    self.read_ast_ty(param_ty)
                } else {
                    self.errors.push(self.param_missing_ty(param.ident.span));
                    Ty::POISON
                }
            })
            .collect();
        let prev = body.insert_var(
            *ident,
            self.tcx.intern(TyKind::Function(Function { params, ret })),
            Var::Const,
        );

        if prev.is_some() { Err(self.already_defined(*ident)) } else { Ok(()) }
    }

    fn preanalyze_method(&mut self, body: &Body<'tcx>, ty: Ty<'tcx>, fndecl: &FnDecl, id: ExprId) {
        _ = body;
        let FnDecl { ident, generics, params, ret, .. } = fndecl;
        self.fn_generics = self.tcx.new_generics(generics);
        self.produced_generics.insert(id, self.fn_generics);
        let ret = match ret {
            Some(ret) => self.read_ast_ty_with(*ret, Some(ty)),
            None => Ty::UNIT,
        };
        let params = params
            .iter()
            .enumerate()
            .map(|(i, param)| match param.ty {
                Some(param_ty) => self.read_ast_ty_with(param_ty, Some(ty)),
                None if i == 0 && param.ident.symbol == "self" => ty,
                None => {
                    self.errors.push(self.param_missing_ty(param.ident.span));
                    Ty::POISON
                }
            })
            .collect();

        let fn_ty = Function { params, ret };
        self.tcx.add_method(ty, ident.symbol, fn_ty);
    }
    fn current(&mut self) -> &mut Body<'tcx> {
        self.bodies.last_mut().unwrap()
    }

    fn analyze_block(&mut self, id: BlockId) -> Result<Ty<'tcx>> {
        let block = &self.ast.blocks[id];
        self.analyze_block_inner(block)
    }

    fn analyze_block_inner(&mut self, block: &Block) -> Result<Ty<'tcx>> {
        self.current().scopes.push(Scope::default());
        let mut ty = None;
        for &id in &block.stmts {
            ty = Some(self.analyze_expr(id)?);
        }
        self.current().scopes.pop().unwrap();
        Ok(if block.is_expr {
            ty.unwrap_or(Ty::UNIT)
        } else if ty.is_some_and(|ty| ty.is_never()) {
            Ty::NEVER
        } else {
            Ty::UNIT
        })
    }

    fn read_ast_ty(&mut self, id: ast::TypeId) -> Ty<'tcx> {
        self.read_ast_ty_with(id, None)
    }

    fn read_ast_ty_with(&mut self, id: ast::TypeId, for_ty: Option<Ty<'tcx>>) -> Ty<'tcx> {
        let ast_ty = &self.ast.types[id];
        let ty = match ast_ty.kind {
            ast::TyKind::Ref(of) => self.tcx.intern(TyKind::Ref(self.read_ast_ty_with(of, for_ty))),
            ast::TyKind::Func { ref params, ret } => {
                let ret = match ret {
                    Some(ty) => self.read_ast_ty_with(ty, for_ty),
                    None => Ty::UNIT,
                };
                let params =
                    params.iter().map(|param| self.read_ast_ty_with(*param, for_ty)).collect();
                self.tcx.intern(TyKind::Function(Function { params, ret }))
            }
            ast::TyKind::Never => Ty::NEVER,
            ast::TyKind::Unit => Ty::UNIT,
            ast::TyKind::Array(of) => {
                self.tcx.intern(TyKind::Array(self.read_ast_ty_with(of, for_ty)))
            }
            ast::TyKind::Name { ident, .. } if ident.symbol == "_" => self.tcx.new_infer(),
            ast::TyKind::Name { ident, .. } if ident.symbol == "self" => {
                if let Some(ty) = for_ty {
                    ty
                } else {
                    self.errors.push(self.invalid_self(ast_ty.span));
                    Ty::POISON
                }
            }
            ast::TyKind::Name { ident, ref generics } => {
                if generics.is_empty() {
                    match ([self.impl_generics, self.fn_generics].iter().copied().flatten())
                        .find(|&g| self.tcx.generic_symbol(g) == ident.symbol)
                    {
                        Some(id) => self.tcx.intern(TyKind::Generic(id)),
                        None => self.read_named_ty(ident),
                    }
                } else {
                    let ty = self.read_named_ty(ident);
                    match ty.0 {
                        TyKind::Struct(strct) => {
                            // TODO: hashmap is not needed
                            let mut map = HashMap::default();
                            // TODO: custom error here
                            assert!(generics.len() == strct.generics.len as usize);
                            for (id, ty) in strct.generics.iter().zip(generics) {
                                map.insert(id, self.read_ast_ty(*ty));
                            }
                            ty.replace_generics(self.tcx, &mut |id| map[&id])
                        }
                        _ => unreachable!(),
                    }
                }
            }
        };
        self.ty_info.type_ids[id] = ty;
        ty
    }

    fn read_named_ty(&mut self, ident: Identifier) -> Ty<'tcx> {
        if let Some(&ty) =
            self.bodies.iter().rev().find_map(|body| body.ty_names.get(&ident.symbol))
        {
            return ty;
        }
        self.errors.push(self.unknown_type_err(ident));
        Ty::POISON
    }

    fn eq(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, expr: ExprId) -> Infer {
        if let Err([lhs, rhs]) = self.tcx.eq(lhs, rhs) {
            self.errors.push(self.subtype_err(lhs, rhs, expr));
            return Infer { out: Err(()) };
        }
        Infer { out: Ok(()) }
    }

    fn eq_block(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, block: BlockId) -> Infer {
        if let Err([lhs, rhs]) = self.tcx.eq(lhs, rhs) {
            self.errors.push(self.subtype_err_block(lhs, rhs, block));
            return Infer { out: Err(()) };
        }
        Infer { out: Ok(()) }
    }

    fn sub(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, expr: ExprId) -> Infer {
        if let Err([lhs, rhs]) = self.tcx.sub(lhs, rhs) {
            self.errors.push(self.subtype_err(lhs, rhs, expr));
            return Infer { out: Err(()) };
        }
        Infer { out: Ok(()) }
    }

    fn sub_span(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, span: Span) -> Infer {
        if let Err([lhs, rhs]) = self.tcx.sub(lhs, rhs) {
            self.errors.push(self.subtype_err_inner(lhs, rhs, vec![span]));
            return Infer { out: Err(()) };
        }
        Infer { out: Ok(()) }
    }

    fn sub_block(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, block: BlockId) -> Infer {
        if let Err([lhs, rhs]) = self.tcx.sub(lhs, rhs) {
            self.errors.push(self.subtype_err_block(lhs, rhs, block));
            return Infer { out: Err(()) };
        }
        Infer { out: Ok(()) }
    }

    #[expect(clippy::too_many_lines)]
    fn analyze_expr(&mut self, id: ExprId) -> Result<Ty<'tcx>> {
        let expr_span = self.ast.exprs[id].span;
        if !self.within_const && self.bodies.len() <= 2 && !self.is_item(id) {
            return Err(self.expected_item(id));
        }
        if self.within_const && !self.is_const(id) {
            return Err(self.expected_const(id));
        }

        let ty = match self.ast.exprs[id].kind {
            ExprKind::Trait(ref trait_) => self.analyze_trait(trait_, id)?,
            ExprKind::Impl(ref impl_) => self.analyze_impl(impl_, id)?,
            ExprKind::Assert(expr) => {
                let ty = self.analyze_expr(expr)?;
                self.sub(ty, Ty::BOOL, expr);
                Ty::UNIT
            }
            ExprKind::Lit(ref lit) => self.analyze_lit(lit)?,
            ExprKind::Ident(ident) => self.read_ident(ident, expr_span)?,
            ExprKind::Unary { expr, op } => 'outer: {
                let operand = self.analyze_expr(expr)?;
                let ty = match op {
                    UnaryOp::Neg => Ty::INT,
                    UnaryOp::Not => Ty::BOOL,
                    UnaryOp::Ref => break 'outer self.tcx.intern(TyKind::Ref(operand)),
                    UnaryOp::Deref => {
                        let operand = self.tcx.infer_shallow(operand);
                        let TyKind::Ref(inner) = operand.0 else {
                            if !operand.is_poison() {
                                self.errors.push(self.cannot_deref(operand, expr_span));
                            }
                            break 'outer Ty::POISON;
                        };
                        break 'outer *inner;
                    }
                };
                self.sub(operand, ty, id).then(|| ty)
            }
            ExprKind::Binary { lhs, op, rhs } => self.analyze_binary_expr(lhs, op, rhs)?,
            ExprKind::Index { expr, index } => self.index(expr, index, expr_span)?,
            ExprKind::FnCall { function, ref args } => 'out: {
                let fn_ty = self.analyze_expr(function)?;
                let TyKind::Function(Function { params, ret }) = fn_ty.0 else {
                    let fn_span = self.ast.exprs[function].span;
                    self.errors.push(self.expected_function(fn_ty, fn_span));
                    break 'out Ty::POISON;
                };

                if args.len() != params.len() {
                    self.errors.push(self.invalid_arg_count(
                        args.len(),
                        params.len(),
                        self.ast.exprs[function].span,
                        expr_span,
                    ));
                }

                for (&arg_id, param) in std::iter::zip(args, params) {
                    let arg = self.analyze_expr(arg_id)?;
                    self.sub(arg, *param, arg_id);
                }
                *ret
            }
            ExprKind::MethodCall { expr, method, ref args } => 'out: {
                let ty = self.tcx.infer_shallow(self.analyze_expr(expr)?);
                let Some(func) = self.tcx.get_method(ty, method.symbol) else {
                    if !ty.is_poison() {
                        self.errors.push(self.method_not_found(ty, method));
                    }
                    return Ok(Ty::POISON);
                };
                let func = func.caller(self.tcx);

                let Function { ref params, ret } = func;

                if args.len() + 1 != params.len() {
                    self.errors.push(self.invalid_arg_count(
                        args.len() + 1,
                        params.len(),
                        method.span,
                        expr_span,
                    ));
                    break 'out ret;
                }

                self.anyref_sub(ty, params[0], expr);

                for (&arg_id, param) in args.iter().zip(&params[1..]) {
                    let arg = self.analyze_expr(arg_id)?;
                    self.sub(arg, *param, arg_id);
                }

                let fn_ty = self.tcx.intern(TyKind::Function(func));
                self.ty_info.method_types.insert(id, fn_ty);

                ret
            }
            ExprKind::FnDecl(ref decl) => self.analyze_fndecl(decl, id)?,
            ExprKind::Struct { .. } => Ty::UNIT,
            ExprKind::Let { ident, ty, expr } => {
                let expr_ty = self.analyze_expr(expr)?;
                let ty = if let Some(ty) = ty {
                    let ty = self.read_ast_ty(ty);
                    self.sub(expr_ty, ty, expr);
                    ty
                } else {
                    expr_ty
                };
                self.insert_var(ident, ty, Var::Let);
                Ty::UNIT
            }
            ExprKind::Const { ident, ty, expr } => {
                let within_const = std::mem::replace(&mut self.within_const, true);
                let expr_ty = self.analyze_expr(expr)?;
                self.within_const = within_const;
                let ty = if let Some(ty) = ty {
                    let ty = self.read_ast_ty(ty);
                    self.sub(expr_ty, ty, expr);
                    ty
                } else {
                    expr_ty
                };
                if self.tcx.try_infer_deep(ty).is_err() {
                    return Err(self.cannot_infer(ty, self.ast.spans([expr])));
                }
                self.insert_var(ident, ty, Var::Const);
                Ty::UNIT
            }
            ExprKind::For { ident, iter, body } => {
                // for now only allow ranges
                let iter_ty = self.analyze_expr(iter)?;
                let iter_ty = self.tcx.infer_shallow(iter_ty);
                let ident_ty = match iter_ty.0 {
                    TyKind::Range => Ty::INT,
                    TyKind::Array(of) => *of,
                    _ => return Err(self.cannot_iter(iter_ty, self.ast.exprs[iter].span)),
                };

                self.current().scopes.push(Scope::default());
                self.insert_var(ident, ident_ty, Var::Let);

                self.current().loops += 1;
                let out = self.analyze_block(body)?;
                self.current().loops -= 1;
                self.current().scopes.pop().unwrap();

                self.sub_block(out, Ty::UNIT, body);
                Ty::UNIT
            }
            ExprKind::While { condition, block } => {
                let condition_ty = self.analyze_expr(condition)?;
                self.current().scopes.push(Scope::default());
                self.sub(condition_ty, Ty::BOOL, condition);
                self.current().loops += 1;
                self.analyze_block(block)?;
                self.current().loops -= 1;
                self.current().scopes.pop().unwrap();
                Ty::UNIT
            }
            ExprKind::Match { scrutinee, ref arms } => {
                let mut ty = None;
                let scrutinee = self.analyze_expr(scrutinee)?;
                for arm in arms {
                    self.current().scopes.push(Scope::default());
                    self.analyze_pat(&arm.pat, scrutinee)?;
                    let arm_ty = self.analyze_expr(arm.body)?;
                    match ty {
                        None => ty = Some(arm_ty),
                        Some(ty) => _ = self.eq(arm_ty, ty, arm.body),
                    }
                    self.current().scopes.pop().unwrap();
                }
                // TODO: produce error here instead
                ty.unwrap_or_else(|| self.tcx.new_infer())
            }
            ExprKind::Is { .. } => todo!(),
            ExprKind::If { ref arms, els } => {
                let mut expected_ty = None;

                for arm in arms {
                    let ty = self.analyze_expr(arm.condition)?;
                    self.sub(ty, Ty::BOOL, id);
                    let block_ty = self.analyze_block(arm.body)?;
                    if let Some(expected_ty) = expected_ty {
                        self.eq_block(expected_ty, block_ty, arm.body);
                    } else {
                        expected_ty = Some(block_ty);
                    }
                }
                let expected_ty = expected_ty.unwrap();
                if let Some(els) = els {
                    let block_ty = self.analyze_block(els)?;
                    self.sub_block(expected_ty, block_ty, els);
                } else {
                    // TODO: specialized error message here.
                    self.sub(expected_ty, Ty::UNIT, id);
                }
                expected_ty
            }
            ExprKind::Block(block_id) => {
                let block = &self.ast.blocks[block_id];
                if block.is_expr {
                    let mut ty = None;
                    for &id in &block.stmts {
                        ty = Some(self.analyze_expr(id)?);
                    }
                    ty.unwrap()
                } else {
                    self.analyze_block(block_id)?;
                    Ty::UNIT
                }
            }
            ExprKind::Return(expr) => {
                let ty = expr.map_or(Ok(Ty::UNIT), |expr| self.analyze_expr(expr))?;
                let expected = self.current().ret;
                self.sub(ty, expected, expr.unwrap_or(id));
                Ty::NEVER
            }
            ExprKind::Break => {
                if self.current().loops == 0 {
                    self.errors.push(self.cannot_break(self.ast.exprs[id].span));
                    Ty::POISON
                } else {
                    Ty::NEVER
                }
            }
            ExprKind::Continue => {
                if self.current().loops == 0 {
                    self.errors.push(self.cannot_continue(self.ast.exprs[id].span));
                    Ty::POISON
                } else {
                    Ty::NEVER
                }
            }
            ExprKind::Unreachable => Ty::NEVER,
            ExprKind::FieldAccess { expr, field } => 'out: {
                let expr = self.tcx.infer_shallow(self.analyze_expr(expr)?);
                let TyKind::Struct(strct) = expr.0 else {
                    if !expr.is_poison() {
                        self.errors.push(self.field_error(expr, field));
                    }
                    break 'out Ty::POISON;
                };
                strct.field_ty(field.symbol).unwrap_or_else(|| {
                    self.errors.push(self.unknown_field_error(strct.field_names(), expr, field));
                    Ty::POISON
                })
            }
        };
        self.ty_info.expr_tys[id] = ty;
        Ok(ty)
    }

    fn anyref_sub(&mut self, mut lhs: Ty<'tcx>, mut rhs: Ty<'tcx>, expr: ExprId) {
        loop {
            lhs = self.tcx.infer_shallow(lhs);
            match lhs.0 {
                TyKind::Ref(of) => lhs = *of,
                _ => break,
            }
        }

        loop {
            rhs = self.tcx.infer_shallow(rhs);
            match rhs.0 {
                TyKind::Ref(of) => rhs = *of,
                _ => break,
            }
        }
        self.sub(lhs, rhs, expr);
    }

    fn insert_var(&mut self, ident: Identifier, ty: Ty<'tcx>, kind: Var) {
        self.current().insert_var(ident, ty, kind);
    }

    fn analyze_pat(&mut self, pat: &Pat, scrutinee: Ty<'tcx>) -> Result<()> {
        match pat.kind {
            PatKind::Struct(ident, ref fields) => {
                let ty = self.read_named_ty(ident);
                let strct = match self.tcx.infer_shallow(ty).0 {
                    TyKind::Struct(strct) => strct,
                    TyKind::Poison => return Ok(()),
                    _ => {
                        self.errors.push(self.expected_struct_pat(ty, ident.span));
                        return Ok(());
                    }
                };
                let (ty, strct) = strct.caller(self.tcx);
                self.ty_info.struct_pat_types.insert(ident.span, ty);
                self.sub_span(ty, scrutinee, pat.span);

                for PatArg { ident, pat } in fields {
                    let field_ty = strct.field_ty(ident.symbol).unwrap_or_else(|| {
                        self.errors.push(self.unknown_field_error(strct.field_names(), ty, *ident));
                        Ty::POISON
                    });
                    self.analyze_pat(pat, field_ty)?;
                }
            }
            PatKind::Ident(ident) => {
                // TODO: ...
                let ident = Identifier { symbol: ident, span: pat.span };
                self.insert_var(ident, scrutinee, Var::Let);
            }
            PatKind::Str(..) => _ = self.sub_span(Ty::STR, scrutinee, pat.span),
            PatKind::Int(..) => _ = self.sub_span(Ty::INT, scrutinee, pat.span),
            PatKind::Expr(block) => {
                let ty = self.analyze_block(block)?;
                let op = BinaryOp { span: pat.span, kind: BinOpKind::Eq };
                if !Self::is_valid_binop(scrutinee, op.kind) {
                    self.errors.push(self.binop_err(op, scrutinee, ty));
                }
                self.sub_block(ty, scrutinee, block);
            }
            PatKind::Or(ref patterns) => {
                for pat in patterns {
                    self.analyze_pat(pat, scrutinee)?;
                }
            }
        }
        Ok(())
    }

    fn analyze_binary_expr(&mut self, lhs: ExprId, op: BinaryOp, rhs: ExprId) -> Result<Ty<'tcx>> {
        use BinOpKind as B;

        let mut lhs_ty = self.analyze_expr(lhs)?;
        let mut rhs_ty = self.analyze_expr(rhs)?;

        match op.kind {
            BinOpKind::Assign => {}
            kind if kind.is_op_assign() => rhs_ty = rhs_ty.fully_deref(),
            _ => {
                lhs_ty = lhs_ty.fully_deref();
                rhs_ty = rhs_ty.fully_deref();
            }
        }

        self.enforce_valid_binop(lhs_ty, op, rhs_ty, lhs, rhs)?;
        let infer = self.sub(rhs_ty, lhs_ty, rhs);

        Ok(match op.kind {
            B::Assign
            | B::AddAssign
            | B::SubAssign
            | B::MulAssign
            | B::DivAssign
            | B::ModAssign => Ty::UNIT,
            B::And | B::Or | B::Less | B::Greater | B::LessEq | B::GreaterEq | B::Eq | B::Neq => {
                Ty::BOOL
            }
            B::RangeInclusive | B::Range => Ty::RANGE,
            B::Add | B::Sub | B::Mul | B::Div | B::Mod => infer.then(|| lhs_ty),
        })
    }

    fn enforce_valid_binop(
        &self,
        lhs: Ty<'tcx>,
        op: BinaryOp,
        rhs: Ty<'tcx>,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
    ) -> Result<()> {
        if op.kind == BinOpKind::Assign {
            return Ok(());
        }

        let lhs = self.tcx.infer_shallow(lhs);

        if lhs.is_poison() || rhs.is_poison() {
            return Ok(());
        }

        if Self::is_valid_binop(lhs, op.kind) {
            Ok(())
        } else {
            Err(if op.is_logical() {
                self.logical_op_err(lhs, rhs, lhs_expr, rhs_expr)
            } else {
                self.binop_err(op, lhs, rhs)
            })
        }
    }

    fn is_valid_binop(ty: Ty<'tcx>, op: BinOpKind) -> bool {
        match ty.0 {
            TyKind::Int => op.is_op_assign() | op.is_arithmetic() | op.is_compare() | op.is_range(),
            TyKind::Str => op.is_compare() | op.is_add(),
            TyKind::Bool => op.is_eq() | op.is_logical(),
            TyKind::Char | TyKind::Unit => op.is_eq(),
            _ => false,
        }
    }

    fn index(&mut self, expr: ExprId, index: ExprId, span: Span) -> Result<Ty<'tcx>> {
        let expr = self.analyze_expr(expr)?;
        let index = self.analyze_expr(index)?;
        let expr = self.tcx.infer_shallow(expr);
        Ok(self.index_ty(expr, index, span))
    }

    fn index_ty(&mut self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, span: Span) -> Ty<'tcx> {
        match (lhs.0, rhs.0) {
            (TyKind::Poison, _) | (_, TyKind::Poison) => Ty::POISON,
            (TyKind::Str, TyKind::Range) => Ty::STR,
            (TyKind::Array(_), TyKind::Range) => lhs,
            (TyKind::Array(of), TyKind::Int) => *of,
            (TyKind::Str, TyKind::Int) => Ty::CHAR,
            (TyKind::Ref(lhs), _) => self.index_ty(*lhs, rhs, span),
            _ => {
                self.errors.push(self.cannot_index(lhs, span));
                Ty::POISON
            }
        }
    }

    fn analyze_method(
        &mut self,
        ty: Ty<'tcx>,
        decl: &FnDecl,
        method_id: ExprId,
    ) -> Result<Ty<'tcx>> {
        let block_id = decl.block.unwrap();
        self.fn_generics = self.produced_generics[&method_id];
        let fn_ty = self.tcx.get_method(ty, decl.ident.symbol).unwrap();
        self.fndecl_inner(&decl.params, block_id, fn_ty)
    }

    fn analyze_fndecl(&mut self, decl: &FnDecl, id: ExprId) -> Result<Ty<'tcx>> {
        self.fn_generics = self.produced_generics[&id];
        let block_id = decl.block.unwrap();
        // call `read_ident_raw` to avoid producing extra inference variables
        let (fn_ty, _) = self
            .read_ident_raw(decl.ident.symbol, Span::ZERO)
            .expect("fndecl ident should have been inserted already");
        let TyKind::Function(fn_ty) = fn_ty.0 else { unreachable!() };
        self.fndecl_inner(&decl.params, block_id, fn_ty)
    }

    fn fndecl_inner(
        &mut self,
        params: &[ast::Param],
        block_id: BlockId,
        fn_ty: &'tcx Function<'tcx>,
    ) -> Result<Ty<'tcx>> {
        let Function { params: param_tys, ret, .. } = fn_ty;
        let mut body = Body::new(*ret);
        for (param, &ty) in std::iter::zip(params, param_tys) {
            body.insert_var(param.ident, ty, Var::Let);
        }
        let block = &self.ast.blocks[block_id];
        let body_ret = self.analyze_body_with(block, body)?.0;
        self.sub_block(body_ret, *ret, block_id);
        Ok(Ty::UNIT)
    }

    fn analyze_trait(&self, trait_: &Trait, id: ExprId) -> Result<Ty<'tcx>> {
        _ = trait_;
        _ = id;
        todo!()
    }

    fn analyze_impl(&mut self, impl_: &Impl, id: ExprId) -> Result<Ty<'tcx>> {
        _ = id;
        let &Impl { ty, ref methods, .. } = impl_;
        self.impl_generics = self.produced_generics[&id];
        let ty = self.read_ast_ty(ty);
        for &method_id in methods {
            let ExprKind::FnDecl(func) = &self.ast.exprs[method_id].kind else { unreachable!() };
            self.analyze_method(ty, func, method_id)?;
        }
        Ok(Ty::UNIT)
    }

    fn read_ident(&self, ident: Symbol, span: Span) -> Result<Ty<'tcx>> {
        Ok(match self.read_ident_raw(ident, span)? {
            (Interned(TyKind::Function(func)), Var::Const) => {
                self.tcx.intern(TyKind::Function(func.caller(self.tcx)))
            }
            (other, _) => other,
        })
    }

    // like `read_ident` but will not produce `TyVid`s for generic functions
    fn read_ident_raw(&self, ident: Symbol, span: Span) -> Result<(Ty<'tcx>, Var)> {
        self.bodies
            .iter()
            .rev()
            .find_map(|body| body.scopes.iter().rev().find_map(|scope| scope.variables.get(&ident)))
            .copied()
            .ok_or_else(|| self.ident_not_found(ident, span))
    }

    fn analyze_lit(&mut self, lit: &Lit) -> Result<Ty<'tcx>> {
        Ok(match lit {
            Lit::FStr(fstr) => {
                for &segment in fstr {
                    self.analyze_expr(segment)?;
                }
                Ty::STR
            }
            Lit::Unit => Ty::UNIT,
            Lit::Bool(..) => Ty::BOOL,
            Lit::Int(..) => Ty::INT,
            Lit::Char(..) => Ty::CHAR,
            Lit::Str(..) => Ty::STR,
            Lit::Array { segments } => 'block: {
                let mut segments = segments.iter();
                let Some(first) = segments.next() else {
                    break 'block self.tcx.intern(TyKind::Array(self.tcx.new_infer()));
                };
                let first_ty = self.analyze_expr(first.expr)?;
                if let Some(repeated) = first.repeated {
                    let ty = self.analyze_expr(repeated)?;
                    self.eq(ty, Ty::INT, repeated);
                }
                for seg in segments {
                    let seg_ty = self.analyze_expr(seg.expr)?;
                    self.eq(first_ty, seg_ty, seg.expr);
                    if let Some(repeated) = seg.repeated {
                        let ty = self.analyze_expr(repeated)?;
                        self.eq(ty, Ty::INT, repeated);
                    }
                }
                self.tcx.intern(TyKind::Array(first_ty))
            }
        })
    }

    fn is_item(&self, id: ExprId) -> bool {
        matches!(
            self.ast.exprs[id].kind,
            ExprKind::FnDecl(..)
                | ExprKind::Struct { .. }
                | ExprKind::Impl(..)
                | ExprKind::Trait(..)
                | ExprKind::Const { .. }
        )
    }
    fn is_const(&self, id: ExprId) -> bool {
        match self.ast.exprs[id].kind {
            ExprKind::Lit(ref lit) => match lit {
                Lit::Bool(_) | Lit::Char(_) | Lit::Str(_) | Lit::Int(_) | Lit::Unit => true,
                Lit::Array { .. } => todo!(),
                Lit::FStr(_) => todo!(),
            },
            ExprKind::Binary { lhs, rhs, .. } => self.is_const(lhs) && self.is_const(rhs),
            ExprKind::Unary { expr, .. } => self.is_const(expr),
            _ => todo!(),
        }
    }
}
