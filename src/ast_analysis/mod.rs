mod errors;

use std::path::Path;

use index_vec::IndexVec;
use miette::Result;
use thin_vec::ThinVec;

use crate::{
    HashMap,
    ast::{
        self, Ast, BinOpKind, BinaryOp, Block, BlockId, ExprId, ExprKind, FnDecl, Identifier, Impl,
        Lit, Trait, TypeId, UnaryOp,
    },
    span::Span,
    symbol::Symbol,
    ty::{Function, GenericRange, Ty, TyCtx, TyKind},
};

#[derive(Default, Debug)]
pub struct TyInfo<'tcx> {
    pub expr_tys: IndexVec<ExprId, Ty<'tcx>>,
    pub type_ids: IndexVec<TypeId, Ty<'tcx>>,
    pub struct_types: HashMap<Span, Ty<'tcx>>,
    pub method_types: HashMap<ExprId, Ty<'tcx>>,
}

#[derive(Debug)]
struct Body<'tcx> {
    ty_names: HashMap<Symbol, Ty<'tcx>>,
    ret: Ty<'tcx>,
    scopes: Vec<Scope<'tcx>>,
    loops: usize,
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
}

fn setup_ty_info<'tcx>(ast: &Ast) -> TyInfo<'tcx> {
    let shared = &TyKind::Unit;
    TyInfo {
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
) -> Result<TyInfo<'tcx>> {
    let ty_info = setup_ty_info(ast);
    let body = global_body();
    let mut collector =
        Collector { path: file, src, ty_info, ast, tcx, bodies: vec![body], within_const: false };
    let top_level_exprs = ast.top_level.iter().copied().collect();
    let top_level = ast::Block { span: Span::ZERO, stmts: top_level_exprs, is_expr: false };
    collector.analyze_body_with(&top_level, Body::new(&TyKind::Never))?;

    let mut ty_info = std::mem::take(&mut collector.ty_info);
    for (expr, ty) in std::iter::zip(&ast.exprs, &mut ty_info.expr_tys) {
        *ty = tcx.try_infer_deep(ty).map_err(|ty| collector.cannot_infer(ty, expr.span))?;
    }
    ty_info.type_ids.iter_mut().for_each(|ty| *ty = tcx.infer_deep(ty));
    ty_info.method_types.values_mut().for_each(|ty| *ty = tcx.infer_deep(ty));

    Ok(ty_info)
}

fn global_body<'tcx>() -> Body<'tcx> {
    let mut body = Body::new(&TyKind::Never);
    let common = [
        ("bool", &TyKind::Bool),
        ("int", &TyKind::Int),
        ("char", &TyKind::Char),
        ("str", &TyKind::Str),
    ]
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
            let ExprKind::Struct { ident, fields } = &self.ast.exprs[*id].kind else {
                continue;
            };
            let symbols: ThinVec<_> = fields.iter().map(|field| field.ident.symbol).collect();
            let fields: ThinVec<_> =
                fields.iter().map(|field| self.read_ast_ty(field.ty)).collect::<Result<_>>()?;
            let params = fields.clone();
            let struct_ty = self.tcx.new_struct(ident.symbol, symbols, fields);
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
                ExprKind::FnDecl(func) => self.preanalyze_fndecl(&mut body, func)?,
                ExprKind::Impl(impl_) => {
                    let generics = self.tcx.new_generics(&impl_.generics);
                    let ty =
                        self.read_ast_ty_with(impl_.ty, None, [generics, GenericRange::EMPTY])?;
                    for func in &impl_.methods {
                        self.preanalyze_method(&mut body, ty, generics, func)?;
                    }
                }
                _ => {}
            }
        }
        self.bodies.push(body);
        let out = self.analyze_block_inner(block)?;
        Ok((out, self.bodies.pop().unwrap()))
    }

    fn preanalyze_fndecl(&mut self, body: &mut Body<'tcx>, fndecl: &FnDecl) -> Result<()> {
        let FnDecl { ident, generics, params, ret, .. } = fndecl;
        let generics = self.tcx.new_generics(generics);
        let ret = match ret {
            Some(ret) => self.read_ast_ty_with(*ret, None, [GenericRange::EMPTY, generics])?,
            None => &TyKind::Unit,
        };
        let params = params
            .iter()
            .map(|param| self.read_ast_ty_with(param.ty, None, [GenericRange::EMPTY, generics]))
            .collect::<Result<_>>()?;
        let prev = body.insert_var(
            *ident,
            self.tcx.intern(TyKind::Function(Function { params, ret })),
            Var::Const,
        );

        if prev.is_some() { Err(self.already_defined(*ident)) } else { Ok(()) }
    }

    fn preanalyze_method(
        &mut self,
        body: &mut Body<'tcx>,
        ty: Ty<'tcx>,
        impl_generics: GenericRange,
        fndecl: &FnDecl,
    ) -> Result<()> {
        _ = body;
        let FnDecl { ident, generics, params, ret, .. } = fndecl;
        let generics = self.tcx.new_generics(generics);
        let ret = match ret {
            Some(ret) => self.read_ast_ty_with(*ret, Some(ty), [impl_generics, generics])?,
            None => &TyKind::Unit,
        };
        let params = params
            .iter()
            .map(|param| self.read_ast_ty_with(param.ty, Some(ty), [impl_generics, generics]))
            .collect::<Result<_>>()?;

        let fn_ty = Function { params, ret };
        self.tcx.add_method(ty, ident.symbol, fn_ty);
        Ok(())
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
            ty.unwrap_or(&TyKind::Unit)
        } else if ty.is_some_and(TyKind::is_never) {
            &TyKind::Never
        } else {
            &TyKind::Unit
        })
    }

    fn read_ast_ty(&mut self, id: ast::TypeId) -> Result<Ty<'tcx>> {
        self.read_ast_ty_with(id, None, [GenericRange::EMPTY; 2])
    }

    fn read_ast_ty_with(
        &mut self,
        id: ast::TypeId,
        for_ty: Option<Ty<'tcx>>,
        generics: [GenericRange; 2],
    ) -> Result<Ty<'tcx>> {
        let ast_ty = &self.ast.types[id];
        let ty = match ast_ty.kind {
            ast::TyKind::Ref(of) => {
                self.tcx.intern(TyKind::Ref(self.read_ast_ty_with(of, for_ty, generics)?))
            }
            ast::TyKind::Func { ref params, ret } => {
                let ret = match ret {
                    Some(ty) => self.read_ast_ty_with(ty, for_ty, generics)?,
                    None => &TyKind::Unit,
                };
                let params = params
                    .iter()
                    .map(|param| self.read_ast_ty_with(*param, for_ty, generics))
                    .collect::<Result<_>>()?;
                self.tcx.intern(TyKind::Function(Function { params, ret }))
            }
            ast::TyKind::Never => &TyKind::Never,
            ast::TyKind::Unit => &TyKind::Unit,
            ast::TyKind::Array(of) => {
                self.tcx.intern(TyKind::Array(self.read_ast_ty_with(of, for_ty, generics)?))
            }
            ast::TyKind::Name(name) if name == "_" => self.tcx.new_infer(),
            ast::TyKind::Name(name) if name == "self" => match for_ty {
                Some(ty) => ty,
                None => return Err(self.invalid_self(ast_ty.span)),
            },
            ast::TyKind::Name(name) => {
                match (generics.iter().copied().flatten())
                    .find(|&g| self.tcx.generic_symbol(g) == name)
                {
                    Some(id) => self.tcx.intern(TyKind::Generic(id)),
                    None => self.read_named_ty(name, ast_ty.span)?,
                }
            }
        };
        self.ty_info.type_ids[id] = ty;
        Ok(ty)
    }

    fn read_named_ty(&self, name: Symbol, span: Span) -> Result<Ty<'tcx>> {
        if let Some(&ty) = self.bodies.iter().rev().find_map(|body| body.ty_names.get(&name)) {
            return Ok(ty);
        }
        Err(self.unknown_type_err(name, span))
    }

    fn eq(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, expr: ExprId) -> Result<()> {
        self.tcx.eq(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err(lhs, rhs, expr))
    }

    fn eq_block(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, block: BlockId) -> Result<()> {
        self.tcx.eq(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err_block(lhs, rhs, block))
    }

    fn sub(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, expr: ExprId) -> Result<()> {
        self.tcx.sub(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err(lhs, rhs, expr))
    }

    fn sub_block(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, block: BlockId) -> Result<()> {
        self.tcx.sub(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err_block(lhs, rhs, block))
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
                self.sub(ty, &TyKind::Bool, expr)?;
                &TyKind::Unit
            }
            ExprKind::Lit(ref lit) => self.analyze_lit(lit)?,
            ExprKind::Ident(ident) => self.read_ident(ident, expr_span)?,
            ExprKind::Unary { expr, op } => 'outer: {
                let operand = self.analyze_expr(expr)?;
                let ty = match op {
                    UnaryOp::Neg => &TyKind::Int,
                    UnaryOp::Not => &TyKind::Bool,
                    UnaryOp::Ref => break 'outer self.tcx.intern(TyKind::Ref(operand)),
                    UnaryOp::Deref => {
                        let operand = self.tcx.infer_shallow(operand);
                        let TyKind::Ref(inner) = operand else {
                            return Err(self.cannot_deref(operand, expr_span));
                        };
                        break 'outer inner;
                    }
                };
                self.sub(operand, ty, id)?;
                ty
            }
            ExprKind::Binary { lhs, op, rhs } => self.analyze_binary_expr(lhs, op, rhs)?,
            ExprKind::Index { expr, index } => self.index(expr, index, expr_span)?,
            ExprKind::FnCall { function, ref args } => {
                let fn_ty = self.analyze_expr(function)?;
                let TyKind::Function(Function { params, ret }) = fn_ty else {
                    let fn_span = self.ast.exprs[function].span;
                    return Err(self.expected_function(fn_ty, fn_span));
                };

                if args.len() != params.len() {
                    return Err(self.invalid_arg_count(
                        args.len(),
                        params.len(),
                        self.ast.exprs[function].span,
                        expr_span,
                    ));
                }

                for (&arg_id, param) in std::iter::zip(args, params) {
                    let arg = self.analyze_expr(arg_id)?;
                    self.sub(arg, param, arg_id)?;
                }
                ret
            }
            ExprKind::MethodCall { expr, method, ref args } => {
                let ty = self.tcx.infer_shallow(self.analyze_expr(expr)?);
                let Some(func) = self.tcx.get_method(ty, method.symbol) else {
                    return Err(self.method_not_found(ty, method));
                };
                let func = func.caller(self.tcx);

                let Function { ref params, ret } = func;

                if args.len() + 1 != params.len() {
                    return Err(self.invalid_arg_count(
                        args.len() + 1,
                        params.len(),
                        method.span,
                        expr_span,
                    ));
                }

                self.anyref_sub(ty, params[0], expr)?;

                for (&arg_id, param) in args.iter().zip(&params[1..]) {
                    let arg = self.analyze_expr(arg_id)?;
                    self.sub(arg, param, arg_id)?;
                }

                let fn_ty = self.tcx.intern(TyKind::Function(func));
                self.ty_info.method_types.insert(id, fn_ty);

                ret
            }
            ExprKind::FnDecl(ref decl) => self.analyze_fndecl(decl)?,
            ExprKind::Struct { .. } => &TyKind::Unit,
            ExprKind::Let { ident, ty, expr } => {
                let expr_ty = self.analyze_expr(expr)?;
                let ty = if let Some(ty) = ty {
                    let ty = self.read_ast_ty(ty)?;
                    self.sub(expr_ty, ty, expr)?;
                    ty
                } else {
                    expr_ty
                };
                self.insert_var(ident, ty, Var::Let);
                &TyKind::Unit
            }
            ExprKind::Const { ident, ty, expr } => {
                let within_const = std::mem::replace(&mut self.within_const, true);
                let expr_ty = self.analyze_expr(expr)?;
                self.within_const = within_const;
                let ty = if let Some(ty) = ty {
                    let ty = self.read_ast_ty(ty)?;
                    self.sub(expr_ty, ty, expr)?;
                    ty
                } else {
                    expr_ty
                };
                if self.tcx.try_infer_deep(ty).is_err() {
                    return Err(self.cannot_infer(ty, self.ast.spans([expr])));
                }
                self.insert_var(ident, ty, Var::Const);
                &TyKind::Unit
            }
            ExprKind::For { ident, iter, body } => {
                // for now only allow ranges
                let iter_ty = self.analyze_expr(iter)?;
                self.tcx.infer_shallow(iter_ty);
                let ident_ty = match iter_ty {
                    TyKind::Range => &TyKind::Int,
                    TyKind::Array(of) => of,
                    _ => return Err(self.cannot_iter(iter_ty, self.ast.exprs[iter].span)),
                };

                self.insert_var(ident, ident_ty, Var::Let);

                self.current().loops += 1;
                let out = self.analyze_block(body)?;
                self.current().loops -= 1;
                self.sub_block(out, &TyKind::Unit, body)?;
                &TyKind::Unit
            }
            ExprKind::While { condition, block } => {
                let condition_ty = self.analyze_expr(condition)?;
                self.sub(condition_ty, &TyKind::Bool, condition)?;
                self.current().loops += 1;
                self.analyze_block(block)?;
                self.current().loops -= 1;
                &TyKind::Unit
            }
            ExprKind::If { ref arms, els } => {
                let mut expected_ty = None;

                for arm in arms {
                    let ty = self.analyze_expr(arm.condition)?;
                    self.sub(ty, &TyKind::Bool, id)?;
                    let block_ty = self.analyze_block(arm.body)?;
                    if let Some(expected_ty) = expected_ty {
                        self.eq_block(expected_ty, block_ty, arm.body)?;
                    } else {
                        expected_ty = Some(block_ty);
                    }
                }
                let expected_ty = expected_ty.unwrap();
                if let Some(els) = els {
                    let block_ty = self.analyze_block(els)?;
                    self.sub_block(expected_ty, block_ty, els)?;
                } else {
                    // TODO: specialized error message here.
                    self.sub(expected_ty, &TyKind::Unit, id)?;
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
                    &TyKind::Unit
                }
            }
            ExprKind::Return(expr) => {
                let ty = expr.map_or(Ok(&TyKind::Unit), |expr| self.analyze_expr(expr))?;
                let expected = self.current().ret;
                self.sub(ty, expected, expr.unwrap_or(id))?;
                &TyKind::Never
            }
            ExprKind::Break => {
                if self.current().loops == 0 {
                    return Err(self.cannot_break(self.ast.exprs[id].span));
                }
                &TyKind::Never
            }
            ExprKind::Continue => {
                if self.current().loops == 0 {
                    return Err(self.cannot_continue(self.ast.exprs[id].span));
                }
                &TyKind::Never
            }
            ExprKind::Unreachable => &TyKind::Never,
            ExprKind::FieldAccess { expr, field } => {
                let expr = self.tcx.infer_shallow(self.analyze_expr(expr)?);
                let TyKind::Struct { symbols, fields, .. } = expr else {
                    return Err(self.field_error(expr, field));
                };
                let field = symbols
                    .iter()
                    .position(|&s| s == field.symbol)
                    .ok_or_else(|| self.field_error(expr, field))?;
                fields[field]
            }
        };
        self.ty_info.expr_tys[id] = ty;
        Ok(ty)
    }

    fn anyref_sub(&mut self, mut lhs: Ty<'tcx>, mut rhs: Ty<'tcx>, expr: ExprId) -> Result<()> {
        loop {
            lhs = self.tcx.infer_shallow(lhs);
            match lhs {
                TyKind::Ref(of) => lhs = of,
                _ => break,
            }
        }

        loop {
            rhs = self.tcx.infer_shallow(rhs);
            match rhs {
                TyKind::Ref(of) => rhs = of,
                _ => break,
            }
        }
        self.sub(lhs, rhs, expr)
    }

    fn insert_var(&mut self, ident: Identifier, ty: Ty<'tcx>, kind: Var) {
        self.current().insert_var(ident, ty, kind);
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
        self.sub(rhs_ty, lhs_ty, rhs)?;

        Ok(match op.kind {
            B::Assign
            | B::AddAssign
            | B::SubAssign
            | B::MulAssign
            | B::DivAssign
            | B::ModAssign => &TyKind::Unit,
            B::And | B::Or | B::Less | B::Greater | B::LessEq | B::GreaterEq | B::Eq | B::Neq => {
                &TyKind::Bool
            }
            B::RangeInclusive | B::Range => &TyKind::Range,
            B::Add | B::Sub | B::Mul | B::Div | B::Mod => lhs_ty,
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

        let matches = match lhs {
            TyKind::Int => op.is_op_assign() | op.is_arithmetic() | op.is_compare() | op.is_range(),
            TyKind::Str => op.is_compare() | op.is_add(),
            TyKind::Bool => op.is_eq() | op.is_logical(),
            TyKind::Char | TyKind::Unit => op.is_eq(),
            _ => false,
        };

        if matches {
            Ok(())
        } else {
            Err(if op.is_logical() {
                self.logical_op_err(lhs, rhs, lhs_expr, rhs_expr)
            } else {
                self.binop_err(op, lhs, rhs)
            })
        }
    }

    fn index(&mut self, expr: ExprId, index: ExprId, span: Span) -> Result<Ty<'tcx>> {
        let expr = self.analyze_expr(expr)?;
        let index = self.analyze_expr(index)?;
        let expr = self.tcx.infer_shallow(expr);
        self.index_ty(expr, index, span)
    }

    fn index_ty(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, span: Span) -> Result<Ty<'tcx>> {
        Ok(match (lhs, rhs) {
            (TyKind::Str, TyKind::Range) => &TyKind::Str,
            (TyKind::Array(_), TyKind::Range) => lhs,
            (TyKind::Array(of), TyKind::Int) => *of,
            (TyKind::Str, TyKind::Int) => &TyKind::Char,
            (TyKind::Ref(lhs), rhs) => return self.index_ty(lhs, rhs, span),
            _ => return Err(self.cannot_index(lhs, span)),
        })
    }

    fn analyze_method(&mut self, impl_: &Impl, decl: &FnDecl) -> Result<Ty<'tcx>> {
        let &FnDecl { ident, ref params, block, .. } = decl;
        let block_id = block.unwrap();
        let impl_generics = self.tcx.new_generics(&impl_.generics);

        let ty = self.read_ast_ty_with(impl_.ty, None, [GenericRange::EMPTY, impl_generics])?;
        let fn_ty = self.tcx.get_method(ty, ident.symbol).unwrap();

        let Function { params: param_tys, ret, .. } = fn_ty;

        let mut body = Body::new(ret);
        for (param, &ty) in std::iter::zip(params, param_tys) {
            body.insert_var(param.ident, ty, Var::Let);
        }
        let block = &self.ast.blocks[block_id];
        let body_ret = self.analyze_body_with(block, body)?.0;
        self.sub_block(body_ret, ret, block_id)?;
        Ok(&TyKind::Unit)
    }

    fn analyze_fndecl(&mut self, decl: &FnDecl) -> Result<Ty<'tcx>> {
        let &FnDecl { ident, ref params, block, .. } = decl;
        let block_id = block.unwrap();
        // call `read_ident_raw` to avoid producing extra inference variables
        let (fn_ty, _) = self
            .read_ident_raw(ident.symbol, Span::ZERO)
            .expect("fndecl ident should have been inserted already");
        let TyKind::Function(Function { params: param_tys, ret, .. }) = fn_ty else {
            unreachable!()
        };
        let mut body = Body::new(ret);
        for (param, &ty) in std::iter::zip(params, param_tys) {
            body.insert_var(param.ident, ty, Var::Let);
        }
        let block = &self.ast.blocks[block_id];
        let body_ret = self.analyze_body_with(block, body)?.0;
        self.sub_block(body_ret, ret, block_id)?;
        Ok(&TyKind::Unit)
    }

    fn analyze_trait(&mut self, trait_: &Trait, id: ExprId) -> Result<Ty<'tcx>> {
        _ = id;
        let &Trait { ident, ref methods } = trait_;
        _ = ident;
        for func in methods {
            self.analyze_fndecl(func)?;
        }
        Ok(&TyKind::Unit)
    }

    fn analyze_impl(&mut self, impl_: &Impl, id: ExprId) -> Result<Ty<'tcx>> {
        _ = id;
        let &Impl { ty, ref generics, ref methods } = impl_;
        _ = ty;
        _ = generics;
        for func in methods {
            self.analyze_method(impl_, func)?;
        }
        Ok(&TyKind::Unit)
    }

    fn read_ident(&self, ident: Symbol, span: Span) -> Result<Ty<'tcx>> {
        Ok(match self.read_ident_raw(ident, span)? {
            (TyKind::Function(func), Var::Const) => {
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
                &TyKind::Str
            }
            Lit::Unit => &TyKind::Unit,
            Lit::Bool(..) => &TyKind::Bool,
            Lit::Int(..) => &TyKind::Int,
            Lit::Char(..) => &TyKind::Char,
            Lit::Str(..) => &TyKind::Str,
            Lit::Array { segments } => 'block: {
                let mut segments = segments.iter();
                let Some(first) = segments.next() else {
                    break 'block self.tcx.intern(TyKind::Array(self.tcx.new_infer()));
                };
                let first_ty = self.analyze_expr(first.expr)?;
                if let Some(repeated) = first.repeated {
                    let ty = self.analyze_expr(repeated)?;
                    self.eq(ty, &TyKind::Int, repeated)?;
                }
                for seg in segments {
                    let seg_ty = self.analyze_expr(seg.expr)?;
                    self.eq(first_ty, seg_ty, seg.expr)?;
                    if let Some(repeated) = seg.repeated {
                        let ty = self.analyze_expr(repeated)?;
                        self.eq(ty, &TyKind::Int, repeated)?;
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
