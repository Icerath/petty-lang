mod errors;

use std::path::Path;

use index_vec::IndexVec;
use miette::Result;
use thin_vec::ThinVec;

use crate::{
    HashMap,
    ast::{
        self, Ast, BinOpKind, BinaryOp, Block, BlockId, ExprId, ExprKind, FnDecl, Impl, Lit, Trait,
        TypeId, UnaryOp,
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
}

#[derive(Debug)]
struct Body<'tcx> {
    ty_names: HashMap<Symbol, Ty<'tcx>>,
    variables: HashMap<Symbol, Ty<'tcx>>,
    ret: Ty<'tcx>,
}

impl<'tcx> Body<'tcx> {
    pub fn new(ret: Ty<'tcx>) -> Self {
        Self { ty_names: HashMap::default(), variables: HashMap::default(), ret }
    }
}

struct Collector<'src, 'ast, 'tcx> {
    ty_info: TyInfo<'tcx>,
    bodies: Vec<Body<'tcx>>,
    ast: &'ast Ast,
    tcx: &'tcx TyCtx<'tcx>,
    src: &'src str,
    file: Option<&'src Path>,
}

fn setup_ty_info<'tcx>(ast: &Ast) -> TyInfo<'tcx> {
    let shared = &TyKind::Unit;
    TyInfo {
        expr_tys: std::iter::repeat_n(shared, ast.exprs.len()).collect(),
        type_ids: std::iter::repeat_n(shared, ast.types.len()).collect(),
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
    let mut collector = Collector { file, src, ty_info, ast, tcx, bodies: vec![body] };
    let top_level_exprs = ast.top_level.iter().copied().collect();
    let top_level = ast::Block { span: Span::ZERO, stmts: top_level_exprs, is_expr: false };
    collector.analyze_body_with(&top_level, Body::new(&TyKind::Never))?;

    let mut ty_info = std::mem::take(&mut collector.ty_info);
    for (expr, ty) in std::iter::zip(&ast.exprs, &mut ty_info.expr_tys) {
        *ty = tcx.try_infer_deep(ty).map_err(|ty| collector.cannot_infer(ty, expr.span))?;
    }
    ty_info.type_ids.iter_mut().for_each(|ty| *ty = tcx.infer_deep(ty));

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
            let ExprKind::Struct { ident, fields, span } = &self.ast.exprs[*id].kind else {
                continue;
            };
            let symbols: ThinVec<_> = fields.iter().map(|field| field.ident).collect();
            let fields: ThinVec<_> =
                fields.iter().map(|field| self.read_ast_ty(field.ty)).collect::<Result<_>>()?;
            let params = fields.clone();
            let struct_ty = self.tcx.new_struct(*ident, symbols, fields);
            self.current().ty_names.insert(*ident, struct_ty);
            self.ty_info.struct_types.insert(*span, struct_ty);

            body.variables.insert(
                *ident,
                self.tcx.intern(TyKind::Function(Function { params, ret: struct_ty })),
            );
        }

        for &id in &block.stmts {
            let ExprKind::FnDecl(FnDecl { ident, generics, params, ret, .. }) =
                &self.ast.exprs[id].kind
            else {
                continue;
            };
            let generics = self.tcx.new_generics(generics);
            let ret = match ret {
                Some(ret) => self.read_ast_ty_with(*ret, generics)?,
                None => &TyKind::Unit,
            };
            let params = params
                .iter()
                .map(|param| self.read_ast_ty_with(param.ty, generics))
                .collect::<Result<_>>()?;
            body.variables
                .insert(*ident, self.tcx.intern(TyKind::Function(Function { params, ret })));
        }
        self.bodies.push(body);
        let out = self.analyze_block_inner(block)?;
        Ok((out, self.bodies.pop().unwrap()))
    }

    fn current(&mut self) -> &mut Body<'tcx> {
        self.bodies.last_mut().unwrap()
    }

    fn analyze_block(&mut self, id: BlockId) -> Result<Ty<'tcx>> {
        let block = &self.ast.blocks[id];
        self.analyze_block_inner(block)
    }

    fn analyze_block_inner(&mut self, block: &Block) -> Result<Ty<'tcx>> {
        let mut ty = None;
        for &id in &block.stmts {
            ty = Some(self.analyze_expr(id)?);
        }
        Ok(if block.is_expr {
            ty.unwrap_or(&TyKind::Unit)
        } else if ty.is_some_and(TyKind::is_never) {
            &TyKind::Never
        } else {
            &TyKind::Unit
        })
    }

    fn read_ast_ty(&mut self, id: ast::TypeId) -> Result<Ty<'tcx>> {
        self.read_ast_ty_with(id, GenericRange::EMPTY)
    }

    fn read_ast_ty_with(&mut self, id: ast::TypeId, generics: GenericRange) -> Result<Ty<'tcx>> {
        let ast_ty = &self.ast.types[id];
        let ty = match ast_ty.kind {
            ast::TyKind::Ref(of) => {
                self.tcx.intern(TyKind::Ref(self.read_ast_ty_with(of, generics)?))
            }
            ast::TyKind::Func { ref params, ret } => {
                let ret = match ret {
                    Some(ty) => self.read_ast_ty_with(ty, generics)?,
                    None => &TyKind::Unit,
                };
                let params = params
                    .iter()
                    .map(|param| self.read_ast_ty_with(*param, generics))
                    .collect::<Result<_>>()?;
                self.tcx.intern(TyKind::Function(Function { params, ret }))
            }
            ast::TyKind::Never => &TyKind::Never,
            ast::TyKind::Unit => &TyKind::Unit,
            ast::TyKind::Array(of) => {
                self.tcx.intern(TyKind::Array(self.read_ast_ty_with(of, generics)?))
            }
            ast::TyKind::Name(name) if name == "_" => self.tcx.new_infer(),
            ast::TyKind::Name(name) => {
                match generics.iter().find(|&g| self.tcx.generic_symbol(g) == name) {
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
        Err(self.unknown_type_err(span))
    }

    fn eq(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, expr: ExprId) -> Result<()> {
        self.tcx.eq(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err(lhs, rhs, expr))
    }

    fn eq_block(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, block: BlockId) -> Result<()> {
        self.tcx.eq(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err_block(lhs, rhs, block))
    }

    fn subtype(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, expr: ExprId) -> Result<()> {
        self.tcx.sub(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err(lhs, rhs, expr))
    }

    fn subtype_block(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, block: BlockId) -> Result<()> {
        self.tcx.sub(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err_block(lhs, rhs, block))
    }

    #[expect(clippy::too_many_lines)]
    fn analyze_expr(&mut self, id: ExprId) -> Result<Ty<'tcx>> {
        let expr_span = self.ast.exprs[id].span;
        let ty = match self.ast.exprs[id].kind {
            ExprKind::Trait(ref trait_) => self.analyze_trait(trait_, id)?,
            ExprKind::Impl(ref impl_) => self.analyze_impl(impl_, id)?,
            ExprKind::Assert(expr) => {
                let ty = self.analyze_expr(expr)?;
                self.subtype(ty, &TyKind::Bool, expr)?;
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
                self.subtype(operand, ty, id)?;
                ty
            }
            ExprKind::Binary { lhs, op, rhs } => self.analyze_binary_expr(lhs, op, rhs)?,
            ExprKind::Index { expr, index } => self.index(expr, index, expr_span)?,
            ExprKind::FnCall { function, ref args } => {
                let fn_ty = self.analyze_expr(function)?;
                let TyKind::Function(func) = fn_ty else {
                    let fn_span = self.ast.exprs[function].span;
                    return Err(self.expected_function(fn_ty, fn_span));
                };

                let (params, ret) = func.caller(self.tcx);

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
                    self.subtype(arg, param, arg_id)?;
                }
                ret
            }
            ExprKind::FnDecl(ref decl) => self.analyze_fndecl(decl)?,
            ExprKind::Struct { .. } => &TyKind::Unit,
            ExprKind::Let { ident, ty, expr } => {
                let expr_ty = self.analyze_expr(expr)?;
                let ty = if let Some(ty) = ty {
                    let ty = self.read_ast_ty(ty)?;
                    self.subtype(expr_ty, ty, expr)?;
                    ty
                } else {
                    expr_ty
                };
                self.current().variables.insert(ident, ty);
                &TyKind::Unit
            }
            ExprKind::For { ident, iter, body } => {
                // for now only allow ranges
                let iter_ty = self.analyze_expr(iter)?;
                self.subtype(iter_ty, &TyKind::Range, iter)?;
                self.current().variables.insert(ident, &TyKind::Int);
                let out = self.analyze_block(body)?;
                self.subtype_block(out, &TyKind::Unit, body)?;
                &TyKind::Unit
            }
            ExprKind::While { condition, block } => {
                let condition_ty = self.analyze_expr(condition)?;
                self.subtype(condition_ty, &TyKind::Bool, condition)?;
                self.analyze_block(block)?;
                &TyKind::Unit
            }
            ExprKind::If { ref arms, els } => {
                let mut expected_ty = None;

                for arm in arms {
                    let ty = self.analyze_expr(arm.condition)?;
                    self.subtype(ty, &TyKind::Bool, id)?;
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
                    self.subtype_block(expected_ty, block_ty, els)?;
                } else {
                    // TODO: specialized error message here.
                    self.subtype(expected_ty, &TyKind::Unit, id)?;
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
                self.subtype(ty, expected, expr.unwrap_or(id))?;
                &TyKind::Never
            }
            ExprKind::Break | ExprKind::Unreachable => &TyKind::Never,
            ExprKind::FieldAccess { expr, field, span } => {
                let expr = self.tcx.infer_shallow(self.analyze_expr(expr)?);
                let TyKind::Struct { symbols, fields, .. } = expr else {
                    return Err(self.field_error(expr, field, span));
                };
                let field = symbols
                    .iter()
                    .position(|&s| s == field)
                    .ok_or_else(|| self.field_error(expr, field, span))?;
                fields[field]
            }
            ExprKind::MethodCall { .. } => todo!(),
        };
        self.ty_info.expr_tys[id] = ty;
        Ok(ty)
    }

    fn analyze_binary_expr(&mut self, lhs: ExprId, op: BinaryOp, rhs: ExprId) -> Result<Ty<'tcx>> {
        let mut lhs_ty = self.analyze_expr(lhs)?;
        let mut rhs_ty = self.analyze_expr(rhs)?;

        match op.kind {
            BinOpKind::Assign => {}
            BinOpKind::AddAssign
            | BinOpKind::SubAssign
            | BinOpKind::MulAssign
            | BinOpKind::DivAssign
            | BinOpKind::ModAssign => rhs_ty = rhs_ty.fully_deref(),
            _ => {
                lhs_ty = lhs_ty.fully_deref();
                rhs_ty = rhs_ty.fully_deref();
            }
        }

        self.enforce_valid_binop(lhs_ty, op, rhs_ty)?;

        Ok(match op.kind {
            BinOpKind::Assign
            | BinOpKind::AddAssign
            | BinOpKind::SubAssign
            | BinOpKind::MulAssign
            | BinOpKind::DivAssign
            | BinOpKind::ModAssign => {
                self.subtype(rhs_ty, lhs_ty, rhs)?;
                &TyKind::Unit
            }
            BinOpKind::Less
            | BinOpKind::Greater
            | BinOpKind::LessEq
            | BinOpKind::GreaterEq
            | BinOpKind::Eq
            | BinOpKind::Neq => &TyKind::Bool,
            BinOpKind::Range | BinOpKind::RangeInclusive => {
                self.eq(lhs_ty, rhs_ty, rhs)?;

                match op.kind {
                    BinOpKind::Range => self.tcx.intern(TyKind::Range),
                    BinOpKind::RangeInclusive => self.tcx.intern(TyKind::RangeInclusive),
                    _ => unreachable!(),
                }
            }
            BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div | BinOpKind::Mod => {
                self.eq(lhs_ty, rhs_ty, rhs)?;
                lhs_ty
            }
        })
    }

    fn enforce_valid_binop(&self, lhs: Ty<'tcx>, op: BinaryOp, rhs: Ty<'tcx>) -> Result<()> {
        if let BinOpKind::Assign = op.kind {
            return Ok(());
        }

        let lhs = self.tcx.infer_shallow(lhs);
        let rhs = self.tcx.infer_shallow(rhs);

        macro_rules! filter {
            ($([$ty:ident => $($op:ident)|+])+) => {
                $((matches!(lhs, TyKind::$ty) && matches!(op.kind, $(BinOpKind::$op)|+))) || +
            };
        }

        let matches = filter! {
            [Int => Add | Sub | Mul | Div | Mod | AddAssign | SubAssign | MulAssign | DivAssign | ModAssign
                | Eq | Neq | Less | LessEq | Greater | GreaterEq | Range | RangeInclusive
            ]
            [Str => Add | AddAssign | Less | Greater | LessEq | GreaterEq | Eq | Neq]
            [Bool => Eq | Neq]
            [Char => Eq | Neq]
            [Unit => Eq | Neq]
        };
        if matches { Ok(()) } else { Err(self.binop_err(op, lhs, rhs)) }
    }

    fn index(&mut self, expr: ExprId, index: ExprId, span: Span) -> Result<Ty<'tcx>> {
        let expr = self.analyze_expr(expr)?;
        let index = self.analyze_expr(index)?;
        let expr = self.tcx.infer_shallow(expr);
        self.index_ty(expr, index, span)
    }

    fn index_ty(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, span: Span) -> Result<Ty<'tcx>> {
        Ok(match (lhs, rhs) {
            (TyKind::Str, TyKind::Range | TyKind::RangeInclusive) => &TyKind::Str,
            (TyKind::Array(_), TyKind::Range | TyKind::RangeInclusive) => lhs,
            (TyKind::Array(of), TyKind::Int) => *of,
            (TyKind::Str, TyKind::Int) => &TyKind::Char,
            (TyKind::Ref(lhs), rhs) => return self.index_ty(lhs, rhs, span),
            _ => return Err(self.cannot_index(lhs, span)),
        })
    }

    fn analyze_fndecl(&mut self, decl: &FnDecl) -> Result<Ty<'tcx>> {
        let &FnDecl { ident, ref generics, ref params, ret, block } = decl;
        _ = generics;
        _ = ret;
        let block_id = block.unwrap();
        let fn_ty = self.current().variables[&ident];
        let TyKind::Function(Function { params: param_tys, ret, .. }) = fn_ty else {
            unreachable!()
        };
        let mut body = Body::new(ret);
        for (param, ty) in std::iter::zip(params, param_tys) {
            body.variables.insert(param.ident, *ty);
        }
        let block = &self.ast.blocks[block_id];
        let body_ret = self.analyze_body_with(block, body)?.0;
        self.subtype_block(body_ret, ret, block_id)?;
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
        let &Impl { trait_, ty, ref methods } = impl_;
        _ = trait_;
        _ = ty;
        for func in methods {
            self.analyze_fndecl(func)?;
        }
        Ok(&TyKind::Unit)
    }

    fn read_ident(&self, ident: Symbol, span: Span) -> Result<Ty<'tcx>> {
        (self.bodies.iter().rev().find_map(|body| body.variables.get(&ident)).copied())
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
}
