mod errors;

use std::path::Path;

use index_vec::IndexVec;
use miette::Result;
use thin_vec::ThinVec;

use crate::{
    HashMap,
    ast::{
        self, Ast, BinOpKind, BinaryOp, Block, BlockId, ExprId, ExprKind, FnDecl, Lit, TypeId,
        UnaryOp,
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

    let mut ty_info = collector.ty_info;
    ty_info.expr_tys.iter_mut().for_each(|ty| *ty = tcx.infer_deep(ty));
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
                fields.iter().map(|field| self.read_ast_ty(field.ty)).collect();
            let params = fields.clone();
            let struct_ty = self.tcx.new_struct(*ident, symbols, fields);
            self.bodies.last_mut().unwrap().ty_names.insert(*ident, struct_ty);
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
                Some(ret) => self.read_ast_ty_with(*ret, generics),
                None => &TyKind::Unit,
            };
            let params =
                params.iter().map(|param| self.read_ast_ty_with(param.ty, generics)).collect();
            body.variables
                .insert(*ident, self.tcx.intern(TyKind::Function(Function { params, ret })));
        }
        self.bodies.push(body);
        let out = self.analyze_block_inner(block)?;
        Ok((out, self.bodies.pop().unwrap()))
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

    #[track_caller]
    fn read_ast_ty(&mut self, id: ast::TypeId) -> Ty<'tcx> {
        self.read_ast_ty_with(id, GenericRange::EMPTY)
    }

    #[track_caller]
    fn read_ast_ty_with(&mut self, id: ast::TypeId, generics: GenericRange) -> Ty<'tcx> {
        let ty = match self.ast.types[id] {
            ast::Ty::Func { ref params, ret } => {
                let ret = ret.map_or(&TyKind::Unit, |ty| self.read_ast_ty_with(ty, generics));
                let params =
                    params.iter().map(|param| self.read_ast_ty_with(*param, generics)).collect();
                self.tcx.intern(TyKind::Function(Function { params, ret }))
            }
            ast::Ty::Never => &TyKind::Never,
            ast::Ty::Unit => &TyKind::Unit,
            ast::Ty::Array(of) => {
                self.tcx.intern(TyKind::Array(self.read_ast_ty_with(of, generics)))
            }
            ast::Ty::Name(name) => {
                match generics.iter().find(|&g| self.tcx.generic_symbol(g) == name) {
                    Some(id) => self.tcx.intern(TyKind::Generic(id)),
                    None => self.read_named_ty(name),
                }
            }
        };
        self.ty_info.type_ids[id] = ty;
        ty
    }

    #[track_caller]
    fn read_named_ty(&self, name: Symbol) -> Ty<'tcx> {
        self.bodies.iter().rev().find_map(|body| body.ty_names.get(&name)).unwrap()
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
        let ty = match self.ast.exprs[id].kind {
            ExprKind::Assert(expr) => {
                let ty = self.analyze_expr(expr)?;
                self.subtype(ty, &TyKind::Bool, expr)?;
                &TyKind::Unit
            }
            ExprKind::Lit(ref lit) => self.analyze_lit(lit)?,
            ExprKind::Ident(ident) => self.read_ident(ident)?,
            ExprKind::Unary { expr, op } => {
                let operand = self.analyze_expr(expr)?;
                let ty = match op {
                    UnaryOp::Neg => &TyKind::Int,
                    UnaryOp::Not => &TyKind::Bool,
                };
                self.subtype(operand, ty, id)?;
                ty
            }
            ExprKind::Binary {
                lhs,
                rhs,
                op:
                    BinaryOp {
                        kind:
                            BinOpKind::Assign
                            | BinOpKind::AddAssign
                            | BinOpKind::SubAssign
                            | BinOpKind::MulAssign
                            | BinOpKind::DivAssign,
                        ..
                    },
            } => {
                let lhs_ty = self.analyze_expr(lhs)?;
                let rhs_ty = self.analyze_expr(rhs)?;
                self.subtype(rhs_ty, lhs_ty, rhs)?;
                &TyKind::Unit
            }
            ExprKind::Binary {
                lhs,
                rhs,
                op:
                    BinaryOp {
                        kind:
                            BinOpKind::Less
                            | BinOpKind::Greater
                            | BinOpKind::LessEq
                            | BinOpKind::GreaterEq
                            | BinOpKind::Eq
                            | BinOpKind::Neq,
                        ..
                    },
            } => {
                let lhs = self.analyze_expr(lhs)?;
                let rhs_ty = self.analyze_expr(rhs)?;
                self.eq(lhs, rhs_ty, rhs)?;
                &TyKind::Bool
            }
            ExprKind::Binary {
                lhs,
                rhs,
                op: op @ BinaryOp { kind: BinOpKind::Range | BinOpKind::RangeInclusive, .. },
            } => {
                let lhs = self.analyze_expr(lhs)?;
                let rhs_ty = self.analyze_expr(rhs)?;
                self.eq(lhs, rhs_ty, rhs)?;

                self.subtype(lhs, &TyKind::Int, id)?;
                self.subtype(rhs_ty, &TyKind::Int, id)?;

                match op.kind {
                    BinOpKind::Range => self.tcx.intern(TyKind::Range),
                    BinOpKind::RangeInclusive => self.tcx.intern(TyKind::RangeInclusive),
                    _ => unreachable!(),
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                let lhs = self.analyze_expr(lhs)?;
                let rhs_ty = self.analyze_expr(rhs)?;
                self.eq(lhs, rhs_ty, rhs)?;
                lhs
            }
            ExprKind::Index { expr, index } => {
                let expr = self.analyze_expr(expr)?;
                let index = self.analyze_expr(index)?;
                let expr = self.tcx.infer_shallow(expr);
                match (expr, index) {
                    (TyKind::Str, TyKind::Range | TyKind::RangeInclusive) => &TyKind::Str,
                    (TyKind::Array(_), TyKind::Range | TyKind::RangeInclusive) => expr,

                    (TyKind::Array(of), TyKind::Int) => *of,
                    (TyKind::Str, TyKind::Int) => &TyKind::Char,
                    _ => panic!("Cannot index `{expr:?}`"),
                }
            }
            ExprKind::FnCall { function, ref args } => {
                let fn_ty = self.analyze_expr(function)?;
                let TyKind::Function(func) = fn_ty else {
                    panic!("expected `function`, found {fn_ty:?}");
                };
                let (params, ret) = func.caller(self.tcx);
                assert_eq!(args.len(), params.len());

                for (&arg, param) in std::iter::zip(args, params) {
                    let arg = self.analyze_expr(arg)?;
                    self.subtype(arg, param, id)?;
                }
                ret
            }
            ExprKind::FnDecl(FnDecl { ident, ref params, block, .. }) => {
                let fn_ty = self.bodies.last().unwrap().variables[&ident];
                let TyKind::Function(Function { params: param_tys, ret, .. }) = fn_ty else {
                    unreachable!()
                };
                let mut body = Body::new(ret);
                for (param, ty) in std::iter::zip(params, param_tys) {
                    body.variables.insert(param.ident, *ty);
                }
                let block = &self.ast.blocks[block];
                let body_ret = self.analyze_body_with(block, body)?.0;
                self.subtype(body_ret, ret, id)?;
                &TyKind::Unit
            }
            ExprKind::Struct { .. } => &TyKind::Unit,
            ExprKind::Let { ident, ty, expr } => {
                let expr_ty = self.analyze_expr(expr)?;
                let ty = if let Some(ty) = ty {
                    let ty = self.read_ast_ty(ty);
                    self.subtype(expr_ty, ty, expr)?;
                    ty
                } else {
                    expr_ty
                };
                let body = self.bodies.last_mut().unwrap();
                body.variables.insert(ident, ty);
                &TyKind::Unit
            }
            ExprKind::For { ident, iter, body } => {
                // for now only allow ranges
                let iter_ty = self.analyze_expr(iter)?;
                self.subtype(iter_ty, &TyKind::Range, iter)?;
                self.bodies.last_mut().unwrap().variables.insert(ident, &TyKind::Int);
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
                let expected = self.bodies.last().unwrap().ret;
                self.subtype(ty, expected, expr.unwrap_or(id))?;
                &TyKind::Never
            }
            ExprKind::Break | ExprKind::Unreachable => &TyKind::Never,
            ExprKind::FieldAccess { expr, field } => {
                let expr = self.tcx.infer_shallow(self.analyze_expr(expr)?);
                let TyKind::Struct { symbols, fields, .. } = expr else { panic!() };
                let field = symbols
                    .iter()
                    .position(|&s| s == field)
                    .unwrap_or_else(|| panic!("unknown field: {field}"));
                fields[field]
            }
            ExprKind::MethodCall { .. } => todo!(),
        };
        self.ty_info.expr_tys[id] = ty;
        Ok(ty)
    }

    fn read_ident(&self, ident: Symbol) -> Result<Ty<'tcx>> {
        self.bodies
            .iter()
            .rev()
            .find_map(|body| body.variables.get(&ident))
            .copied()
            .ok_or_else(|| miette::miette!("todo: {ident}"))
    }

    fn analyze_lit(&mut self, lit: &Lit) -> Result<Ty<'tcx>> {
        Ok(match lit {
            Lit::Abort => &TyKind::Never,
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
