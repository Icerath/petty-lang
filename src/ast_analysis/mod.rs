use crate::{
    ast::{self, Ast, BinaryOp, Block, BlockId, Expr, ExprId, Lit, TypeId, UnaryOp},
    symbol::Symbol,
    ty::{Ty, TyCtx, TyKind},
};
use std::collections::HashMap;

use index_vec::IndexVec;

#[derive(Default, Debug)]
pub struct TyInfo {
    pub expr_tys: IndexVec<ExprId, Ty>,
    pub type_ids: IndexVec<TypeId, Ty>,
}

#[derive(Debug)]
struct Body {
    ty_names: HashMap<Symbol, Ty>,
    variables: HashMap<Symbol, Ty>,
    ret: Ty,
}

impl Body {
    pub fn new(ret: Ty) -> Self {
        Self { ty_names: HashMap::default(), variables: HashMap::default(), ret }
    }
}

struct Collector<'ast, 'tcx> {
    ty_info: TyInfo,
    bodies: Vec<Body>,
    ast: &'ast Ast,
    tcx: &'tcx TyCtx,
}

fn setup_ty_info(ast: &Ast, tcx: &TyCtx) -> TyInfo {
    let shared = tcx.unit().clone();
    TyInfo {
        expr_tys: std::iter::repeat_n(shared.clone(), ast.exprs.len()).collect(),
        type_ids: std::iter::repeat_n(shared, ast.types.len()).collect(),
    }
}

pub fn analyze(ast: &Ast, tcx: &TyCtx) -> TyInfo {
    let ty_info = setup_ty_info(ast, tcx);
    let body = global_body(tcx);
    let mut collector = Collector { ty_info, ast, tcx, bodies: vec![body] };
    let top_level_exprs = ast.top_level.iter().copied().collect();
    let top_level = ast::Block { stmts: top_level_exprs, is_expr: false };
    collector.analyze_body_with(&top_level, Body::new(tcx.never().clone()));

    let mut ty_info = collector.ty_info;
    ty_info.expr_tys.iter_mut().for_each(|ty| *ty = tcx.infer_deep(ty));
    ty_info.type_ids.iter_mut().for_each(|ty| *ty = tcx.infer_deep(ty));

    ty_info
}

fn global_body(tcx: &TyCtx) -> Body {
    let mut body = Body::new(tcx.never().clone());
    let common =
        [("bool", tcx.bool()), ("int", tcx.int()), ("char", tcx.char()), ("str", tcx.str())]
            .map(|(name, ty)| (Symbol::from(name), ty.clone()));
    body.ty_names.extend(common);
    body
}

impl Collector<'_, '_> {
    fn analyze_body_with(&mut self, block: &ast::Block, mut body: Body) -> (Ty, Body) {
        // look for structs/enums first.
        // for stmt in &*ast.top_level.borrow() {}

        for &id in &block.stmts {
            let Expr::FnDecl { ident, params, ret, .. } = &self.ast.exprs[id] else { continue };
            let ret = match ret {
                Some(ret) => self.read_ast_ty(*ret),
                None => self.tcx.unit().clone(),
            };
            let params = params.iter().map(|param| self.read_ast_ty(param.ty)).collect();
            body.variables.insert(*ident, Ty::from(TyKind::Function { params, ret }));
        }
        self.bodies.push(body);
        let out = self.analyze_block_inner(block);
        (out, self.bodies.pop().unwrap())
    }

    fn analyze_block(&mut self, id: BlockId) -> Ty {
        let block = &self.ast.blocks[id];
        self.analyze_block_inner(block)
    }

    fn analyze_block_inner(&mut self, block: &Block) -> Ty {
        let mut ty = None;
        for &id in &block.stmts {
            ty = Some(self.analyze_expr(id));
        }
        if block.is_expr {
            ty.unwrap_or_else(|| self.tcx.unit().clone())
        } else if ty.is_some_and(|ty| *ty.kind() == TyKind::Never) {
            self.tcx.never().clone()
        } else {
            self.tcx.unit().clone()
        }
    }

    fn read_ast_ty(&mut self, id: ast::TypeId) -> Ty {
        let ty = match self.ast.types[id] {
            ast::Ty::Never => self.tcx.never().clone(),
            ast::Ty::Unit => self.tcx.unit().clone(),
            ast::Ty::Array(of) => TyKind::Array(self.read_ast_ty(of)).into(),
            ast::Ty::Name(name) => self.read_named_ty(name),
        };
        self.ty_info.type_ids[id] = ty.clone();
        ty
    }

    fn read_named_ty(&self, name: Symbol) -> Ty {
        self.bodies.iter().rev().find_map(|body| body.ty_names.get(&name)).unwrap().clone()
    }

    #[must_use]
    #[expect(clippy::too_many_lines)]
    fn analyze_expr(&mut self, id: ExprId) -> Ty {
        match &self.ast.exprs[id] {
            Expr::Lit(lit) => self.analyze_lit(lit, id),
            &Expr::Ident(ident) => _ = self.read_ident(ident, id),
            &Expr::Unary { expr, op } => {
                let operand = self.analyze_expr(expr);
                let ty = match op {
                    UnaryOp::Neg => self.tcx.int(),
                    UnaryOp::Not => self.tcx.bool(),
                };
                self.tcx.subtype(&operand, ty);
                self.ty_info.expr_tys[id] = ty.clone();
            }
            &Expr::Binary {
                lhs,
                rhs,
                op:
                    BinaryOp::Assign
                    | BinaryOp::AddAssign
                    | BinaryOp::SubAssign
                    | BinaryOp::MulAssign
                    | BinaryOp::DivAssign,
            } => {
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.tcx.subtype(&rhs, &lhs);
            }
            &Expr::Binary {
                lhs,
                rhs,
                op:
                    BinaryOp::Less
                    | BinaryOp::Greater
                    | BinaryOp::LessEq
                    | BinaryOp::GreaterEq
                    | BinaryOp::Eq
                    | BinaryOp::Neq,
            } => {
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.tcx.eq(&lhs, &rhs);
                self.ty_info.expr_tys[id] = self.tcx.bool().clone();
            }
            &Expr::Binary { lhs, rhs, op: op @ (BinaryOp::Range | BinaryOp::RangeInclusive) } => {
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.tcx.eq(&lhs, &rhs);

                self.tcx.subtype(&lhs, self.tcx.int());
                self.tcx.subtype(&rhs, self.tcx.int());

                let ty = match op {
                    BinaryOp::Range => TyKind::Range.into(),
                    BinaryOp::RangeInclusive => TyKind::RangeInclusive.into(),
                    _ => unreachable!(),
                };
                self.ty_info.expr_tys[id] = ty;
            }
            &Expr::Binary { lhs, rhs, .. } => {
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.tcx.eq(&lhs, &rhs);
                self.ty_info.expr_tys[id] = lhs;
            }
            &Expr::Index { expr, index } => {
                let expr = self.analyze_expr(expr);
                let index = self.analyze_expr(index);
                let expr = self.tcx.infer_shallow(&expr);
                let out = match (expr.kind(), index.kind()) {
                    (TyKind::Str, TyKind::Range | TyKind::RangeInclusive) => self.tcx.str().clone(),
                    (TyKind::Array(_), TyKind::Range | TyKind::RangeInclusive) => expr,

                    (TyKind::Array(of), TyKind::Int) => of.clone(),
                    (TyKind::Str, TyKind::Int) => self.tcx.char().clone(),
                    _ => panic!("Cannot index `{expr:?}`"),
                };
                self.ty_info.expr_tys[id] = out;
            }
            Expr::FnCall { function, args } => {
                let fn_ty = self.analyze_expr(*function);
                let TyKind::Function { params, ret } = fn_ty.kind() else {
                    panic!("Expected `function`, found {fn_ty:?}");
                };

                for (arg, param) in std::iter::zip(args, params) {
                    let arg = self.analyze_expr(*arg);
                    self.tcx.subtype(&arg, param);
                }
                self.ty_info.expr_tys[id] = ret.clone();
            }
            Expr::FnDecl { block, params, ident, .. } => {
                let fn_ty = self.bodies.last().unwrap().variables[ident].clone();
                let TyKind::Function { params: param_tys, ret } = fn_ty.kind() else {
                    unreachable!()
                };
                let mut body = Body::new(ret.clone());
                for (param, ty) in std::iter::zip(params, param_tys) {
                    body.variables.insert(param.ident, ty.clone());
                }
                let block = &self.ast.blocks[*block];
                let body_ret = self.analyze_body_with(block, body).0;
                self.tcx.subtype(&body_ret, ret);
            }
            Expr::Let { ident, ty, expr } => {
                let expr_ty = self.analyze_expr(*expr);
                let ty = if let Some(ty) = ty {
                    let ty = self.read_ast_ty(*ty);
                    self.tcx.subtype(&expr_ty, &ty);
                    ty
                } else {
                    expr_ty
                };
                let body = self.bodies.last_mut().unwrap();
                body.variables.insert(*ident, ty);
            }
            Expr::While { condition, block } => {
                self.tcx.subtype(&self.analyze_expr(*condition), self.tcx.bool());
                self.analyze_block(*block);
            }
            Expr::If { arms, els } => {
                let mut expected_ty = None;

                for arm in arms {
                    let ty = self.analyze_expr(arm.condition);
                    self.tcx.subtype(&ty, self.tcx.bool());
                    let block_ty = self.analyze_block(arm.body);
                    if let Some(expected_ty) = expected_ty.as_ref() {
                        self.tcx.eq(expected_ty, &block_ty);
                    } else {
                        expected_ty = Some(block_ty);
                    }
                }
                let expected_ty = expected_ty.unwrap();
                if let &Some(els) = els {
                    let block_ty = self.analyze_block(els);
                    self.tcx.subtype(&expected_ty, &block_ty);
                } else {
                    self.tcx.subtype(&expected_ty, self.tcx.unit());
                }
                self.ty_info.expr_tys[id] = expected_ty;
            }
            Expr::Block(block_id) => {
                let block = &self.ast.blocks[*block_id];
                let ty = if block.is_expr {
                    let mut ty = None;
                    for &id in &block.stmts {
                        ty = Some(self.analyze_expr(id));
                    }
                    ty.unwrap()
                } else {
                    self.analyze_block(*block_id);
                    self.tcx.unit().clone()
                };
                self.ty_info.expr_tys[id] = ty;
            }
            Expr::Return(expr) => {
                let ty = expr
                    .as_ref()
                    .map_or_else(|| self.tcx.unit().clone(), |expr| self.analyze_expr(*expr));
                let expected = &self.bodies.last().unwrap().ret;
                self.tcx.subtype(&ty, expected);
                self.ty_info.expr_tys[id] = self.tcx.never().clone();
            }
            Expr::Break => self.ty_info.expr_tys[id] = self.tcx.never().clone(),
            expr => todo!("{expr:?}"),
        }
        self.ty_info.expr_tys[id].clone()
    }

    fn read_ident(&mut self, ident: Symbol, id: ExprId) -> Ty {
        for body in self.bodies.iter().rev() {
            if let Some(ty) = body.variables.get(&ident) {
                self.ty_info.expr_tys[id] = ty.clone();
                return ty.clone();
            }
        }
        panic!("{:?}", &*ident);
    }

    fn analyze_lit(&mut self, lit: &Lit, id: ExprId) {
        let ty = match lit {
            Lit::Abort => self.tcx.never().clone(),
            Lit::Unit => self.tcx.unit().clone(),
            Lit::Bool(..) => self.tcx.bool().clone(),
            Lit::Int(..) => self.tcx.int().clone(),
            Lit::Char(..) => self.tcx.char().clone(),
            Lit::Str(..) => self.tcx.str().clone(),
            Lit::Array { segments } => 'block: {
                let mut segments = segments.iter();
                let Some(first) = segments.next() else {
                    break 'block TyKind::Array(self.tcx.new_infer()).into();
                };
                let first_ty = self.analyze_expr(first.expr);
                if let Some(repeated) = first.repeated {
                    self.tcx.eq(&self.analyze_expr(repeated), self.tcx.int());
                }
                for seg in segments {
                    let seg_ty = self.analyze_expr(seg.expr);
                    self.tcx.eq(&first_ty, &seg_ty);
                    if let Some(repeated) = seg.repeated {
                        self.tcx.eq(&self.analyze_expr(repeated), self.tcx.int());
                    }
                }
                TyKind::Array(first_ty).into()
            }
        };
        self.ty_info.expr_tys[id] = ty;
    }
}
