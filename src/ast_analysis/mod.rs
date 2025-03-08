use crate::{
    ast::{self, Ast, BinaryOp, Expr, ExprId, Lit, Stmt},
    ty::{Ty, TyCtx, TyKind},
};
use ustr::{Ustr as Symbol, UstrMap};

#[derive(Default, Debug)]
pub struct TyInfo {
    expr_tys: Vec<Ty>,
}

#[derive(Default, Debug)]
struct Body {
    ty_names: UstrMap<Ty>,
    variables: UstrMap<Ty>,
}

struct Collector<'ast, 'tcx> {
    ty_info: TyInfo,
    bodies: Vec<Body>,
    ast: &'ast Ast,
    tcx: &'tcx mut TyCtx,
}

fn setup_ty_info(ast: &Ast, tcx: &mut TyCtx) -> TyInfo {
    let mut ty_info = TyInfo::default();

    ty_info.expr_tys.reserve_exact(ast.exprs.borrow().len());
    let shared = tcx.bool().clone();
    ty_info.expr_tys.extend(std::iter::repeat_n(shared, ast.exprs.borrow().len()));
    ty_info
}

pub fn analyze(ast: &Ast, tcx: &mut TyCtx) -> TyInfo {
    let ty_info = setup_ty_info(ast, tcx);
    let body = global_body(tcx);
    let mut collector = Collector { ty_info, ast, tcx, bodies: vec![body] };
    collector.analyze_body(&ast.top_level.borrow());
    let mut ty_info = collector.ty_info;

    for ty in &mut ty_info.expr_tys {
        *ty = tcx.infer(ty);
    }

    ty_info
}

fn global_body(tcx: &mut TyCtx) -> Body {
    let mut body = Body::default();
    let common =
        [("bool", tcx.bool()), ("int", tcx.int()), ("char", tcx.char()), ("str", tcx.str())]
            .map(|(name, ty)| (Symbol::from(name), ty.clone()));
    body.ty_names.extend(common);
    body
}

impl Collector<'_, '_> {
    fn analyze_body(&mut self, stmts: &[Stmt]) -> Body {
        let mut body = Body::default();
        // look for structs/enums first.
        // for stmt in &*ast.top_level.borrow() {}

        for stmt in stmts {
            let Stmt::FnDecl { ident, params, ret, .. } = stmt else { continue };
            let ret =
                ret.as_ref().map_or_else(|| self.tcx.unit().clone(), |ret| self.read_ast_ty(ret));
            let params = params.iter().map(|param| self.read_ast_ty(&param.ty)).collect();
            body.variables.insert(*ident, Ty::from(TyKind::Function { params, ret }));
        }
        self.bodies.push(body);
        self.analyze_block(stmts);
        self.bodies.pop().unwrap()
    }

    fn analyze_block(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            self.analyze_stmt(stmt);
        }
    }
    fn analyze_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr(expr) => _ = self.analyze_expr(*expr),
            Stmt::FnDecl { block, .. } => _ = self.analyze_body(&block.stmts),
            Stmt::Let { ident, ty, expr } => {
                let expr_ty = self.analyze_expr(*expr).clone();
                if let Some(ty) = ty {
                    let ty = self.read_ast_ty(ty);
                    self.tcx.eq(&expr_ty, &ty);
                }
                let body = self.bodies.last_mut().unwrap();
                body.variables.insert(*ident, expr_ty);
            }
            Stmt::While { condition, block } => {
                self.analyze_expr(*condition);
                self.analyze_block(&block.stmts);
            }
            Stmt::If { arms, els } => {
                for arm in arms {
                    let ty = self.analyze_expr(arm.condition);
                    assert_eq!(*ty.kind(), TyKind::Bool);
                    self.analyze_block(&arm.body.stmts);
                }
                if let Some(els) = els {
                    self.analyze_block(&els.stmts);
                }
            }
        }
    }

    fn read_ast_ty(&self, ty: &ast::Ty) -> Ty {
        match ty {
            ast::Ty::Array(of) => TyKind::Array(self.read_ast_ty(of)).into(),
            ast::Ty::Name(name) => {
                for body in self.bodies.iter().rev() {
                    if let Some(ty) = body.ty_names.get(name) {
                        return ty.clone();
                    }
                }
                panic!("{name:?}");
            }
        }
    }

    fn analyze_expr(&mut self, id: ExprId) -> Ty {
        match &*self.ast.get(id) {
            Expr::Lit(lit) => self.analyze_lit(lit, id),
            &Expr::Ident(ident) => _ = self.read_ident(ident, id),
            &Expr::Unary { expr, .. } => _ = self.analyze_expr(expr),
            &Expr::Binary { lhs, rhs, op: BinaryOp::Eq | BinaryOp::Neq } => {
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.tcx.eq(&lhs, &rhs);
                self.ty_info.expr_tys[id] = self.tcx.bool().clone();
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
                    self.tcx.eq(&arg, param);
                }
                self.ty_info.expr_tys[id] = ret.clone();
            }
            expr => todo!("{expr:?}"),
        }
        self.ty_info.expr_tys[id].clone()
    }

    fn read_ident(&mut self, ident: Symbol, id: ExprId) -> Ty {
        let last = self.bodies.last().unwrap();
        let ty = last.variables.get(&ident).unwrap_or_else(|| panic!("{:?}", &*ident)).clone();
        self.ty_info.expr_tys[id] = ty.clone();
        ty
    }

    fn analyze_lit(&mut self, lit: &Lit, id: ExprId) {
        let ty = match lit {
            Lit::Bool(..) => self.tcx.bool().clone(),
            Lit::Int(..) => self.tcx.int().clone(),
            Lit::Char(..) => self.tcx.char().clone(),
            Lit::Str(..) => self.tcx.str().clone(),
            Lit::Array { segments } => 'block: {
                let mut segments = segments.iter();
                let Some(first) = segments.next() else { break 'block self.tcx.new_infer() };
                let first_ty = self.analyze_expr(first.expr).clone();

                for seg in segments {
                    let seg_ty = self.analyze_expr(seg.expr);
                    self.tcx.eq(&first_ty, &seg_ty);
                }
                TyKind::Array(first_ty).into()
            }
        };
        self.ty_info.expr_tys[id] = ty;
    }
}
