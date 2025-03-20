use std::path::PathBuf;

use crate::{
    HashMap,
    ast::{self, Ast, BinOpKind, BinaryOp, Block, BlockId, ExprId, ExprKind, Lit, TypeId, UnaryOp},
    span::Span,
    symbol::Symbol,
    ty::{Ty, TyCtx, TyKind},
};
use miette::{LabeledSpan, NamedSource, Result};

use index_vec::IndexVec;

#[derive(Default, Debug)]
pub struct TyInfo<'tcx> {
    pub expr_tys: IndexVec<ExprId, Ty<'tcx>>,
    pub type_ids: IndexVec<TypeId, Ty<'tcx>>,
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
    file: Option<PathBuf>,
}

fn setup_ty_info<'tcx>(ast: &Ast, tcx: &'tcx TyCtx<'tcx>) -> TyInfo<'tcx> {
    let shared = tcx.unit();
    TyInfo {
        expr_tys: std::iter::repeat_n(shared, ast.exprs.len()).collect(),
        type_ids: std::iter::repeat_n(shared, ast.types.len()).collect(),
    }
}

pub fn analyze<'tcx>(
    file: Option<PathBuf>,
    src: &str,
    ast: &Ast,
    tcx: &'tcx TyCtx<'tcx>,
) -> TyInfo<'tcx> {
    let ty_info = setup_ty_info(ast, tcx);
    let body = global_body(tcx);
    let mut collector = Collector { file, src, ty_info, ast, tcx, bodies: vec![body] };
    let top_level_exprs = ast.top_level.iter().copied().collect();
    let top_level = ast::Block { stmts: top_level_exprs, is_expr: false };
    collector.analyze_body_with(&top_level, Body::new(tcx.never()));

    let mut ty_info = collector.ty_info;
    ty_info.expr_tys.iter_mut().for_each(|ty| *ty = tcx.infer_deep(*ty));
    ty_info.type_ids.iter_mut().for_each(|ty| *ty = tcx.infer_deep(*ty));

    ty_info
}

fn global_body<'tcx>(tcx: &'tcx TyCtx<'tcx>) -> Body<'tcx> {
    let mut body = Body::new(tcx.never());
    let common =
        [("bool", tcx.bool()), ("int", tcx.int()), ("char", tcx.char()), ("str", tcx.str())]
            .map(|(name, ty)| (Symbol::from(name), ty));
    body.ty_names.extend(common);
    body
}

impl<'tcx> Collector<'_, '_, 'tcx> {
    fn analyze_body_with(
        &mut self,
        block: &ast::Block,
        mut body: Body<'tcx>,
    ) -> (Ty<'tcx>, Body<'tcx>) {
        // look for structs/enums first.
        // for stmt in &*ast.top_level.borrow() {}

        for &id in &block.stmts {
            let ExprKind::FnDecl { ident, params, ret, .. } = &self.ast.exprs[id].kind else {
                continue;
            };
            let ret = match ret {
                Some(ret) => self.read_ast_ty(*ret),
                None => self.tcx.unit(),
            };
            let params = params.iter().map(|param| self.read_ast_ty(param.ty)).collect();
            body.variables.insert(*ident, self.tcx.intern(TyKind::Function { params, ret }));
        }
        self.bodies.push(body);
        let out = self.analyze_block_inner(block);
        (out, self.bodies.pop().unwrap())
    }

    fn analyze_block(&mut self, id: BlockId) -> Ty<'tcx> {
        let block = &self.ast.blocks[id];
        self.analyze_block_inner(block)
    }

    fn analyze_block_inner(&mut self, block: &Block) -> Ty<'tcx> {
        let mut ty = None;
        for &id in &block.stmts {
            ty = Some(self.analyze_expr(id));
        }
        if block.is_expr {
            ty.unwrap_or_else(|| self.tcx.unit())
        } else if ty.is_some_and(Ty::is_never) {
            self.tcx.never()
        } else {
            self.tcx.unit()
        }
    }

    fn read_ast_ty(&mut self, id: ast::TypeId) -> Ty<'tcx> {
        let ty = match self.ast.types[id] {
            ast::Ty::Never => self.tcx.never(),
            ast::Ty::Unit => self.tcx.unit(),
            ast::Ty::Array(of) => self.tcx.intern(TyKind::Array(self.read_ast_ty(of))),
            ast::Ty::Name(name) => self.read_named_ty(name),
        };
        self.ty_info.type_ids[id] = ty;
        ty
    }

    fn read_named_ty(&self, name: Symbol) -> Ty<'tcx> {
        *self.bodies.iter().rev().find_map(|body| body.ty_names.get(&name)).unwrap()
    }

    fn subtype(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, span: Span) -> Result<()> {
        self.tcx.try_subtype(lhs, rhs).map_err(|[lhs, rhs]| self.subtype_err(lhs, rhs, span))
    }

    #[cold]
    #[inline(never)]
    fn subtype_err(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, span: Span) -> miette::Error {
        let label = LabeledSpan::at(span, "here");
        miette::miette!(
            labels = vec![label],
            code = "type error",
            "expected `{rhs}`, found `{lhs}`"
        )
        .with_source_code(self.src())
    }

    fn src(&self) -> NamedSource<String> {
        match self.file.as_ref().and_then(|file| file.to_str()) {
            Some(file) => NamedSource::new(file, self.src.to_string()),
            None => NamedSource::new("", self.src.to_string()),
        }
    }

    #[must_use]
    #[expect(clippy::too_many_lines)]
    fn analyze_expr(&mut self, id: ExprId) -> Ty<'tcx> {
        let ty = match &self.ast.exprs[id].kind {
            ExprKind::Lit(lit) => self.analyze_lit(lit),
            &ExprKind::Ident(ident) => self.read_ident(ident),
            &ExprKind::Unary { expr, op } => {
                let operand = self.analyze_expr(expr);
                let ty = match op {
                    UnaryOp::Neg => self.tcx.int(),
                    UnaryOp::Not => self.tcx.bool(),
                };
                self.tcx.subtype(operand, ty);
                ty
            }
            &ExprKind::Binary {
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
                let span = self.ast.spans([lhs, rhs]);
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.subtype(rhs, lhs, span).expect("");
                self.tcx.unit()
            }
            &ExprKind::Binary {
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
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.tcx.eq(lhs, rhs);
                self.tcx.bool()
            }
            &ExprKind::Binary {
                lhs,
                rhs,
                op: op @ BinaryOp { kind: BinOpKind::Range | BinOpKind::RangeInclusive, .. },
            } => {
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.tcx.eq(lhs, rhs);

                self.tcx.subtype(lhs, self.tcx.int());
                self.tcx.subtype(rhs, self.tcx.int());

                match op.kind {
                    BinOpKind::Range => self.tcx.intern(TyKind::Range),
                    BinOpKind::RangeInclusive => self.tcx.intern(TyKind::RangeInclusive),
                    _ => unreachable!(),
                }
            }
            &ExprKind::Binary { lhs, rhs, .. } => {
                let lhs = self.analyze_expr(lhs);
                let rhs = self.analyze_expr(rhs);
                self.tcx.eq(lhs, rhs);
                lhs
            }
            &ExprKind::Index { expr, index } => {
                let expr = self.analyze_expr(expr);
                let index = self.analyze_expr(index);
                let expr = self.tcx.infer_shallow(expr);
                let out = match (&*expr, &*index) {
                    (TyKind::Str, TyKind::Range | TyKind::RangeInclusive) => self.tcx.str(),
                    (TyKind::Array(_), TyKind::Range | TyKind::RangeInclusive) => expr,

                    (TyKind::Array(of), TyKind::Int) => *of,
                    (TyKind::Str, TyKind::Int) => self.tcx.char(),
                    _ => panic!("Cannot index `{expr:?}`"),
                };
                out
            }
            ExprKind::FnCall { function, args } => {
                let fn_ty = self.analyze_expr(*function);
                let TyKind::Function { params, ret } = &*fn_ty else {
                    panic!("expected `function`, found {fn_ty:?}");
                };

                for (&arg, &param) in std::iter::zip(args, params) {
                    let arg = self.analyze_expr(arg);
                    self.tcx.subtype(arg, param);
                }
                *ret
            }
            ExprKind::FnDecl { block, params, ident, .. } => {
                let fn_ty = self.bodies.last().unwrap().variables[ident];
                let TyKind::Function { params: param_tys, ret } = &*fn_ty else { unreachable!() };
                let mut body = Body::new(*ret);
                for (param, ty) in std::iter::zip(params, param_tys) {
                    body.variables.insert(param.ident, *ty);
                }
                let block = &self.ast.blocks[*block];
                let body_ret = self.analyze_body_with(block, body).0;
                self.tcx.subtype(body_ret, *ret);
                self.tcx.unit()
            }
            ExprKind::Let { ident, ty, expr } => {
                let expr_ty = self.analyze_expr(*expr);
                let ty = if let Some(ty) = ty {
                    let ty = self.read_ast_ty(*ty);
                    self.tcx.subtype(expr_ty, ty);
                    ty
                } else {
                    expr_ty
                };
                let body = self.bodies.last_mut().unwrap();
                body.variables.insert(*ident, ty);
                self.tcx.unit()
            }
            ExprKind::While { condition, block } => {
                self.tcx.subtype(self.analyze_expr(*condition), self.tcx.bool());
                self.analyze_block(*block);
                self.tcx.unit()
            }
            ExprKind::If { arms, els } => {
                let mut expected_ty = None;

                for arm in arms {
                    let ty = self.analyze_expr(arm.condition);
                    self.tcx.subtype(ty, self.tcx.bool());
                    let block_ty = self.analyze_block(arm.body);
                    if let Some(expected_ty) = expected_ty {
                        self.tcx.eq(expected_ty, block_ty);
                    } else {
                        expected_ty = Some(block_ty);
                    }
                }
                let expected_ty = expected_ty.unwrap();
                if let &Some(els) = els {
                    let block_ty = self.analyze_block(els);
                    self.tcx.subtype(expected_ty, block_ty);
                } else {
                    self.tcx.subtype(expected_ty, self.tcx.unit());
                }
                self.ty_info.expr_tys[id] = expected_ty;
                self.tcx.unit()
            }
            ExprKind::Block(block_id) => {
                let block = &self.ast.blocks[*block_id];
                if block.is_expr {
                    let mut ty = None;
                    for &id in &block.stmts {
                        ty = Some(self.analyze_expr(id));
                    }
                    ty.unwrap()
                } else {
                    self.analyze_block(*block_id);
                    self.tcx.unit()
                }
            }
            ExprKind::Return(expr) => {
                let ty = expr.map_or_else(|| self.tcx.unit(), |expr| self.analyze_expr(expr));
                let expected = self.bodies.last().unwrap().ret;
                self.tcx.subtype(ty, expected);
                self.tcx.never()
            }
            ExprKind::Break => self.tcx.never(),
            expr => todo!("{expr:?}"),
        };
        self.ty_info.expr_tys[id] = ty;
        ty
    }

    fn read_ident(&self, ident: Symbol) -> Ty<'tcx> {
        *self.bodies.iter().rev().find_map(|body| body.variables.get(&ident)).unwrap()
    }

    fn analyze_lit(&mut self, lit: &Lit) -> Ty<'tcx> {
        match lit {
            Lit::Abort => self.tcx.never(),
            Lit::Unit => self.tcx.unit(),
            Lit::Bool(..) => self.tcx.bool(),
            Lit::Int(..) => self.tcx.int(),
            Lit::Char(..) => self.tcx.char(),
            Lit::Str(..) => self.tcx.str(),
            Lit::Array { segments } => 'block: {
                let mut segments = segments.iter();
                let Some(first) = segments.next() else {
                    break 'block self.tcx.intern(TyKind::Array(self.tcx.new_infer()));
                };
                let first_ty = self.analyze_expr(first.expr);
                if let Some(repeated) = first.repeated {
                    self.tcx.eq(self.analyze_expr(repeated), self.tcx.int());
                }
                for seg in segments {
                    let seg_ty = self.analyze_expr(seg.expr);
                    self.tcx.eq(first_ty, seg_ty);
                    if let Some(repeated) = seg.repeated {
                        self.tcx.eq(self.analyze_expr(repeated), self.tcx.int());
                    }
                }
                self.tcx.intern(TyKind::Array(first_ty))
            }
        }
    }
}
