use std::path::Path;
use thin_vec::{ThinVec, thin_vec};

use crate::{
    ast::{self, Ast, BinOpKind, BinaryOp},
    ast_analysis::TyInfo,
    errors,
    hir::{self, Expr, ExprKind, Hir, IfStmt, Lit},
    symbol::Symbol,
    ty::{Ty, TyKind},
};

pub fn lower<'tcx>(
    src: &str,
    path: Option<&Path>,
    mut ast: Ast,
    ty_info: TyInfo<'tcx>,
) -> Hir<'tcx> {
    assert_eq!(ast.exprs.len(), ty_info.expr_tys.len());
    let top_level = std::mem::take(&mut ast.top_level);
    let mut lowering = Lowering { src, path, ast: &ast, hir: Hir::default(), ty_info };
    let mut hir_root = vec![];
    for expr in top_level {
        hir_root.push(lowering.lower(expr));
    }
    lowering.hir.root = hir_root;
    lowering.hir
}

struct Lowering<'src, 'ast, 'tcx> {
    ast: &'ast Ast,
    hir: Hir<'tcx>,
    ty_info: TyInfo<'tcx>,
    src: &'src str,
    path: Option<&'src Path>,
}

impl<'tcx> Lowering<'_, '_, 'tcx> {
    #[track_caller]
    fn get_ty(&self, expr_id: ast::ExprId) -> Ty<'tcx> {
        // Note: Does it provide any real benefit to remove the bounds check here? It seems relatively safe so I'm not opposed to it.
        // Safety: We check once at lower_ast that ty_info can hold all of ast's expressions.
        self.ty_info.expr_tys[expr_id]
    }

    fn lower(&mut self, ast_expr: ast::ExprId) -> hir::ExprId {
        let hir_expr = self.lower_inner(ast_expr);
        self.hir.exprs.push(hir_expr)
    }

    fn lower_lvalue(&mut self, expr_id: ast::ExprId) -> hir::LValue {
        match &self.ast.exprs[expr_id].kind {
            &ast::ExprKind::Ident(name) => hir::LValue::Name(name),
            ast::ExprKind::Index { expr, index } => {
                let indexee = Box::new(self.lower_lvalue(*expr));
                hir::LValue::Index { indexee, index: self.lower(*index) }
            }
            _ => panic!("Invalid lhs of assignment"),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn lower_inner(&mut self, expr_id: ast::ExprId) -> hir::Expr<'tcx> {
        match &self.ast.exprs[expr_id].kind {
            &ast::ExprKind::Binary {
                lhs,
                op:
                    op @ BinaryOp {
                        kind:
                            BinOpKind::AddAssign
                            | BinOpKind::SubAssign
                            | BinOpKind::MulAssign
                            | BinOpKind::DivAssign
                            | BinOpKind::ModAssign,
                        ..
                    },
                rhs,
            } => {
                let expr = {
                    let op = match op.kind {
                        BinOpKind::AddAssign => hir::BinaryOp::Add,
                        BinOpKind::SubAssign => hir::BinaryOp::Sub,
                        BinOpKind::MulAssign => hir::BinaryOp::Mul,
                        BinOpKind::DivAssign => hir::BinaryOp::Div,
                        BinOpKind::ModAssign => hir::BinaryOp::Mod,
                        _ => unreachable!(),
                    };
                    let kind = ExprKind::Binary { lhs: self.lower(lhs), op, rhs: self.lower(rhs) };
                    self.hir.exprs.push(Expr { kind, ty: self.ty_info.expr_tys[rhs] })
                };

                let kind = hir::ExprKind::Assignment { lhs: self.lower_lvalue(lhs), expr };
                hir::Expr { ty: self.ty_info.expr_tys[expr_id], kind }
            }
            &ast::ExprKind::Binary { lhs, op: BinaryOp { kind: BinOpKind::Assign, .. }, rhs } => {
                let kind = hir::ExprKind::Assignment {
                    lhs: self.lower_lvalue(lhs),
                    expr: self.lower(rhs),
                };
                hir::Expr { ty: self.ty_info.expr_tys[expr_id], kind }
            }
            &ast::ExprKind::Binary { lhs, op, rhs } => {
                let op = match op.kind {
                    BinOpKind::Add => hir::BinaryOp::Add,
                    BinOpKind::Sub => hir::BinaryOp::Sub,
                    BinOpKind::Mul => hir::BinaryOp::Mul,
                    BinOpKind::Div => hir::BinaryOp::Div,
                    BinOpKind::Mod => hir::BinaryOp::Mod,
                    BinOpKind::Less => hir::BinaryOp::Less,
                    BinOpKind::Greater => hir::BinaryOp::Greater,
                    BinOpKind::LessEq => hir::BinaryOp::LessEq,
                    BinOpKind::GreaterEq => hir::BinaryOp::GreaterEq,
                    BinOpKind::Eq => hir::BinaryOp::Eq,
                    BinOpKind::Neq => hir::BinaryOp::Neq,
                    BinOpKind::Range => hir::BinaryOp::Range,
                    BinOpKind::RangeInclusive => hir::BinaryOp::RangeInclusive,
                    _ => unreachable!("{op:?}"),
                };
                hir::Expr {
                    ty: self.ty_info.expr_tys[expr_id],
                    kind: hir::ExprKind::Binary { lhs: self.lower(lhs), op, rhs: self.lower(rhs) },
                }
            }
            &ast::ExprKind::Block(block) => self.lower_block(block),
            ast::ExprKind::Lit(lit) => self.lower_literal(lit, expr_id),
            ast::ExprKind::FnDecl(ast::FnDecl { ident, params, ret, block, .. }) => {
                self.lower_fn_decl(*ident, params, *ret, *block, expr_id)
            }
            &ast::ExprKind::Let { ident, expr, .. } => self.lower_let_stmt(ident, expr),
            ast::ExprKind::If { arms, els } => self.lower_if_stmt(arms, *els, expr_id),
            &ast::ExprKind::While { condition, block } => self.lower_while_loop(condition, block),
            &ast::ExprKind::Ident(symbol) => {
                hir::Expr { ty: self.get_ty(expr_id), kind: ExprKind::Ident(symbol) }
            }
            ast::ExprKind::FnCall { function, args } => {
                self.lower_fn_call(*function, args, expr_id)
            }
            &ast::ExprKind::Index { expr, index } => hir::Expr {
                ty: self.get_ty(expr_id),
                kind: ExprKind::Index { expr: self.lower(expr), index: self.lower(index) },
            },
            &ast::ExprKind::Return(expr) => {
                let inner = match expr {
                    Some(expr) => self.lower(expr),
                    None => self.hir.exprs.push(hir::Expr::UNIT),
                };
                hir::Expr { ty: &TyKind::Never, kind: ExprKind::Return(inner) }
            }
            &ast::ExprKind::Unary { op, expr } => hir::Expr {
                ty: self.get_ty(expr_id),
                kind: ExprKind::Unary { op, expr: self.lower(expr) },
            },
            ast::ExprKind::Break => hir::Expr { ty: &TyKind::Never, kind: ExprKind::Break },
            &ast::ExprKind::Struct { ident, ref fields } => {
                let fields = (fields.iter())
                    .map(|field| hir::Param {
                        ident: field.ident,
                        ty: self.ty_info.type_ids[field.ty],
                    })
                    .collect();
                hir::Expr { ty: &TyKind::Unit, kind: ExprKind::Struct { ident, fields } }
            }
            &ast::ExprKind::Assert(expr) => {
                let display = ExprKind::PrintStr(self.assert_failed_error(expr));
                let display = self.hir.exprs.push(Expr { ty: &TyKind::Unit, kind: display });

                let abort = (self.hir.exprs)
                    .push(Expr { ty: &TyKind::Never, kind: ExprKind::Literal(Lit::Abort) });

                let body = ThinVec::from([display, abort]);
                let condition_kind =
                    ExprKind::Unary { op: ast::UnaryOp::Not, expr: self.lower(expr) };
                let condition =
                    self.hir.exprs.push(Expr { ty: &TyKind::Bool, kind: condition_kind });
                let arms = thin_vec![IfStmt { condition, body }];
                Expr { ty: &TyKind::Unit, kind: hir::ExprKind::If { arms, els: ThinVec::new() } }
            }
            expr => todo!("{expr:?}"),
        }
    }

    fn assert_failed_error(&self, expr: ast::ExprId) -> Symbol {
        let span = self.ast.exprs[expr].span;
        let report = errors::error("assertion failed", self.path, self.src, &[(span, "".into())]);
        Symbol::from(format!("{report:?}").as_str())
    }

    fn lower_fn_call(
        &mut self,
        function: ast::ExprId,
        args: &[ast::ExprId],
        expr_id: ast::ExprId,
    ) -> hir::Expr<'tcx> {
        let function = self.lower(function);
        let args = args.iter().map(|arg| self.lower(*arg)).collect();
        hir::Expr { ty: self.get_ty(expr_id), kind: hir::ExprKind::FnCall { function, args } }
    }

    fn lower_while_loop(&mut self, condition: ast::ExprId, body: ast::BlockId) -> hir::Expr<'tcx> {
        let condition = hir::Expr {
            ty: &TyKind::Bool,
            kind: hir::ExprKind::Unary { op: hir::UnaryOp::Not, expr: self.lower(condition) },
        };
        let condition = self.hir.exprs.push(condition);
        let break_ = hir::Expr { ty: &TyKind::Unit, kind: ExprKind::Break };
        let break_ = self.hir.exprs.push(break_);
        let if_stmt = hir::Expr {
            ty: &TyKind::Unit,
            kind: ExprKind::If {
                arms: ThinVec::from([hir::IfStmt { condition, body: ThinVec::from([break_]) }]),
                els: ThinVec::new(),
            },
        };
        let mut block = self.lower_block_inner(body).1;
        block.insert(0, self.hir.exprs.push(if_stmt));
        hir::Expr { ty: &TyKind::Unit, kind: ExprKind::Loop(block) }
    }

    fn lower_if_stmt(
        &mut self,
        arms: &[ast::IfStmt],
        els: Option<ast::BlockId>,
        id: ast::ExprId,
    ) -> hir::Expr<'tcx> {
        let arms = arms
            .iter()
            .map(|arm| hir::IfStmt {
                condition: self.lower(arm.condition),
                body: self.lower_block_inner(arm.body).1,
            })
            .collect();

        let els = els.map_or_else(ThinVec::new, |els| self.lower_block_inner(els).1);
        hir::Expr { ty: self.get_ty(id), kind: ExprKind::If { arms, els } }
    }

    fn lower_let_stmt(&mut self, ident: Symbol, expr: ast::ExprId) -> hir::Expr<'tcx> {
        hir::Expr { ty: &TyKind::Unit, kind: hir::ExprKind::Let { ident, expr: self.lower(expr) } }
    }

    fn lower_fn_decl(
        &mut self,
        ident: Symbol,
        params: &[ast::Param],
        ret: Option<ast::TypeId>,
        block: ast::BlockId,
        expr_id: ast::ExprId,
    ) -> hir::Expr<'tcx> {
        let ret = match ret {
            Some(ret) => self.ty_info.type_ids[ret],
            None => &TyKind::Unit,
        };
        let params = params
            .iter()
            .map(|param| hir::Param { ident: param.ident, ty: self.ty_info.type_ids[param.ty] })
            .collect();
        let (_, body) = self.lower_block_inner(block);

        hir::Expr {
            ty: self.get_ty(expr_id),
            kind: hir::ExprKind::FnDecl(Box::new(hir::FnDecl { ident, params, ret, body })),
        }
    }

    fn lower_literal(&mut self, lit: &ast::Lit, expr_id: ast::ExprId) -> hir::Expr<'tcx> {
        let lit = match lit {
            &ast::Lit::Abort => hir::Lit::Abort,
            &ast::Lit::Unit => hir::Lit::Unit,
            &ast::Lit::Bool(bool) => hir::Lit::Bool(bool),
            &ast::Lit::Int(int) => hir::Lit::Int(int),
            &ast::Lit::Char(char) => hir::Lit::Char(char),
            &ast::Lit::Str(str) => hir::Lit::String(str),
            ast::Lit::Array { segments } => {
                let hir_segments = segments.iter().map(|segment| {
                    let expr = self.lower(segment.expr);
                    let repeated = segment.repeated.map(|expr| self.lower(expr));
                    hir::ArraySeg { expr, repeated }
                });
                hir::Lit::Array { segments: hir_segments.collect() }
            }
        };
        hir::Expr { ty: self.get_ty(expr_id), kind: ExprKind::Literal(lit) }
    }

    fn lower_block(&mut self, block_id: ast::BlockId) -> hir::Expr<'tcx> {
        let (block_ty, exprs) = self.lower_block_inner(block_id);
        hir::Expr { ty: block_ty, kind: ExprKind::Block(exprs) }
    }

    fn lower_block_inner(&mut self, block_id: ast::BlockId) -> (Ty<'tcx>, ThinVec<hir::ExprId>) {
        let block = &self.ast.blocks[block_id];
        let block_ty =
            if block.is_expr { self.get_ty(*block.stmts.last().unwrap()) } else { &TyKind::Unit };
        let needs_unit = self.block_needs_terminating_unit(block);

        let mut new = ThinVec::with_capacity(block.stmts.len() + usize::from(needs_unit));
        for &expr in &block.stmts {
            new.push(self.lower(expr));
        }
        if needs_unit {
            new.push(self.hir.exprs.push(hir::Expr::UNIT));
        }
        (block_ty, new)
    }

    fn block_needs_terminating_unit(&self, block: &ast::Block) -> bool {
        // if a block isn't terminated by a semicolon then it already returns the correct type.
        if block.is_expr {
            return false;
        }
        block.stmts.last().is_some_and(|last| self.get_ty(*last) != &TyKind::Unit)
    }
}
