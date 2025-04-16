use std::path::Path;

use thin_vec::{ThinVec, thin_vec};

use crate::{
    ast::{self, Ast, BinOpKind, BinaryOp},
    ast_analysis::TyInfo,
    errors,
    hir::{self, ExprKind, Hir, IfStmt},
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

    #[allow(clippy::too_many_lines)]
    fn lower_inner(&mut self, expr_id: ast::ExprId) -> hir::Expr<'tcx> {
        let expr_ty = self.get_ty(expr_id);
        match self.ast.exprs[expr_id].kind {
            ast::ExprKind::Impl(..) | ast::ExprKind::Trait(..) => hir::Expr::UNIT,
            ast::ExprKind::Unreachable => ExprKind::Unreachable.with(&TyKind::Never),
            ast::ExprKind::Binary {
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
                    let ty = self.get_ty(rhs);
                    let lhs = self.lower(lhs);
                    let rhs = self.lower(rhs);
                    self.hir.exprs.push(ExprKind::Binary { lhs, op, rhs }.with(ty))
                };

                (hir::ExprKind::Assignment { lhs: self.lower(lhs), expr }).with(expr_ty)
            }
            ast::ExprKind::Binary { lhs, op: BinaryOp { kind: BinOpKind::Assign, .. }, rhs } => {
                (hir::ExprKind::Assignment { lhs: self.lower(lhs), expr: self.lower(rhs) })
                    .with(expr_ty)
            }
            ast::ExprKind::Binary { lhs, op, rhs } => {
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
                (hir::ExprKind::Binary { lhs: self.lower(lhs), op, rhs: self.lower(rhs) })
                    .with(expr_ty)
            }
            ast::ExprKind::Block(block) => self.lower_block(block),
            ast::ExprKind::Lit(ref lit) => self.lower_literal(lit, expr_id),
            ast::ExprKind::FnDecl(ref decl) => self.lower_fn_decl(decl),
            ast::ExprKind::Let { ident, expr, .. } => self.lower_let_stmt(ident, expr),
            ast::ExprKind::If { ref arms, els } => self.lower_if_stmt(arms, els, expr_id),
            ast::ExprKind::While { condition, block } => self.lower_while_loop(condition, block),
            ast::ExprKind::For { ident, iter, body } => self.lower_for_loop(ident, iter, body),
            ast::ExprKind::Ident(symbol) => ExprKind::Ident(symbol).with(expr_ty),
            ast::ExprKind::FnCall { function, ref args } => {
                self.lower_fn_call(function, args, expr_id)
            }
            ast::ExprKind::Index { expr, index } => {
                (ExprKind::Index { expr: self.lower(expr), index: self.lower(index) }).with(expr_ty)
            }
            ast::ExprKind::Return(expr) => {
                let inner = match expr {
                    Some(expr) => self.lower(expr),
                    None => self.hir.exprs.push(hir::Expr::UNIT),
                };
                ExprKind::Return(inner).with(&TyKind::Never)
            }
            ast::ExprKind::Unary { op, expr } => {
                (ExprKind::Unary { op, expr: self.lower(expr) }).with(expr_ty)
            }
            ast::ExprKind::Break => hir::Expr::BREAK,
            ast::ExprKind::Struct { ident, ref fields, span } => {
                let struct_ty = self.ty_info.struct_types[&span];

                let fields: ThinVec<_> = (fields.iter())
                    .map(|field| hir::Param {
                        ident: field.ident,
                        ty: self.ty_info.type_ids[field.ty],
                    })
                    .collect();

                let body =
                    ThinVec::from([self.hir.exprs.push(hir::ExprKind::StructInit.with(struct_ty))]);
                (hir::FnDecl { ident, params: fields.clone().into(), ret: struct_ty, body }).into()
            }
            ast::ExprKind::Assert(expr) => {
                let display =
                    ExprKind::PrintStr(self.assert_failed_error(expr)).with(&TyKind::Unit);
                let display = self.hir.exprs.push(display);

                let abort = (self.hir.exprs).push(ExprKind::Abort.with(&TyKind::Never));

                let body = ThinVec::from([display, abort]);
                let condition = self.lower_then_not(expr);
                let arms = thin_vec![IfStmt { condition, body }];
                (hir::ExprKind::If { arms, els: ThinVec::new() }).with(&TyKind::Unit)
            }
            ast::ExprKind::MethodCall { .. } => todo!(),
            ast::ExprKind::FieldAccess { expr, field } => {
                let TyKind::Struct { symbols, .. } = self.get_ty(expr) else { unreachable!() };
                let expr = self.lower(expr);

                let field = symbols.iter().position(|&s| s == field).unwrap();
                (hir::ExprKind::Field { expr, field }).with(expr_ty)
            }
        }
    }

    fn lower_then_not(&mut self, ast_expr: ast::ExprId) -> hir::ExprId {
        let inner = self.lower(ast_expr);
        let hir_expr = (ExprKind::Unary { op: hir::UnaryOp::Not, expr: inner }).with(&TyKind::Bool);
        self.hir.exprs.push(hir_expr)
    }

    fn assert_failed_error(&self, expr: ast::ExprId) -> Symbol {
        let span = self.ast.exprs[expr].span;
        let report = errors::error("assertion failed", self.path, self.src, [(span, "")]);
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
        (hir::ExprKind::FnCall { function, args }).with(self.get_ty(expr_id))
    }

    fn lower_while_loop(&mut self, condition: ast::ExprId, body: ast::BlockId) -> hir::Expr<'tcx> {
        let condition = self.lower_then_not(condition);
        let break_ = self.hir.exprs.push(hir::Expr::BREAK);

        let if_stmt = (ExprKind::If {
            arms: ThinVec::from([hir::IfStmt { condition, body: ThinVec::from([break_]) }]),
            els: ThinVec::new(),
        })
        .with(&TyKind::Unit);
        let mut block = self.lower_block_inner(body).1;
        block.insert(0, self.hir.exprs.push(if_stmt));
        ExprKind::Loop(block).with(&TyKind::Unit)
    }

    fn lower_for_loop(
        &mut self,
        ident: Symbol,
        iter: ast::ExprId,
        body: ast::BlockId,
    ) -> hir::Expr<'tcx> {
        _ = ident;
        _ = iter;
        _ = body;
        todo!()
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
        (ExprKind::If { arms, els }).with(self.get_ty(id))
    }

    fn lower_let_stmt(&mut self, ident: Symbol, expr: ast::ExprId) -> hir::Expr<'tcx> {
        (hir::ExprKind::Let { ident, expr: self.lower(expr) }).with(&TyKind::Unit)
    }

    fn lower_fn_decl(&mut self, decl: &ast::FnDecl) -> hir::Expr<'tcx> {
        let ast::FnDecl { ident, ref params, ret, block, .. } = *decl;

        let block = block.unwrap();

        let ret = match ret {
            Some(ret) => self.ty_info.type_ids[ret],
            None => &TyKind::Unit,
        };

        let params = params
            .iter()
            .map(|param| hir::Param { ident: param.ident, ty: self.ty_info.type_ids[param.ty] })
            .collect();
        let (_, body) = self.lower_block_inner(block);
        (hir::FnDecl { ident, params, ret, body }).into()
    }

    fn lower_literal(&mut self, lit: &ast::Lit, expr_id: ast::ExprId) -> hir::Expr<'tcx> {
        let lit = match *lit {
            ast::Lit::Unit => hir::Lit::Unit,
            ast::Lit::Bool(bool) => hir::Lit::Bool(bool),
            ast::Lit::Int(int) => hir::Lit::Int(int),
            ast::Lit::Char(char) => hir::Lit::Char(char),
            ast::Lit::Str(str) => hir::Lit::String(str),
            ast::Lit::Array { ref segments } => {
                let hir_segments = segments.iter().map(|segment| {
                    let expr = self.lower(segment.expr);
                    let repeated = segment.repeated.map(|expr| self.lower(expr));
                    hir::ArraySeg { expr, repeated }
                });
                hir::Lit::Array { segments: hir_segments.collect() }
            }
            ast::Lit::FStr(ref segments) => {
                let segments = segments.iter().map(|&segment| self.lower(segment)).collect();
                hir::Lit::FStr { segments }
            }
        };
        ExprKind::Literal(lit).with(self.get_ty(expr_id))
    }

    fn lower_block(&mut self, block_id: ast::BlockId) -> hir::Expr<'tcx> {
        let (block_ty, exprs) = self.lower_block_inner(block_id);
        ExprKind::Block(exprs).with(block_ty)
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
