use crate::{
    ast::{self, Ast},
    ast_analysis::TyInfo,
    hir::{self, Hir},
    ty::TyCtx,
};

pub fn lower_ast(mut ast: Ast, ty_info: TyInfo, tcx: &TyCtx) -> Hir {
    let top_level = std::mem::take(&mut ast.top_level);
    let mut lowering = Lowering { ast, hir: Hir::default(), tcx, ty_info };
    for expr in top_level {
        lowering.lower(expr);
    }
    lowering.hir
}

struct Lowering<'tcx> {
    ast: Ast,
    hir: Hir,
    tcx: &'tcx TyCtx,
    ty_info: TyInfo,
}

impl Lowering<'_> {
    fn lower(&mut self, ast_expr: ast::ExprId) -> hir::ExprId {
        let hir_expr = self.lower_inner(ast_expr);
        self.hir.exprs.push(hir_expr)
    }
    fn lower_inner(&mut self, expr_id: ast::ExprId) -> hir::Expr {
        match &self.ast.exprs[expr_id] {
            &ast::Expr::Binary { lhs, op, rhs } => hir::Expr {
                ty: self.ty_info.expr_tys[expr_id].clone(),
                kind: hir::ExprKind::Binary { lhs: self.lower(lhs), op, rhs: self.lower(rhs) },
            },
            &ast::Expr::Block(block) => self.lower_block(block, expr_id),
            expr => todo!("{expr:?}"),
        }
    }

    fn lower_block(&mut self, block_id: ast::BlockId, expr_id: ast::ExprId) -> hir::Expr {
        todo!()
    }
}
