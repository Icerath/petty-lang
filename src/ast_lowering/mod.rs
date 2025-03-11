use thin_vec::{ThinVec, thin_vec};

use crate::{
    ast::{self, Ast},
    ast_analysis::TyInfo,
    hir::{self, ExprKind, Hir},
    symbol::Symbol,
    ty::{Ty, TyCtx},
};

pub fn lower_ast(mut ast: Ast, ty_info: TyInfo, tcx: &TyCtx) -> Hir {
    assert_eq!(ast.exprs.len(), ty_info.expr_tys.len());
    let top_level = std::mem::take(&mut ast.top_level);
    let mut lowering = Lowering { ast: &ast, hir: Hir::default(), tcx, ty_info };
    let mut hir_root = vec![];
    for expr in top_level {
        hir_root.push(lowering.lower(expr));
    }
    lowering.hir.root = hir_root;
    lowering.hir
}

struct Lowering<'ast, 'tcx> {
    ast: &'ast Ast,
    hir: Hir,
    tcx: &'tcx TyCtx,
    ty_info: TyInfo,
}

impl Lowering<'_, '_> {
    #[track_caller]
    fn get_ty(&self, expr_id: ast::ExprId) -> &Ty {
        // Note: Does it provide any real benefit to remove the bounds check here? It seems relatively safe so I'm not opposed to it.
        // Safety: We check once at lower_ast that ty_info can hold all of ast's expressions.
        &self.ty_info.expr_tys[expr_id]
    }
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
            &ast::Expr::Block(block) => self.lower_block(block),
            ast::Expr::Lit(lit) => self.lower_literal(lit, expr_id),
            ast::Expr::FnDecl { ident, params, ret, block } => {
                self.lower_fn_decl(*ident, params, *ret, *block, expr_id)
            }
            expr => todo!("{expr:?}"),
        }
    }

    fn lower_fn_decl(
        &mut self,
        ident: Symbol,
        params: &[ast::Param],
        ret: Option<ast::TypeId>,
        block: ast::BlockId,
        expr_id: ast::ExprId,
    ) -> hir::Expr {
        let ret = match ret {
            Some(ret) => self.ty_info.type_ids[ret].clone(),
            None => self.tcx.unit().clone(),
        };
        let params = params
            .iter()
            .map(|param| hir::Param {
                ident: param.ident,
                ty: self.ty_info.type_ids[param.ty].clone(),
            })
            .collect();
        let (_, body) = self.lower_block_inner(block);

        hir::Expr {
            ty: self.get_ty(expr_id).clone(),
            kind: hir::ExprKind::FnDecl { ident, params, ret, body },
        }
    }

    fn lower_literal(&mut self, lit: &ast::Lit, expr_id: ast::ExprId) -> hir::Expr {
        let lit = match lit {
            // &ast::Lit::Unit => hir::Lit::Unit,
            &ast::Lit::Bool(bool) => hir::Lit::Bool(bool),
            &ast::Lit::Int(int) => hir::Lit::Int(int),
            &ast::Lit::Char(char) => hir::Lit::Char(char),
            &ast::Lit::Str(str) => hir::Lit::String(str),
            ast::Lit::Array { segments } => todo!("{segments:?}"),
        };
        hir::Expr { ty: self.get_ty(expr_id).clone(), kind: ExprKind::Literal(lit) }
    }

    fn lower_block(&mut self, block_id: ast::BlockId) -> hir::Expr {
        let (block_ty, exprs) = self.lower_block_inner(block_id);
        hir::Expr { ty: block_ty, kind: ExprKind::Block(exprs) }
    }

    fn lower_block_inner(&mut self, block_id: ast::BlockId) -> (Ty, ThinVec<hir::ExprId>) {
        let block = &self.ast.blocks[block_id];
        let block_ty = if block.is_expr && !block.stmts.is_empty() {
            self.get_ty(*block.stmts.last().unwrap()).clone()
        } else {
            self.tcx.unit().clone()
        };
        let needs_unit = self.block_needs_terminating_unit(block, &block_ty);

        let mut new = ThinVec::with_capacity(block.stmts.len() + usize::from(needs_unit));
        for &expr in &block.stmts {
            new.push(self.lower(expr));
        }
        if needs_unit {
            new.push(self.hir.exprs.push(hir::Expr::unit(self.tcx)));
        }
        (block_ty, new)
    }

    fn block_needs_terminating_unit(&self, block: &ast::Block, block_ty: &Ty) -> bool {
        if block.is_expr {
            return false;
        }
        let last = *block.stmts.last().expect("non-expression blocks should never be empty");
        self.get_ty(last) != block_ty
    }
}
