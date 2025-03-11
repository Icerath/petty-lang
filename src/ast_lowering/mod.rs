use thin_vec::ThinVec;

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
            &ast::Expr::Let { ident, expr, .. } => self.lower_let_stmt(ident, expr),
            expr => todo!("{expr:?}"),
        }
    }

    fn lower_let_stmt(&mut self, ident: Symbol, expr: ast::ExprId) -> hir::Expr {
        hir::Expr {
            ty: self.tcx.unit().clone(),
            kind: hir::ExprKind::Let { ident, expr: self.lower(expr) },
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
            ast::Lit::Array { segments } => {
                let hir_segments = segments.iter().map(|segment| {
                    let expr = self.lower(segment.expr);
                    let repeated = segment.repeated.map(|expr| self.lower(expr));
                    hir::ArraySeg { expr, repeated }
                });
                hir::Lit::Array { segments: hir_segments.collect() }
            }
        };
        hir::Expr { ty: self.get_ty(expr_id).clone(), kind: ExprKind::Literal(lit) }
    }

    fn lower_block(&mut self, block_id: ast::BlockId) -> hir::Expr {
        let (block_ty, exprs) = self.lower_block_inner(block_id);
        hir::Expr { ty: block_ty, kind: ExprKind::Block(exprs) }
    }

    fn lower_block_inner(&mut self, block_id: ast::BlockId) -> (Ty, ThinVec<hir::ExprId>) {
        let block = &self.ast.blocks[block_id];
        let block_ty = if block.is_expr {
            self.get_ty(*block.stmts.last().unwrap()).clone()
        } else {
            self.tcx.unit().clone()
        };
        let needs_unit = self.block_needs_terminating_unit(block);

        let mut new = ThinVec::with_capacity(block.stmts.len() + usize::from(needs_unit));
        for &expr in &block.stmts {
            new.push(self.lower(expr));
        }
        if needs_unit {
            new.push(self.hir.exprs.push(hir::Expr::unit(self.tcx)));
        }
        (block_ty, new)
    }

    fn block_needs_terminating_unit(&self, block: &ast::Block) -> bool {
        // if a block isn't terminated by a semicolon then it already returns the correct type.
        if block.is_expr {
            return false;
        }
        match block.stmts.last() {
            // we don't need a unit if the last expr is already a unit
            Some(last) => self.get_ty(*last) != self.tcx.unit(),
            // empty blocks don't need to need a terminating unit
            None => false,
        }
    }
}
