use std::collections::BTreeMap;

use thin_vec::{ThinVec, thin_vec};

use crate::{
    ast::{self, Ast, BinOpKind, BinaryOp, Stmt},
    ast_analysis::TyInfo,
    errors,
    hir::{self, BodyId, ExprKind, Hir, IfStmt, OpAssign, Pat, PatField},
    symbol::Symbol,
    ty::{Function, Ty, TyKey, TyKind},
};

#[expect(clippy::needless_pass_by_value)]
pub fn lower(ast: Ast, ty_info: TyInfo<'_>) -> Hir<'_> {
    assert_eq!(ast.exprs.len(), ty_info.expr_tys.len());
    let mut lowering = Lowering {
        next_body: BodyId::from_raw(0),
        ast: &ast,
        hir: Hir::default(),
        ty_info,
        methods: BTreeMap::default(),
    };
    lowering.hir.root = lowering.lower_items(&ast.root.items);
    lowering.hir
}

struct Lowering<'ast, 'tcx> {
    ast: &'ast Ast,
    hir: Hir<'tcx>,
    ty_info: TyInfo<'tcx>,
    methods: BTreeMap<(TyKey<'tcx>, Symbol), BodyId>,
    next_body: BodyId,
}

impl<'tcx> Lowering<'_, 'tcx> {
    fn get_ty(&self, expr_id: ast::ExprId) -> Ty<'tcx> {
        self.ty_info.expr_tys[expr_id]
    }

    fn lower_items(&mut self, items: &[ast::ItemId]) -> Vec<hir::ExprId> {
        let mut exprs = vec![];
        for &item in items {
            exprs.push(self.lower_item(item));
        }
        exprs
    }

    fn lower_item(&mut self, item: ast::ItemId) -> hir::ExprId {
        let item = &self.ast.items[item];
        match &item.kind {
            ast::ItemKind::FnDecl(decl) => {
                let body = self.next_body.incr();
                let expr = self.lower_fn_decl(None, decl, body);
                self.hir.exprs.push(expr)
            }
            ast::ItemKind::Module(name, module) => {
                let body = self.lower_items(&module.items).into();
                self.hir.exprs.push(hir::ExprKind::Module(name.symbol, body).with(Ty::UNIT))
            }
            ast::ItemKind::Struct(ident, generics, fields) => {
                _ = generics;
                let struct_ty = self.ty_info.struct_types[&ident.span];

                let fields: ThinVec<_> = (fields.iter())
                    .map(|field| hir::Param {
                        ident: field.ident.symbol,
                        ty: self.ty_info[field.ty],
                    })
                    .collect();

                let body_id = self.next_body.incr();
                let body =
                    ThinVec::from([self.hir.exprs.push(hir::ExprKind::StructInit.with(struct_ty))]);
                self.hir.exprs.push(hir::Expr::from(hir::FnDecl {
                    id: body_id,
                    ident: ident.symbol,
                    for_ty: None,
                    params: fields.into(),
                    ret: struct_ty,
                    body,
                }))
            }
            ast::ItemKind::Impl(impl_) => {
                let mut block = thin_vec![];
                for &method in &impl_.methods {
                    let ast::ItemKind::FnDecl(decl) = &self.ast.items[method].kind else {
                        unreachable!()
                    };
                    let ty = self.ty_info[impl_.ty];
                    let body = self.next_body.incr();
                    self.methods.insert((TyKey(ty), decl.ident.symbol), body);
                    let expr = self.lower_fn_decl(Some(self.ty_info[impl_.ty]), decl, body);
                    block.push(self.hir.exprs.push(expr));
                }
                self.hir.exprs.push(hir::ExprKind::Block(block).with(Ty::UNIT))
            }
            _ => todo!(),
        }
    }

    fn lower(&mut self, ast_expr: ast::ExprId) -> hir::ExprId {
        let hir_expr = self.lower_inner(ast_expr);
        self.hir.exprs.push(hir_expr)
    }

    #[allow(clippy::too_many_lines)]
    fn lower_inner(&mut self, expr_id: ast::ExprId) -> hir::Expr<'tcx> {
        let expr_ty = self.get_ty(expr_id);
        match self.ast.exprs[expr_id].kind {
            ast::ExprKind::Unreachable => ExprKind::Unreachable.with(Ty::NEVER),
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
                let op = OpAssign::try_from(op.kind).unwrap();
                let place = self.lower(lhs);
                let expr = self.lower(rhs);
                ExprKind::OpAssign { place, op, expr }.with(Ty::UNIT)
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
                    BinOpKind::And => hir::BinaryOp::And,
                    BinOpKind::Or => hir::BinaryOp::Or,
                    _ => unreachable!(),
                };
                (hir::ExprKind::Binary { lhs: self.lower(lhs), op, rhs: self.lower(rhs) })
                    .with(expr_ty)
            }
            ast::ExprKind::Block(block) => self.lower_block(block),
            ast::ExprKind::Lit(ref lit) => self.lower_literal(lit, expr_id),
            ast::ExprKind::Let { ident, expr, .. } => self.lower_let_stmt(ident.symbol, expr),
            ast::ExprKind::If { ref arms, els } => self.lower_if_stmt(arms, els, expr_id),
            ast::ExprKind::Match { scrutinee, ref arms } => {
                self.lower_match(scrutinee, arms, expr_id)
            }
            ast::ExprKind::Is { scrutinee, ref pat } => {
                let scrutinee = self.lower(scrutinee);
                let pat = self.lower_pat(pat);
                (hir::ExprKind::Match {
                    new_scope: false,
                    scrutinee,
                    arms: [
                        hir::MatchArm { pat, body: self.hir.exprs.push(hir::Expr::TRUE) },
                        hir::MatchArm {
                            pat: Pat::Wildcard,
                            body: self.hir.exprs.push(hir::Expr::FALSE),
                        },
                    ]
                    .into(),
                })
                .with(Ty::BOOL)
            }
            ast::ExprKind::While { condition, block } => self.lower_while_loop(condition, block),
            ast::ExprKind::For { ident, iter, body } => {
                self.lower_for_loop(ident.symbol, iter, body)
            }
            ast::ExprKind::Path(ref path) => {
                hir::ExprKind::Path(self.lower_path(path)).with(expr_ty)
            }
            ast::ExprKind::FnCall { function, ref args } => {
                self.lower_fn_call(function, args, expr_id)
            }
            ast::ExprKind::MethodCall { expr, method, ref args, .. } => {
                let ty = self.ty_info.expr_tys[expr];
                let fn_ty = self.ty_info.method_types[&expr_id];
                let TyKind::Function(Function { params, .. }) = fn_ty.0 else { unreachable!() };

                let mut expr = self.lower(expr);
                expr = self.make_eq_ref(expr, ty, params[0]);

                let mut new_args = ThinVec::with_capacity(args.len() + 1);
                new_args.push(expr);
                new_args.extend(args.iter().map(|arg| self.lower(*arg)));

                let location = self.methods[&(TyKey(ty), method.symbol)];

                let function = self.hir.exprs.push(hir::ExprKind::Func(location).with(fn_ty));
                (hir::ExprKind::FnCall { function, args: new_args }).with(self.get_ty(expr_id))
            }
            ast::ExprKind::Index { expr, index } => (ExprKind::Index {
                expr: self.lower(expr),
                index: self.lower(index),
                span: self.ast.exprs[expr_id].span,
            })
            .with(expr_ty),
            ast::ExprKind::Return(expr) => {
                let inner = match expr {
                    Some(expr) => self.lower(expr),
                    None => self.hir.exprs.push(hir::Expr::UNIT),
                };
                ExprKind::Return(inner).with(Ty::NEVER)
            }
            ast::ExprKind::Unary { op, expr } => self.lower(expr).unary(op).with(expr_ty),
            ast::ExprKind::Break => hir::Expr::BREAK,
            ast::ExprKind::Continue => hir::Expr::CONTINUE,
            ast::ExprKind::Assert(expr) => {
                let msg = self.assert_failed_error(expr);
                let abort = (self.hir.exprs).push(ExprKind::Abort { msg }.with(Ty::NEVER));

                let body = ThinVec::from([abort]);
                let condition = self.lower_then_not(expr);
                let arms = thin_vec![IfStmt { condition, body }];
                (hir::ExprKind::If { arms, els: None }).with(Ty::UNIT)
            }
            ast::ExprKind::FieldAccess { expr, field, .. } => {
                let TyKind::Struct(strct) = self.get_ty(expr).0 else { unreachable!() };
                let expr = self.lower(expr);

                let field = strct.fields.iter().position(|&(s, _)| s == field.symbol).unwrap();
                (hir::ExprKind::Field { expr, field }).with(expr_ty)
            }
        }
    }

    fn make_eq_ref(
        &mut self,
        mut lhs: hir::ExprId,
        ty: Ty<'tcx>,
        expected: Ty<'tcx>,
    ) -> hir::ExprId {
        let depth_lhs = ty.ref_depth();
        let depth_expected = expected.ref_depth();

        for _ in 0..depth_lhs.saturating_sub(depth_expected) {
            lhs = self
                .hir
                .exprs
                .push((ExprKind::Unary { op: ast::UnaryOp::Deref, expr: lhs }).with(ty));
        }
        for _ in 0..depth_expected.saturating_sub(depth_lhs) {
            lhs = self
                .hir
                .exprs
                .push((ExprKind::Unary { op: ast::UnaryOp::Ref, expr: lhs }).with(ty));
        }
        lhs
    }

    fn lower_then_not(&mut self, ast_expr: ast::ExprId) -> hir::ExprId {
        let hir_expr = self.lower(ast_expr).unary(hir::UnaryOp::Not).with(Ty::BOOL);
        self.hir.exprs.push(hir_expr)
    }

    fn assert_failed_error(&self, expr: ast::ExprId) -> Symbol {
        let span = self.ast.exprs[expr].span;
        let report = errors::error("assertion failed", [(span, "")]);
        Symbol::from(format!("{report:?}"))
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
        let condition = self.lower(condition);
        let break_ = self.hir.exprs.push(hir::Expr::BREAK);

        let body = self.lower_block_inner(body).1;
        let if_stmt = (ExprKind::If {
            arms: ThinVec::from([hir::IfStmt { condition, body }]),
            els: Some(break_),
        })
        .with(Ty::UNIT);
        let if_stmt = self.hir.exprs.push(if_stmt);
        ExprKind::Loop(if_stmt).with(Ty::UNIT)
    }

    fn lower_for_loop(
        &mut self,
        ident: Symbol,
        iter: ast::ExprId,
        body: ast::BlockId,
    ) -> hir::Expr<'tcx> {
        let iter = self.lower(iter);
        let body = self.lower_block_inner(body).1;
        (hir::ExprKind::ForLoop { ident, iter, body }).with(Ty::UNIT)
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

        let els = els.map(|els| {
            let els = self.lower_block(els);
            self.hir.exprs.push(els)
        });
        (ExprKind::If { arms, els }).with(self.get_ty(id))
    }

    fn lower_match(
        &mut self,
        scrutinee: ast::ExprId,
        arms: &[ast::MatchArm],
        id: ast::ExprId,
    ) -> hir::Expr<'tcx> {
        let scrutinee = self.lower(scrutinee);
        (hir::ExprKind::Match {
            new_scope: true,
            scrutinee,
            arms: arms
                .iter()
                .map(|arm| hir::MatchArm {
                    pat: self.lower_pat(&arm.pat),
                    body: self.lower(arm.body),
                })
                .collect(),
        })
        .with(self.ty_info.expr_tys[id])
    }

    fn lower_pat(&mut self, pat: &ast::Pat) -> Pat<'tcx> {
        match pat.kind {
            ast::PatKind::Range(ref pats, inclusive) => {
                let lhs = pats[0].as_ref().map(|pat| self.lower_pat(pat));
                let rhs = pats[1].as_ref().map(|pat| self.lower_pat(pat));
                hir::Pat::Range(Box::new([lhs, rhs]), inclusive)
            }
            ast::PatKind::RangeFull => Pat::Wildcard,
            ast::PatKind::Bool(true) => hir::Pat::Expr(self.hir.exprs.push(hir::Expr::TRUE)),
            ast::PatKind::Bool(false) => hir::Pat::Expr(self.hir.exprs.push(hir::Expr::FALSE)),
            ast::PatKind::Struct(ident, ref fields) => hir::Pat::Struct(
                self.ty_info.struct_pat_types[&ident.span],
                fields
                    .iter()
                    .map(|field| PatField {
                        ident: field.ident.symbol,
                        pat: self.lower_pat(&field.pat),
                    })
                    .collect(),
            ),
            ast::PatKind::Ident(ident) if ident.as_str() == "_" => Pat::Wildcard,
            ast::PatKind::Ident(ident) => Pat::Ident(ident),
            ast::PatKind::Str(str) => Pat::Expr(
                self.hir.exprs.push(ExprKind::Literal(hir::Lit::String(str)).with(Ty::STR)),
            ),
            ast::PatKind::Int(int) => {
                Pat::Expr(self.hir.exprs.push(ExprKind::Literal(hir::Lit::Int(int)).with(Ty::INT)))
            }
            ast::PatKind::Expr(block) => {
                let expr = self.lower_block(block);
                Pat::Expr(self.hir.exprs.push(expr))
            }
            ast::PatKind::If(expr) => hir::Pat::If(self.lower(expr)),
            ast::PatKind::Or(ref patterns) => {
                Pat::Or(patterns.iter().map(|pat| self.lower_pat(pat)).collect())
            }
            ast::PatKind::And(ref pats) => {
                Pat::And(pats.iter().map(|pat| self.lower_pat(pat)).collect())
            }
            ast::PatKind::Array(ref pats) => {
                Pat::Array(pats.iter().map(|pat| self.lower_pat(pat)).collect())
            }
        }
    }

    fn lower_let_stmt(&mut self, ident: Symbol, expr: ast::ExprId) -> hir::Expr<'tcx> {
        (hir::ExprKind::Let { ident, expr: self.lower(expr) }).with(Ty::UNIT)
    }

    #[expect(clippy::unused_self)]
    fn lower_path(&mut self, path: &ast::Path) -> hir::Path {
        let segments = path.segments.iter().map(|ident| ident.symbol).collect();
        hir::Path { segments }
    }

    fn lower_fn_decl(
        &mut self,
        for_ty: Option<Ty<'tcx>>,
        decl: &ast::FnDecl,
        id: BodyId,
    ) -> hir::Expr<'tcx> {
        let ast::FnDecl { ident, ref params, ret, block, .. } = *decl;

        let block = block.unwrap();

        let ret = ret.map_or(Ty::UNIT, |ret| self.ty_info[ret]);

        let params = params
            .iter()
            .map(|param| hir::Param {
                ident: param.ident.symbol,
                ty: param.ty.map_or_else(|| for_ty.unwrap(), |param_ty| self.ty_info[param_ty]),
            })
            .collect();
        let (_, body) = self.lower_block_inner(block);
        (hir::FnDecl { id, ident: ident.symbol, for_ty, params, ret, body }).into()
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
        let block_ty = if let Some(expr) = block.expr { self.get_ty(expr) } else { Ty::UNIT };
        let needs_unit = self.block_needs_terminating_unit(block);

        let mut new = ThinVec::with_capacity(block.stmts.len() + usize::from(needs_unit));
        for &stmt in &block.stmts {
            new.push(match stmt {
                Stmt::Expr(expr) => self.lower(expr),
                Stmt::Item(item) => self.lower_item(item),
            });
        }
        if let Some(expr) = block.expr {
            new.push(self.lower(expr));
        }
        if needs_unit {
            new.push(self.hir.exprs.push(hir::Expr::UNIT));
        }
        (block_ty, new)
    }

    fn block_needs_terminating_unit(&self, block: &ast::Block) -> bool {
        // if a block isn't terminated by a semicolon then it already returns the correct type.
        if block.expr.is_some() {
            return false;
        }
        block.stmts.last().is_some_and(|last| match last {
            Stmt::Expr(expr) => self.get_ty(*expr) != Ty::UNIT,
            Stmt::Item(..) => false,
        })
    }
}
