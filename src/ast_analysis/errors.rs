use miette::Error;

use super::Collector;
use crate::{
    ast::{BinaryOp, BlockId, ExprId, ExprKind},
    span::Span,
    symbol::Symbol,
    ty::Ty,
};

impl<'tcx> Collector<'_, '_, 'tcx> {
    pub fn cannot_break(&self, span: Span) -> Error {
        self.raw_error("`break` outside of a loop", [(span, "cannot `break` outside of a loop")])
    }
    pub fn cannot_continue(&self, span: Span) -> Error {
        self.raw_error(
            "`continue` while outside of a loop",
            [(span, "cannot `continue` outside of a loop")],
        )
    }

    pub fn cannot_iter(&self, ty: Ty, span: Span) -> Error {
        self.raw_error(
            &format!("type `{}` is not iterable", self.tcx.display(ty)),
            [(span, format!("type `{}` is not iterable", self.tcx.display(ty)))],
        )
    }

    pub fn logical_op_err(
        &self,
        lhs: Ty<'tcx>,
        rhs: Ty<'tcx>,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
    ) -> Error {
        let mut errors = vec![];
        let lhs_error = format!("expected `bool`, found `{}`", self.tcx.display(lhs));
        let rhs_error = format!("expected `bool`, found `{}`", self.tcx.display(rhs));

        if !lhs.is_bool() {
            errors.extend(
                self.invalid_type_span(lhs_expr).into_iter().map(|span| (span, &lhs_error)),
            );
        }
        if !rhs.is_bool() {
            errors.extend(
                self.invalid_type_span(rhs_expr).into_iter().map(|span| (span, &rhs_error)),
            );
        }

        self.raw_error("mismatched types", errors)
    }
    pub fn binop_err(&self, op: BinaryOp, lhs: Ty, rhs: Ty) -> Error {
        let op_name = op.kind.name();
        let msg = if lhs == rhs {
            format!("cannot {op_name} values of type `{}`", self.tcx.display(lhs))
        } else {
            format!(
                "cannot {op_name} values of type `{}` with `{}`",
                self.tcx.display(lhs),
                self.tcx.display(rhs)
            )
        };
        self.raw_error(&msg, [(op.span, format!("`{}` is not valid here", op.kind.symbol()))])
    }

    pub fn cannot_index(&self, ty: Ty<'tcx>, span: Span) -> Error {
        self.raw_error(
            &format!("type `{}` cannot be indexed", self.tcx.display(ty)),
            [(span, format!("cannot index `{}`", self.tcx.display(ty)))],
        )
    }

    pub fn field_error(&self, ty: Ty<'tcx>, field: Symbol, span: Span) -> Error {
        self.raw_error(
            &format!("no field `{field}` on type `{}`", self.tcx.display(ty)),
            [(span, "unknown field")],
        )
    }

    pub fn expected_function(&self, ty: Ty<'tcx>, span: Span) -> Error {
        let ty = self.tcx.try_infer_deep(ty).unwrap_or_else(|ty| ty);
        self.raw_error(
            &format!("expected function, found `{}`", self.tcx.display(ty)),
            [(span, format!("`{}` is not callable", self.tcx.display(ty)))],
        )
    }

    pub fn invalid_arg_count(
        &self,
        arg_count: usize,
        param_count: usize,
        func_span: Span,
        expr_span: Span,
    ) -> Error {
        let span_start = func_span.end() as usize;
        let span_end = expr_span.end() as usize;
        let span = Span::new(span_start..span_end, func_span.source());

        let s = if arg_count > param_count { "too many arguments" } else { "missing arguments" };
        self.raw_error(&format!("expected {param_count} arguments, found {arg_count}"), [(span, s)])
    }

    pub fn cannot_infer(&self, ty: Ty<'tcx>, span: Span) -> Error {
        self.raw_error(
            &format!("cannot infer type {}", self.tcx.display(ty)),
            [(span, "cannot infer")],
        )
    }
    pub fn cannot_deref(&self, ty: Ty<'tcx>, span: Span) -> Error {
        let ty = self.tcx.try_infer_deep(ty).unwrap_or_else(|ty| ty);
        self.raw_error(
            &format!("type '{}' cannot be dereferenced", self.tcx.display(ty)),
            [(span, format!("cannot deref `{}`", self.tcx.display(ty)))],
        )
    }
    pub fn ident_not_found(&self, ident: Symbol, span: Span) -> Error {
        self.raw_error(
            &format!("cannot find '{ident}' in this scope"),
            [(span, format!("'{ident}' not found"))],
        )
    }
    pub fn unknown_type_err(&self, name: Symbol, span: Span) -> Error {
        self.raw_error(
            &format!("cannot find type `{name}` in this scope"),
            [(span, format!("type `{name}` not found"))],
        )
    }
    #[cold]
    #[inline(never)]
    pub fn subtype_err(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, expr: ExprId) -> Error {
        self.subtype_err_inner(lhs, rhs, self.invalid_type_span(expr))
    }
    #[cold]
    #[inline(never)]
    pub fn subtype_err_block(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, block: BlockId) -> Error {
        self.subtype_err_inner(lhs, rhs, self.block_span(block))
    }

    #[cold]
    #[inline(never)]
    fn subtype_err_inner(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, spans: Vec<Span>) -> Error {
        let lhs = self.tcx.try_infer_deep(lhs).unwrap_or_else(|ty| ty);
        let rhs = self.tcx.try_infer_deep(rhs).unwrap_or_else(|ty| ty);
        self.raw_error(
            "mismatched types",
            spans.into_iter().map(|span| {
                (
                    span,
                    format!(
                        "expected `{}`, found `{}`",
                        self.tcx.display(rhs),
                        self.tcx.display(lhs)
                    ),
                )
            }),
        )
    }
    fn invalid_type_span(&self, expr: ExprId) -> Vec<Span> {
        let expr = &self.ast.exprs[expr];
        match expr.kind {
            ExprKind::Block(block) => self.block_span(block),
            ExprKind::If { ref arms, els } => arms
                .iter()
                .map(|arm| arm.body)
                .chain(els)
                .flat_map(|block| self.block_span(block))
                .collect(),
            _ => vec![expr.span],
        }
    }
    fn block_span(&self, block: BlockId) -> Vec<Span> {
        let block = &self.ast.blocks[block];
        block.stmts.last().map_or_else(|| vec![block.span], |&last| self.invalid_type_span(last))
    }

    fn raw_error<S>(&self, msg: &str, labels: impl IntoIterator<Item = (Span, S)>) -> Error
    where
        S: Into<String>,
    {
        crate::errors::error(msg, self.path, self.src, labels)
    }
}
