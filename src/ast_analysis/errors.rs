use super::Collector;
use crate::{
    ast::{BlockId, ExprId, ExprKind},
    span::Span,
    symbol::Symbol,
    ty::Ty,
};

impl<'tcx> Collector<'_, '_, 'tcx> {
    pub fn expected_function(&self, ty: Ty<'tcx>, span: Span) -> miette::Error {
        let ty = self.tcx.try_infer_deep(ty).unwrap_or_else(|ty| ty);
        self.raw_error(
            &format!("expected function, found `{ty}`"),
            [(span, format!("`{ty}` is not callable"))],
        )
    }

    pub fn invalid_arg_count(
        &self,
        arg_count: usize,
        param_count: usize,
        func_span: Span,
        expr_span: Span,
    ) -> miette::Error {
        let span_start = func_span.end() as usize;
        let span_end = expr_span.end() as usize;
        let span = Span::new(span_start..span_end, func_span.source());

        let s = if arg_count > param_count { "too many arguments" } else { "missing arguments" };
        self.raw_error(&format!("expected {param_count} arguments, found {arg_count}"), [(span, s)])
    }

    pub fn cannot_infer(&self, ty: Ty<'tcx>, span: Span) -> miette::Error {
        self.raw_error(&format!("cannot infer type {ty}"), [(span, "cannot infer")])
    }
    pub fn cannot_deref(&self, ty: Ty<'tcx>, span: Span) -> miette::Error {
        let ty = self.tcx.try_infer_deep(ty).unwrap_or_else(|ty| ty);
        self.raw_error(
            &format!("type '{ty}' cannot be dereferenced"),
            [(span, format!("cannot deref `{ty}`"))],
        )
    }
    pub fn ident_not_found(&self, ident: Symbol, span: Span) -> miette::Error {
        self.raw_error(
            &format!("identifer '{ident}' not found"),
            [(span, format!("'{ident}' not found"))],
        )
    }
    pub fn unknown_type_err(&self, span: Span) -> miette::Error {
        self.raw_error("unknown type", [(span, "here")])
    }
    #[cold]
    #[inline(never)]
    pub fn subtype_err(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, expr: ExprId) -> miette::Error {
        self.subtype_err_inner(lhs, rhs, self.invalid_type_span(expr))
    }
    #[cold]
    #[inline(never)]
    pub fn subtype_err_block(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, block: BlockId) -> miette::Error {
        self.subtype_err_inner(lhs, rhs, self.block_span(block))
    }

    #[cold]
    #[inline(never)]
    fn subtype_err_inner(&self, lhs: Ty<'tcx>, rhs: Ty<'tcx>, spans: Vec<Span>) -> miette::Error {
        let lhs = self.tcx.try_infer_deep(lhs).unwrap_or_else(|ty| ty);
        let rhs = self.tcx.try_infer_deep(rhs).unwrap_or_else(|ty| ty);
        self.raw_error(
            "mismatched types",
            spans.into_iter().map(|span| (span, format!("expected `{rhs}`, found `{lhs}`"))),
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
        block.stmts.last().map_or(vec![block.span], |&last| self.invalid_type_span(last))
    }

    fn raw_error<S>(&self, msg: &str, labels: impl IntoIterator<Item = (Span, S)>) -> miette::Error
    where
        S: Into<String>,
    {
        crate::errors::error(msg, self.file, self.src, labels)
    }
}
