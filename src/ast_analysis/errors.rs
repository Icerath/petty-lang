use super::Collector;
use crate::{
    ast::{BlockId, ExprId, ExprKind},
    span::Span,
    symbol::Symbol,
    ty::Ty,
};

impl<'tcx> Collector<'_, '_, 'tcx> {
    pub fn cannot_deref(&self, ty: Ty, span: Span) -> miette::Error {
        self.raw_error(&format!("type '{ty}' cannot be dereferenced"), [(span, "cannot deref")])
    }
    pub fn ident_not_found(&self, ident: Symbol, span: Span) -> miette::Error {
        self.raw_error(
            &format!("indentifer '{ident}' not found"),
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
        self.raw_error(
            "mismatched_typed",
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
