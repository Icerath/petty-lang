use super::Collector;
use crate::{
    ast::{BlockId, ExprId, ExprKind},
    errors,
    span::Span,
    ty::Ty,
};

impl<'tcx> Collector<'_, '_, 'tcx> {
    pub fn unknown_type_err(&self, span: Span) -> miette::Error {
        errors::error("unknown type", self.file, self.src, [(span, "here")])
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
        let labels =
            spans.into_iter().map(|span| (span, format!("expected `{rhs}`, found `{lhs}`")));
        errors::error("mismatched_types", self.file, self.src, labels)
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
}
