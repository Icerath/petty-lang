use miette::Result;

use super::{
    Parse, Stream, parse_atom_with,
    token::{Token, TokenKind},
};
use crate::{
    ast::{BinOpKind, BinaryOp, ExprId, ExprKind, UnaryOp},
    source::span::Span,
};

impl Parse for ExprId {
    fn parse(stream: &mut Stream) -> Result<Self> {
        parse_expr(stream, 0)
    }
}

fn parse_expr(stream: &mut Stream, precedence: u8) -> Result<ExprId> {
    const OPS: &[&[BinOpKind]] = &[
        &[
            BinOpKind::Assign,
            BinOpKind::AddAssign,
            BinOpKind::SubAssign,
            BinOpKind::MulAssign,
            BinOpKind::DivAssign,
            BinOpKind::ModAssign,
        ],
        &[BinOpKind::Or],
        &[BinOpKind::And],
        &[
            BinOpKind::Eq,
            BinOpKind::Neq,
            BinOpKind::Greater,
            BinOpKind::Less,
            BinOpKind::GreaterEq,
            BinOpKind::LessEq,
        ],
        &[BinOpKind::Range, BinOpKind::RangeInclusive],
        &[BinOpKind::Add, BinOpKind::Sub],
        &[BinOpKind::Mul, BinOpKind::Div, BinOpKind::Mod],
    ];

    let Some(&ops) = OPS.get(precedence as usize) else {
        return parse_unary_expr(stream);
    };
    let mut root = parse_expr(stream, precedence + 1)?;
    loop {
        let Some(token) = stream.lexer.clone().next().transpose()? else { break };
        let Ok(op) = BinaryOp::try_from(token) else { break };
        if !ops.contains(&op.kind) {
            break;
        }
        _ = stream.next();
        let expr = parse_expr(stream, precedence + 1)?;
        let span = stream.ast.spans([root, expr]);
        root = (stream.ast.exprs)
            .push((ExprKind::Binary { lhs: root, op, rhs: expr }).with_span(span));
    }
    Ok(root)
}

fn parse_leaf_expr(stream: &mut Stream, next: Token) -> Result<ExprId> {
    let mut expr = parse_atom_with(stream, next)?;

    loop {
        let Some(token) = stream.lexer.clone().next().transpose()? else { break };
        match token.kind {
            TokenKind::LParen => {
                _ = stream.next();
                let args = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                let end = stream.lexer.current_pos();
                let span = stream.ast.exprs[expr].span.start()..end;
                expr = (stream.ast.exprs)
                    .push((ExprKind::FnCall { function: expr, args }).with_span(span));
            }
            TokenKind::Dot => 'block: {
                _ = stream.next();
                let (field, field_span) = stream.ident_spanned()?;
                if stream.peek()?.kind != TokenKind::LParen {
                    let end = stream.lexer.current_pos();
                    let span = stream.ast.exprs[expr].span.start()..end;
                    expr = (stream.ast.exprs).push(
                        (ExprKind::FieldAccess { expr, field, span: field_span }).with_span(span),
                    );
                    break 'block;
                }
                _ = stream.next();
                let args = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                let end = stream.lexer.current_pos();
                let span = stream.ast.exprs[expr].span.start()..end;
                expr = (stream.ast.exprs)
                    .push((ExprKind::MethodCall { expr, method: field, args }).with_span(span));
            }
            TokenKind::LBracket => {
                _ = stream.next();
                let index = stream.parse()?;
                stream.expect(TokenKind::RBracket)?;
                let end = stream.lexer.current_pos();
                let span = stream.ast.exprs[expr].span.start()..end;
                expr = stream.ast.exprs.push((ExprKind::Index { expr, index }).with_span(span));
            }
            _ => break,
        }
    }
    Ok(expr)
}

fn parse_unary_expr(stream: &mut Stream) -> Result<ExprId> {
    let token = stream.next()?;
    let expr = match token.kind {
        kind @ (TokenKind::Minus | TokenKind::Not | TokenKind::Ampersand | TokenKind::Star) => {
            let op = match kind {
                TokenKind::Minus => UnaryOp::Neg,
                TokenKind::Not => UnaryOp::Not,
                TokenKind::Ampersand => UnaryOp::Ref,
                TokenKind::Star => UnaryOp::Deref,
                _ => unreachable!(),
            };
            let expr = parse_unary_expr(stream)?;
            (ExprKind::Unary { op, expr })
                .with_span(Span::join([token.span, stream.ast.exprs[expr].span]))
        }
        _ => return parse_leaf_expr(stream, token),
    };
    Ok(stream.ast.exprs.push(expr))
}
