use miette::Result;

use super::{Parse, Stream, parse_atom_with, token::Token};
use crate::{
    ast::{BinOpKind, BinaryOp, ExprId, ExprKind, Pat, UnaryOp},
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
    const EQ_PRECEDENCE: usize = 3;
    const _: () = {
        let mut i = 0;
        let mut found = false;
        while i < OPS[EQ_PRECEDENCE].len() {
            if matches!(OPS[EQ_PRECEDENCE][i], BinOpKind::Eq) {
                found = true;
            }
            i += 1;
        }
        assert!(found);
    };

    let Some(&ops) = OPS.get(precedence as usize) else {
        return parse_unary_expr(stream);
    };
    let mut root = parse_expr(stream, precedence + 1)?;
    loop {
        let token = stream.lexer.clone().next();
        let Ok(op) = BinOpKind::try_from(token) else {
            //
            if precedence as usize == EQ_PRECEDENCE && token == Token::Is {
                _ = stream.next();
                let pat: Pat = stream.parse()?;
                let root_span = stream.ast.exprs[root].span;
                let span =
                    Span::new(root_span.start() as _..pat.span.end() as _, root_span.source());
                root = (stream.ast.exprs)
                    .push((ExprKind::Is { scrutinee: root, pat }).with_span(span));
                continue;
            }
            break;
        };
        if !ops.contains(&op) {
            break;
        }
        _ = stream.next();
        let op = BinaryOp { kind: op, span: stream.lexer.span() };
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
        match stream.peek() {
            Token::LParen => {
                _ = stream.next();
                let args = stream.parse_separated(Token::Comma, Token::RParen)?;
                let span = stream.ast.exprs[expr].span.with_end(stream.lexer.current_pos());
                expr = (stream.ast.exprs)
                    .push((ExprKind::FnCall { function: expr, args }).with_span(span));
            }
            Token::Dot => 'block: {
                _ = stream.next();
                let field = stream.parse()?;
                if stream.peek() != Token::LParen {
                    let span = stream.ast.exprs[expr].span.with_end(stream.lexer.current_pos());
                    expr = (stream.ast.exprs)
                        .push((ExprKind::FieldAccess { expr, field }).with_span(span));
                    break 'block;
                }
                _ = stream.next();
                let args = stream.parse_separated(Token::Comma, Token::RParen)?;
                let span = stream.ast.exprs[expr].span.with_end(stream.lexer.current_pos());
                expr = (stream.ast.exprs)
                    .push((ExprKind::MethodCall { expr, method: field, args }).with_span(span));
            }
            Token::LBracket => {
                _ = stream.next();
                let index = stream.parse()?;
                stream.expect(Token::RBracket)?;
                let span = stream.ast.exprs[expr].span.with_end(stream.lexer.current_pos());
                expr = stream.ast.exprs.push((ExprKind::Index { expr, index }).with_span(span));
            }
            _ => break,
        }
    }
    Ok(expr)
}

fn parse_unary_expr(stream: &mut Stream) -> Result<ExprId> {
    let token = stream.next();
    let token_span = stream.lexer.span();
    match token {
        kind @ (Token::Minus | Token::Not | Token::Ampersand | Token::Star) => {
            let op = match kind {
                Token::Minus => UnaryOp::Neg,
                Token::Not => UnaryOp::Not,
                Token::Ampersand => UnaryOp::Ref,
                Token::Star => UnaryOp::Deref,
                _ => unreachable!(),
            };
            let expr = parse_unary_expr(stream)?;
            let span = token_span.with_end(stream.ast.exprs[expr].span.end());
            Ok(stream.ast.exprs.push((ExprKind::Unary { op, expr }).with_span(span)))
        }
        _ => parse_leaf_expr(stream, token),
    }
}
