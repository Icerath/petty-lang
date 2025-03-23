use crate::ast::{BinOpKind, BinaryOp, ExprId, ExprKind, Lit, UnaryOp};

use super::{
    Parse, Stream, parse_atom_with,
    token::{Token, TokenKind},
};
use miette::Result;

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
        // &[BinOpKind::Or],
        // &[BinOpKind::And],
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
        return parse_leaf_expr(stream);
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

fn parse_leaf_expr(stream: &mut Stream) -> Result<ExprId> {
    let mut expr = parse_unary_expr(stream)?;

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
                let field = stream.expect_ident()?;
                if stream.peek()?.kind == TokenKind::LParen {
                    _ = stream.next();
                    let end = stream.lexer.current_pos();
                    let span = stream.ast.exprs[expr].span.start()..end;
                    expr = (stream.ast.exprs)
                        .push((ExprKind::FieldAccess { expr, field }).with_span(span));
                    break 'block;
                }
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
    let start = token.span.start();
    let expr = match token.kind {
        kind @ (TokenKind::Minus | TokenKind::Not) => {
            let op = if kind == TokenKind::Minus { UnaryOp::Neg } else { UnaryOp::Not };
            let next = stream.next()?;
            (ExprKind::Unary { op, expr: parse_paren_expr(stream, next)? }).todo_span()
        }
        TokenKind::LBracket => ExprKind::Lit(Lit::Array {
            segments: stream.parse_separated(TokenKind::Comma, TokenKind::RBracket)?,
        })
        .with_span(start..stream.lexer.current_pos()),
        _ => return parse_paren_expr(stream, token),
    };
    Ok(stream.ast.exprs.push(expr))
}

fn parse_paren_expr(stream: &mut Stream, token: Token) -> Result<ExprId> {
    if token.kind == TokenKind::LParen {
        if stream.peek()?.kind == TokenKind::RParen {
            _ = stream.next();
            return Ok(stream.ast.exprs.push(ExprKind::Lit(Lit::Unit).todo_span()));
        }
        let expr = stream.parse()?;
        stream.expect(TokenKind::RParen)?;
        return Ok(expr);
    }
    parse_atom_with(stream, token)
}
