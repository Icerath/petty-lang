use crate::{
    ast::{BinOpKind, BinaryOp, Expr, ExprId, ExprKind, Lit, UnaryOp},
    span::Span,
};

use super::{
    Stream, parse_atom_with,
    token::{Token, TokenKind},
};
use miette::Result;

pub fn parse_expr_inner(
    stream: &mut Stream,
    precedence: u8,
    allow_struct_init: bool,
) -> Result<ExprId> {
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
        return parse_leaf_expr(stream, allow_struct_init);
    };
    let mut root = parse_expr_inner(stream, precedence + 1, allow_struct_init)?;
    loop {
        let Some(token) = stream.lexer.clone().next().transpose()? else { break };
        let Ok(op) = BinaryOp::try_from(token) else { break };
        if !ops.contains(&op.kind) {
            break;
        }
        _ = stream.next();
        let expr = parse_expr_inner(stream, precedence + 1, allow_struct_init)?;
        let span = stream.ast.spans([root, expr]);
        root = stream
            .ast
            .exprs
            .push(Expr { span, kind: ExprKind::Binary { lhs: root, op, rhs: expr } });
    }
    Ok(root)
}

fn parse_leaf_expr(stream: &mut Stream, allow_struct_init: bool) -> Result<ExprId> {
    let mut expr = parse_unary_expr(stream, allow_struct_init)?;

    loop {
        let Some(token) = stream.lexer.clone().next().transpose()? else { break };
        match token.kind {
            TokenKind::LParen => {
                _ = stream.next();
                let args = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                let end = stream.lexer.current_pos();
                let span = (stream.ast.exprs[expr].span.start()..end).into();
                expr = stream
                    .ast
                    .exprs
                    .push(Expr { span, kind: ExprKind::FnCall { function: expr, args } });
            }
            TokenKind::Dot => 'block: {
                _ = stream.next();
                let field = stream.expect_ident()?;
                if stream.peek()?.kind == TokenKind::LParen {
                    _ = stream.next();
                    let end = stream.lexer.current_pos();
                    let span = (stream.ast.exprs[expr].span.start()..end).into();
                    expr = stream
                        .ast
                        .exprs
                        .push(Expr { span, kind: ExprKind::FieldAccess { expr, field } });
                    break 'block;
                }
                let args = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                let end = stream.lexer.current_pos();
                let span = (stream.ast.exprs[expr].span.start()..end).into();
                expr = stream
                    .ast
                    .exprs
                    .push(Expr { span, kind: ExprKind::MethodCall { expr, method: field, args } });
            }
            TokenKind::LBracket => {
                _ = stream.next();
                let index = stream.parse()?;
                stream.expect(TokenKind::RBracket)?;
                let end = stream.lexer.current_pos();
                let span = (stream.ast.exprs[expr].span.start()..end).into();
                expr = stream.ast.exprs.push(Expr { span, kind: ExprKind::Index { expr, index } });
            }
            _ => break,
        }
    }
    if !allow_struct_init {
        return Ok(expr);
    }
    let ExprKind::Ident(ident) = stream.ast.exprs[expr].kind else {
        return Ok(expr);
    };
    let TokenKind::LBrace = stream.peek()?.kind else { return Ok(expr) };
    _ = stream.next();
    let args = stream.parse_separated(TokenKind::Comma, TokenKind::RBrace)?;
    Ok(stream.ast.exprs.push((ExprKind::StructInit { ident, args }).todo_span()))
}

fn parse_unary_expr(stream: &mut Stream, allow_struct_init: bool) -> Result<ExprId> {
    _ = allow_struct_init;
    let token = stream.next()?;
    let kind = match token.kind {
        kind @ (TokenKind::Minus | TokenKind::Not) => {
            let op = if kind == TokenKind::Minus { UnaryOp::Neg } else { UnaryOp::Not };
            let next = stream.next()?;
            ExprKind::Unary { op, expr: parse_paren_expr(stream, next)? }
        }
        TokenKind::LBracket => ExprKind::Lit(Lit::Array {
            segments: stream.parse_separated(TokenKind::Comma, TokenKind::RBracket)?,
        }),
        _ => return parse_paren_expr(stream, token),
    };
    let span = Span::ZERO;
    Ok(stream.ast.exprs.push(Expr { span, kind }))
}

fn parse_paren_expr(stream: &mut Stream, token: Token) -> Result<ExprId> {
    if token.kind == TokenKind::LParen {
        if stream.peek()?.kind == TokenKind::RParen {
            _ = stream.next();
            let span = Span::ZERO;
            return Ok(stream.ast.exprs.push(Expr { span, kind: ExprKind::Lit(Lit::Unit) }));
        }
        let expr = stream.parse()?;
        stream.expect(TokenKind::RParen)?;
        return Ok(expr);
    }
    parse_atom_with(stream, token)
}
