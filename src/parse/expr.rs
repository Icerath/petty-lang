use crate::ast::{BinaryOp, Expr, ExprId, Lit, UnaryOp};

use super::{Parse, Stream, token::TokenKind};
use miette::Result;

pub fn parse_expr_inner(
    stream: &mut Stream,
    precedence: u8,
    allow_struct_init: bool,
) -> Result<ExprId> {
    const OPS: &[&[BinaryOp]] = &[
        &[
            BinaryOp::Assign,
            BinaryOp::AddAssign,
            BinaryOp::SubAssign,
            BinaryOp::MulAssign,
            BinaryOp::DivAssign,
            BinaryOp::ModAssign,
        ],
        // &[BinaryOp::Or],
        // &[BinaryOp::And],
        &[
            BinaryOp::Eq,
            BinaryOp::Neq,
            BinaryOp::Greater,
            BinaryOp::Less,
            BinaryOp::GreaterEq,
            BinaryOp::LessEq,
        ],
        &[BinaryOp::Range, BinaryOp::RangeInclusive],
        &[BinaryOp::Add, BinaryOp::Sub],
        &[BinaryOp::Mul, BinaryOp::Div, BinaryOp::Mod],
    ];

    let Some(&ops) = OPS.get(precedence as usize) else {
        return parse_leaf_expr(stream, allow_struct_init);
    };
    let mut root = parse_expr_inner(stream, precedence + 1, allow_struct_init)?;
    loop {
        let token = stream.peek()?;
        let Ok(op) = BinaryOp::try_from(token.kind) else { break };
        if !ops.contains(&op) {
            break;
        }
        _ = stream.next();
        let expr = parse_expr_inner(stream, precedence + 1, allow_struct_init)?;
        root = stream.ast.add(Expr::Binary { lhs: root, op, rhs: expr });
    }
    Ok(root)
}

fn parse_leaf_expr(stream: &mut Stream, allow_struct_init: bool) -> Result<ExprId> {
    let mut expr = parse_unary_expr(stream, allow_struct_init)?;

    loop {
        match stream.peek()?.kind {
            TokenKind::LParen => {
                _ = stream.next();
                let args = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                expr = stream.ast.add(Expr::FnCall { function: expr, args });
            }
            TokenKind::Dot => 'block: {
                _ = stream.next();
                let field = stream.expect_ident()?;
                if stream.peek()?.kind == TokenKind::LParen {
                    _ = stream.next();
                    expr = stream.ast.add(Expr::FieldAccess { expr, field });
                    break 'block;
                }
                let args = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                expr = stream.ast.add(Expr::MethodCall { expr, method: field, args });
            }
            TokenKind::LBracket => {
                _ = stream.next();
                let index = stream.parse()?;
                stream.expect(TokenKind::RBracket)?;
                expr = stream.ast.add(Expr::Index { expr, index });
            }
            _ => break,
        }
    }
    if !allow_struct_init {
        return Ok(expr);
    }
    let Expr::Ident(ident) = *stream.ast.get(expr) else {
        return Ok(expr);
    };
    let TokenKind::LBrace = stream.peek()?.kind else { return Ok(expr) };
    _ = stream.next();
    let args = stream.parse_separated(TokenKind::Comma, TokenKind::RBrace)?;
    Ok(stream.ast.add(Expr::StructInit { ident, args }))
}

fn parse_unary_expr(stream: &mut Stream, allow_struct_init: bool) -> Result<ExprId> {
    let expr = match stream.peek()?.kind {
        kind @ (TokenKind::Minus | TokenKind::Not) => {
            _ = stream.next();
            Ok(Expr::Unary {
                op: if kind == TokenKind::Minus { UnaryOp::Neg } else { UnaryOp::Not },
                expr: parse_expr_inner(stream, 0, allow_struct_init)?,
            })
        }
        TokenKind::LBracket => {
            _ = stream.next();
            parse_array(stream)
        }
        _ => return parse_paren_expr(stream),
    }?;
    Ok(stream.ast.add(expr))
}

fn parse_paren_expr(stream: &mut Stream) -> Result<ExprId> {
    if stream.peek()?.kind == TokenKind::LParen {
        _ = stream.next();
        let expr = parse_expr_inner(stream, 0, true)?;
        stream.expect(TokenKind::RParen)?;
        return Ok(expr);
    }
    if stream.peek()?.kind == TokenKind::Ident {
        return Ok(stream.ast.add(Expr::Ident(stream.expect_ident()?)));
    }
    Ok(stream.ast.add(Expr::Lit(Lit::parse(stream)?)))
}

fn parse_array(stream: &mut Stream) -> Result<Expr> {
    let segments = stream.parse_separated(TokenKind::Comma, TokenKind::RBracket)?;
    Ok(Expr::Lit(Lit::Array { segments }))
}
