mod expr;
mod lex;
mod token;

use std::path::Path;

use crate::{
    ast::{
        ArraySeg, Ast, BinOpKind, BinaryOp, Block, BlockId, Expr, ExprId, ExprKind, FnDecl, IfStmt,
        Lit, Param, Ty, TypeId,
    },
    errors,
    span::Span,
    symbol::Symbol,
};
use lex::Lexer;
use miette::{Error, Result};
use thin_vec::{ThinVec, thin_vec};
use token::{Token, TokenKind};

pub fn parse(src: &str, path: Option<&Path>) -> Result<Ast> {
    let lexer = Lexer::new(src);
    let mut ast = Ast::default();
    let mut stream = Stream { lexer, ast: &mut ast, path };
    let mut top_level = vec![];
    while let Some(next) = stream.lexer.clone().next() {
        if next?.kind == TokenKind::Semicolon {
            _ = stream.lexer.next();
            continue;
        }
        top_level.push(stream.parse()?);
    }
    ast.top_level = top_level;
    Ok(ast)
}

struct Stream<'src, 'path> {
    lexer: Lexer<'src>,
    ast: &'src mut Ast,
    path: Option<&'path Path>,
}

impl Stream<'_, '_> {
    fn next(&mut self) -> Result<Token> {
        if let Some(result) = self.lexer.next() {
            return result;
        }
        Err(self.handle_eof())
    }
    fn peek(&mut self) -> Result<Token> {
        Stream { lexer: self.lexer.clone(), ast: self.ast, path: self.path }.next()
    }
    #[inline(never)]
    #[cold]
    fn handle_eof(&self) -> miette::Error {
        errors::error(
            "unexpected EOF",
            self.path,
            self.lexer.src(),
            &[(self.lexer.span_eof(), "EOF".into())],
        )
    }
    fn expect(&mut self, kind: TokenKind) -> Result<Token> {
        let token = self.next()?;
        if token.kind != kind {
            return Err(errors::error(
                &format!("expected `{}`, found: `{}`", kind.repr(), token.kind.repr()),
                self.path,
                self.lexer.src(),
                &[(self.lexer.span(), "here".into())],
            ));
        }
        Ok(token)
    }
    fn any(&mut self, toks: &[TokenKind]) -> Result<Token> {
        let token = self.next()?;
        if toks.contains(&token.kind) {
            return Ok(token);
        }
        Err(self.any_failed(token, toks))
    }
    #[inline(never)]
    #[cold]
    fn any_failed(&self, found: Token, toks: &[TokenKind]) -> Error {
        errors::error(
            &format!(
                "expected one of {}, found `{}`",
                toks.iter()
                    .map(|kind| format!("`{}`", kind.repr()))
                    .collect::<Vec<_>>()
                    .join(" or "),
                found.kind.repr()
            ),
            self.path,
            self.lexer.src(),
            &[(self.lexer.span(), "here".into())],
        )
    }

    fn expect_ident(&mut self) -> Result<Symbol> {
        let token = self.expect(TokenKind::Ident)?;
        Ok(Symbol::from(&self.lexer.src()[token.span]))
    }
    fn parse<T: Parse>(&mut self) -> Result<T> {
        T::parse(self)
    }
    fn parse_separated<T: Parse>(&mut self, sep: TokenKind, term: TokenKind) -> Result<ThinVec<T>> {
        let mut args = thin_vec![];
        loop {
            if self.peek()?.kind == term {
                _ = self.next();
                break;
            }
            let expr = self.parse()?;
            args.push(expr);
            match self.next()? {
                tok if tok.kind == term => break,
                tok if tok.kind == sep => {}
                found => return Err(self.any_failed(found, &[sep, term])),
            }
        }
        Ok(args)
    }
}

trait Parse: Sized {
    fn parse(stream: &mut Stream) -> Result<Self>;
}

impl Parse for Block {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let start = stream.lexer.current_pos() - 1; // ugly hack to include lbrace in span.
        let mut stmts = thin_vec![];
        let mut is_expr = false;

        loop {
            match stream.peek()?.kind {
                TokenKind::RBrace => {
                    _ = stream.next();
                    break;
                }
                TokenKind::Semicolon => {
                    is_expr = false;
                    _ = stream.next();
                }
                _ => {
                    is_expr = true;
                    stmts.push(stream.parse()?);
                }
            }
        }

        let span = Span::from(start..stream.lexer.current_pos());
        Ok(Self { stmts, is_expr, span })
    }
}

impl Parse for BlockId {
    fn parse(stream: &mut Stream) -> Result<Self> {
        Block::parse(stream).map(|block| stream.ast.blocks.push(block))
    }
}

impl Parse for TypeId {
    fn parse(stream: &mut Stream) -> Result<Self> {
        Ty::parse(stream).map(|block| stream.ast.types.push(block))
    }
}

impl Parse for Ty {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let any = stream.any(&[
            TokenKind::Ident,
            TokenKind::LBracket,
            TokenKind::LParen,
            TokenKind::Not,
        ])?;
        Ok(match any.kind {
            TokenKind::Not => Self::Never,
            TokenKind::Ident => Self::Name(Symbol::from(&stream.lexer.src()[any.span])),
            TokenKind::LBracket => {
                let of = stream.parse()?;
                stream.expect(TokenKind::RBracket)?;
                Self::Array(of)
            }
            TokenKind::LParen => {
                stream.expect(TokenKind::RParen)?;
                Self::Unit
            }
            _ => unreachable!(),
        })
    }
}

fn parse_fn(stream: &mut Stream) -> Result<Expr> {
    let ident = stream.expect_ident()?;
    stream.expect(TokenKind::LParen)?;
    let params = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;

    let chosen = stream.any(&[TokenKind::LBrace, TokenKind::ThinArrow])?;
    let mut ret = None;
    if chosen.kind == TokenKind::ThinArrow {
        ret = Some(stream.parse()?);
        stream.expect(TokenKind::LBrace)?;
    }
    let block = stream.parse()?;
    Ok((ExprKind::FnDecl(FnDecl { ident, params, ret, block })).todo_span())
}

fn parse_struct(stream: &mut Stream) -> Result<Expr> {
    let ident = stream.expect_ident()?;
    stream.expect(TokenKind::LParen)?;
    let fields = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;

    Ok((ExprKind::Struct { ident, fields }).todo_span())
}

fn parse_let(stream: &mut Stream) -> Result<Expr> {
    let ident = stream.expect_ident()?;
    let tok = stream.any(&[TokenKind::Colon, TokenKind::Eq])?;
    let mut ty = None;
    if tok.kind == TokenKind::Colon {
        ty = Some(stream.parse()?);
        stream.expect(TokenKind::Eq)?;
    }
    let expr = stream.parse()?;
    Ok((ExprKind::Let { ident, ty, expr }).todo_span())
}

fn parse_while(stream: &mut Stream) -> Result<Expr> {
    let condition = stream.parse()?;
    stream.expect(TokenKind::LBrace)?;
    let block = stream.parse()?;
    Ok((ExprKind::While { condition, block }).todo_span())
}

fn parse_ifchain(stream: &mut Stream) -> Result<Expr> {
    let mut arms = thin_vec![];
    let els = loop {
        let condition = stream.parse()?;
        stream.expect(TokenKind::LBrace)?;
        let body = stream.parse()?;
        arms.push(IfStmt { condition, body });
        if stream.peek()?.kind != TokenKind::Else {
            break None;
        }
        _ = stream.next();
        if stream.peek()?.kind == TokenKind::If {
            _ = stream.next();
        } else {
            stream.expect(TokenKind::LBrace)?;
            break Some(stream.parse()?);
        }
    };
    Ok((ExprKind::If { arms, els }).todo_span())
}

impl Parse for ArraySeg {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let expr = stream.parse()?;
        let repeated = if stream.peek()?.kind == TokenKind::Semicolon {
            _ = stream.next();
            Some(stream.parse()?)
        } else {
            None
        };
        Ok(Self { expr, repeated })
    }
}

impl Parse for Param {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.expect_ident()?;
        stream.expect(TokenKind::Colon)?;
        let ty = stream.parse()?;
        Ok(Self { ident, ty })
    }
}

impl TryFrom<Token> for BinaryOp {
    type Error = ();
    fn try_from(token: Token) -> Result<Self, Self::Error> {
        let kind = BinOpKind::try_from(token.kind)?;
        Ok(Self { kind, span: token.span })
    }
}

impl TryFrom<TokenKind> for BinOpKind {
    type Error = ();
    fn try_from(kind: TokenKind) -> Result<Self, Self::Error> {
        Ok(match kind {
            TokenKind::Eq => Self::Assign,
            TokenKind::PlusEq => Self::AddAssign,
            TokenKind::MinusEq => Self::SubAssign,
            TokenKind::MulEq => Self::MulAssign,
            TokenKind::DivEq => Self::DivAssign,
            TokenKind::ModEq => Self::ModAssign,

            TokenKind::Plus => Self::Add,
            TokenKind::Minus => Self::Sub,
            TokenKind::Star => Self::Mul,
            TokenKind::Slash => Self::Div,
            TokenKind::Percent => Self::Mod,

            TokenKind::EqEq => Self::Eq,
            TokenKind::Neq => Self::Neq,
            TokenKind::Greater => Self::Greater,
            TokenKind::Less => Self::Less,
            TokenKind::GreaterEq => Self::GreaterEq,
            TokenKind::LessEq => Self::LessEq,

            TokenKind::DotDot => Self::Range,
            TokenKind::DotDotEq => Self::RangeInclusive,
            _ => return Err(()),
        })
    }
}

fn parse_atom_with(stream: &mut Stream, tok: Token) -> Result<ExprId> {
    macro_rules! lit {
        ($lit: expr, $span: expr) => {
            Ok(ExprKind::Lit($lit).with_span($span))
        };
        ($lit: expr) => {
            Ok(ExprKind::Lit($lit).with_span(tok.span))
        };
    }
    macro_rules! all {
        () => {
            Span::from(tok.span.start()..stream.lexer.current_pos())
        };
    }

    let expr = match tok.kind {
        TokenKind::LBrace => Ok(ExprKind::Block(stream.parse()?).with_span(all!())),
        TokenKind::Abort => lit!(Lit::Abort),
        TokenKind::Break => Ok(ExprKind::Break.todo_span()),
        TokenKind::Return => {
            if (stream.lexer.clone().next().transpose()?).is_none_or(|tok| tok.kind.is_terminator())
            {
                Ok(ExprKind::Return(None).with_span(tok.span))
            } else {
                let expr = stream.parse()?;
                let span = tok.span.start()..((&stream.ast.exprs[expr] as &Expr).span.end());
                Ok(ExprKind::Return(Some(expr)).with_span(span))
            }
        }
        TokenKind::Fn => parse_fn(stream),
        TokenKind::Struct => parse_struct(stream),
        TokenKind::Let => parse_let(stream),
        TokenKind::While => parse_while(stream),
        TokenKind::If => parse_ifchain(stream),
        TokenKind::True => lit!(Lit::Bool(true)),
        TokenKind::False => lit!(Lit::Bool(false)),
        TokenKind::Int => lit!(Lit::Int(stream.lexer.src()[tok.span].parse::<i64>().unwrap())),
        TokenKind::Str => {
            // TODO: Escaping
            let str = &stream.lexer.src()[tok.span.shrink(1)];
            lit!(Lit::Str(str.into()))
        }
        TokenKind::Char => {
            // TODO: Escaping
            let str = &stream.lexer.src()[tok.span.shrink(1)];
            lit!(Lit::Char(str.chars().next().unwrap()))
        }
        TokenKind::Ident => {
            Ok(ExprKind::Ident(stream.lexer.src()[tok.span].into()).with_span(tok.span))
        }
        found => {
            return Err(errors::error(
                &format!("expected `expression`, found {found:?}"),
                stream.path,
                stream.lexer.src(),
                &[(stream.lexer.span(), "here".into())],
            ));
        }
    };
    Ok(stream.ast.exprs.push(expr?))
}
