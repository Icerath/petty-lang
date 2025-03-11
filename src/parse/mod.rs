mod expr;
mod lex;
mod token;

use crate::{
    ast::{
        ArraySeg, Ast, BinaryOp, Block, BlockId, Expr, ExprId, IfStmt, Lit, Param, StructInitField,
        Ty, TypeId,
    },
    symbol::Symbol,
};
use lex::Lexer;
use miette::{LabeledSpan, Result, miette};
use thin_vec::{ThinVec, thin_vec};
use token::{Token, TokenKind};

pub fn parse(src: &str) -> Result<Ast> {
    let lexer = Lexer::new(src);
    let mut ast = Ast::default();
    let mut stream = Stream { lexer, ast: &mut ast };
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

struct Stream<'src> {
    lexer: Lexer<'src>,
    ast: &'src mut Ast,
}

impl Stream<'_> {
    fn next(&mut self) -> Result<Token> {
        if let Some(result) = self.lexer.next() {
            return result;
        }
        Err(self.handle_eof())
    }
    fn peek(&mut self) -> Result<Token> {
        Stream { lexer: self.lexer.clone(), ast: self.ast }.next()
    }
    #[inline(never)]
    #[cold]
    fn handle_eof(&self) -> miette::Error {
        let label = LabeledSpan::at(self.lexer.span_eof(), "EOF");
        miette::miette!(labels = vec![label], "Unexpected EOF")
            .with_source_code(self.lexer.src().to_string())
    }
    fn expect(&mut self, kind: TokenKind) -> Result<Token> {
        let token = self.next()?;
        if token.kind != kind {
            let label = LabeledSpan::at(self.lexer.span(), "here");
            return Err(miette!(
                labels = vec![label],
                "expected `{}`, found `{}`",
                kind.repr(),
                token.kind.repr()
            )
            .with_source_code(self.lexer.src().to_string()));
        }
        Ok(token)
    }
    fn any(&mut self, toks: &[TokenKind]) -> Result<Token> {
        let token = self.next()?;
        if toks.contains(&token.kind) {
            return Ok(token);
        }
        let label = LabeledSpan::at(self.lexer.span(), "here");
        Err(miette!(
            labels = vec![label],
            "expected one of {}, found `{}`",
            toks.iter().map(|kind| format!("`{}`", kind.repr())).collect::<Vec<_>>().join(" or "),
            token.kind.repr()
        )
        .with_source_code(self.lexer.src().to_string()))
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
        while self.peek()?.kind != term {
            let expr = self.parse()?;
            args.push(expr);
            if self.peek()?.kind == term {
                break;
            }
            self.expect(sep)?;
        }
        _ = self.next();
        Ok(args)
    }
}

trait Parse: Sized {
    fn parse(stream: &mut Stream) -> Result<Self>;
}

impl Parse for Block {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let mut stmts = thin_vec![];
        let mut is_expr = false;

        loop {
            let tok = stream.peek()?;
            match tok.kind {
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
        Ok(Block { stmts, is_expr })
    }
}

impl Parse for ExprId {
    fn parse(stream: &mut Stream) -> Result<Self> {
        parse_expr(stream, true)
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

fn parse_expr(stream: &mut Stream, allow_struct_init: bool) -> Result<ExprId> {
    expr::parse_expr_inner(stream, 0, allow_struct_init)
}

impl Parse for Ty {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let any = stream.any(&[TokenKind::Ident, TokenKind::LBracket, TokenKind::LParen])?;
        Ok(match any.kind {
            TokenKind::Ident => Ty::Name(Symbol::from(&stream.lexer.src()[any.span])),
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
    if let TokenKind::ThinArrow = chosen.kind {
        ret = Some(stream.parse()?);
        stream.expect(TokenKind::LBrace)?;
    }
    let block = stream.parse()?;
    Ok(Expr::FnDecl { ident, params, ret, block })
}

fn parse_let(stream: &mut Stream) -> Result<Expr> {
    let ident = stream.expect_ident()?;
    let tok = stream.any(&[TokenKind::Colon, TokenKind::Eq])?;
    let mut ty = None;
    if let TokenKind::Colon = tok.kind {
        ty = Some(stream.parse()?);
        stream.expect(TokenKind::Eq)?;
    }
    let expr = stream.parse()?;
    Ok(Expr::Let { ident, ty, expr })
}

fn parse_while(stream: &mut Stream) -> Result<Expr> {
    let condition = stream.parse()?;
    stream.expect(TokenKind::LBrace)?;
    let block = stream.parse()?;
    Ok(Expr::While { condition, block })
}

fn parse_ifchain(stream: &mut Stream) -> Result<Expr> {
    let mut arms = thin_vec![];
    let els = loop {
        let condition = stream.parse()?;
        stream.expect(TokenKind::LBrace)?;
        let body = stream.parse()?;
        arms.push(IfStmt { condition, body });
        let next = stream.peek()?;
        if !(next.kind == TokenKind::Ident && &stream.lexer.src()[next.span] == "else") {
            break None;
        }
        _ = stream.next();
        let next = stream.peek()?;
        if next.kind == TokenKind::Ident && &stream.lexer.src()[next.span] == "if" {
            _ = stream.next();
            continue;
        }
        stream.expect(TokenKind::LBrace)?;
        break Some(stream.parse()?);
    };
    Ok(Expr::If { arms, els })
}

impl Parse for StructInitField {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let field = stream.expect_ident()?;
        let mut expr = None;
        if stream.peek()?.kind == TokenKind::Colon {
            _ = stream.next();
            expr = Some(stream.parse()?);
        }
        Ok(Self { field, expr })
    }
}

impl Parse for ArraySeg {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let expr = stream.parse()?;
        let mut repeated = None;
        if stream.peek()?.kind == TokenKind::Semicolon {
            _ = stream.next();
            repeated = Some(stream.parse()?);
        }
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

impl TryFrom<TokenKind> for BinaryOp {
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
    macro_rules! kw {
        ($kw: ident) => {
            &stream.lexer.src()[tok.span] == stringify!($kw)
        };
    }

    macro_rules! lit {
        ($lit: expr) => {
            Ok(Expr::Lit($lit))
        };
    }

    let expr = match tok.kind {
        TokenKind::LBrace => Ok(Expr::Block(stream.parse()?)),
        TokenKind::Ident if kw!(fn) => parse_fn(stream),
        TokenKind::Ident if kw!(let) => parse_let(stream),
        TokenKind::Ident if kw!(while) => parse_while(stream),
        TokenKind::Ident if kw!(if) => parse_ifchain(stream),
        TokenKind::Ident if &stream.lexer.src()[tok.span] == "true" => lit!(Lit::Bool(true)),
        TokenKind::Ident if &stream.lexer.src()[tok.span] == "false" => lit!(Lit::Bool(false)),
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
        TokenKind::Ident => Ok(Expr::Ident(stream.lexer.src()[tok.span].into())),
        found => {
            let label = LabeledSpan::at(stream.lexer.span(), "here");
            return Err(miette::miette!(
                labels = vec![label],
                "expected `expression`, found {found:?}",
            )
            .with_source_code(stream.lexer.src().to_string()));
        }
    };
    Ok(stream.ast.exprs.push(expr?))
}
