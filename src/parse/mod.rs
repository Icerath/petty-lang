mod expr;
mod lex;
mod token;

use crate::ast::{
    ArraySeg, Ast, BinaryOp, Block, ExprId, IfStmt, Lit, Param, Stmt, StructInitField, Ty,
};
use lex::Lexer;
use miette::{LabeledSpan, Result, miette};
use thin_vec::{ThinVec, thin_vec};
use token::{Token, TokenKind};
use ustr::Ustr as Symbol;

pub fn parse(src: &str) -> Result<Ast> {
    let lexer = Lexer::new(src);
    let ast = Ast::default();
    let mut stream = Stream { lexer, ast: &ast };
    while stream.lexer.clone().next().is_some() {
        ast.push_top(stream.parse()?);
    }
    Ok(ast)
}

#[derive(Clone)]
struct Stream<'src> {
    lexer: Lexer<'src>,
    ast: &'src Ast,
}

impl Stream<'_> {
    fn next(&mut self) -> Result<Token> {
        if let Some(result) = self.lexer.next() {
            return result;
        }
        Err(self.handle_eof())
    }
    fn peek(&self) -> Result<Token> {
        self.clone().next()
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

impl Parse for Stmt {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let tok = stream.peek()?;
        parse_stmt_with(stream, tok)
    }
}

fn parse_stmt_with(stream: &mut Stream, tok: Token) -> Result<Stmt> {
    macro_rules! kw {
        ($kw: ident) => {
            &stream.lexer.src()[tok.span] == stringify!($kw)
        };
    }
    macro_rules! skip {
        ($expr: expr) => {{
            _ = stream.next();
            $expr
        }};
    }

    match tok.kind {
        TokenKind::Ident if kw!(fn) => skip!(parse_fn(stream)),
        TokenKind::Ident if kw!(let) => skip!(parse_let(stream)),
        TokenKind::Ident if kw!(while) => skip!(parse_while(stream)),
        TokenKind::Ident if kw!(if) => skip!(parse_ifchain(stream)),
        _ => Ok(Stmt::Expr(stream.parse()?)),
    }
}

impl Parse for Block {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let mut stmts = thin_vec![];
        loop {
            let tok = stream.peek()?;
            match tok.kind {
                TokenKind::RBrace => {
                    _ = stream.next();
                    break;
                }
                TokenKind::Semicolon => {
                    _ = stream.next();
                    continue;
                }
                _ => stmts.push(parse_stmt_with(stream, tok)?),
            }
        }
        Ok(Block { stmts })
    }
}

impl Parse for ExprId {
    fn parse(stream: &mut Stream) -> Result<Self> {
        parse_expr(stream, true)
    }
}

fn parse_expr(stream: &mut Stream, allow_struct_init: bool) -> Result<ExprId> {
    expr::parse_expr_inner(stream, 0, allow_struct_init)
}

impl Parse for Ty {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let any = stream.any(&[TokenKind::Ident, TokenKind::LBracket])?;
        Ok(match any.kind {
            TokenKind::Ident => Ty::Name(Symbol::from(&stream.lexer.src()[any.span])),
            TokenKind::LBracket => {
                let of = stream.parse()?;
                stream.expect(TokenKind::RBracket)?;
                Self::Array(Box::new(of))
            }
            _ => unreachable!(),
        })
    }
}

fn parse_fn(stream: &mut Stream) -> Result<Stmt> {
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
    Ok(Stmt::FnDecl { ident, params, ret, block })
}

fn parse_let(stream: &mut Stream) -> Result<Stmt> {
    let ident = stream.expect_ident()?;
    let tok = stream.any(&[TokenKind::Colon, TokenKind::Eq])?;
    let mut ty = None;
    if let TokenKind::Colon = tok.kind {
        ty = Some(stream.parse()?);
        stream.expect(TokenKind::Eq)?;
    }
    let expr = stream.parse()?;
    Ok(Stmt::Let { ident, ty, expr })
}

fn parse_while(stream: &mut Stream) -> Result<Stmt> {
    let condition = stream.parse()?;
    stream.expect(TokenKind::LBrace)?;
    let block = stream.parse()?;
    Ok(Stmt::While { condition, block })
}

fn parse_ifchain(stream: &mut Stream) -> Result<Stmt> {
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
    Ok(Stmt::If { arms, els })
}

impl Parse for Lit {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let next = stream.next()?;
        Ok(match next.kind {
            TokenKind::Ident if &stream.lexer.src()[next.span] == "true" => Self::Bool(true),
            TokenKind::Ident if &stream.lexer.src()[next.span] == "false" => Self::Bool(false),
            TokenKind::Int => Self::Int(stream.lexer.src()[next.span].parse::<i64>().unwrap()),
            TokenKind::Str => {
                // TODO: Escaping
                let str = &stream.lexer.src()[next.span.shrink(1)];
                Self::Str(str.into())
            }
            TokenKind::Char => {
                // TODO: Escaping
                let str = &stream.lexer.src()[next.span.shrink(1)];
                Self::Char(str.chars().next().unwrap())
            }
            found => {
                let label = LabeledSpan::at(stream.lexer.span(), "here");
                return Err(miette::miette!(
                    labels = vec![label],
                    "expected `expression`, found {found:?}",
                )
                .with_source_code(stream.lexer.src().to_string()));
            }
        })
    }
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
