mod expr;
mod lex;
mod token;

use std::path::Path;

use lex::Lexer;
use miette::{Error, IntoDiagnostic, Result};
use thin_vec::{ThinVec, thin_vec};
use token::{Token, TokenKind};

use crate::{
    ast::{
        self, ArraySeg, Ast, BinOpKind, BinaryOp, Block, BlockId, Expr, ExprId, ExprKind, Field,
        FnDecl, Ident, IfStmt, Impl, Item, ItemId, ItemKind, Lit, MatchArm, Module, Param, Pat,
        PatArg, PatKind, Stmt, Trait, Ty, TyKind, TypeId,
    },
    errors,
    span::Span,
    symbol::Symbol,
};

pub fn parse(src: &str, path: &Path) -> Result<Ast> {
    let lexer = Lexer::new(src, path).into_diagnostic()?;
    let mut ast = Ast::default();
    let mut stream = Stream { lexer, ast: &mut ast };
    ast.root.items = stream.parse_items(TokenKind::Eof)?;
    Ok(ast)
}

struct Stream<'src> {
    lexer: Lexer<'src>,
    ast: &'src mut Ast,
}

impl Stream<'_> {
    fn parse_items(&mut self, terminator: TokenKind) -> Result<Vec<ItemId>> {
        let mut items = vec![];
        loop {
            match self.peek().kind {
                kind if kind == terminator => break,
                TokenKind::Semicolon => _ = self.lexer.next(),
                _ => items.push(self.parse()?),
            }
        }
        _ = self.next();
        Ok(items)
    }

    fn next(&mut self) -> Token {
        self.lexer.next()
    }
    fn clone(&mut self) -> Stream {
        Stream { lexer: self.lexer.clone(), ast: self.ast }
    }
    fn peek(&mut self) -> Token {
        self.clone().next()
    }
    fn expect(&mut self, kind: TokenKind) -> Result<Token> {
        let token = self.next();
        if token.kind != kind {
            return Err(errors::error(
                &format!("expected `{}`, found: `{}`", kind.repr(), token.kind.repr()),
                [(self.lexer.span(), format!("expected `{}`", kind.repr()))],
            ));
        }
        Ok(token)
    }
    fn any(&mut self, toks: &[TokenKind]) -> Result<Token> {
        let token = self.next();
        if toks.contains(&token.kind) {
            return Ok(token);
        }
        Err(self.any_failed(token, toks))
    }
    #[inline(never)]
    #[cold]
    fn any_failed(&self, found: Token, toks: &[TokenKind]) -> Error {
        let toks =
            toks.iter().map(|kind| format!("`{}`", kind.repr())).collect::<Vec<_>>().join(" or ");
        errors::error(
            &format!("expected one of {toks}, found `{}`", found.kind.repr()),
            [(self.lexer.span(), format!("expected one of '{toks}'"))],
        )
    }

    fn parse<T: Parse>(&mut self) -> Result<T> {
        T::parse(self)
    }
    fn parse_separated<T: Parse>(&mut self, sep: TokenKind, term: TokenKind) -> Result<ThinVec<T>> {
        let mut args = thin_vec![];
        loop {
            if self.peek().kind == term {
                _ = self.next();
                break;
            }
            let expr = self.parse()?;
            args.push(expr);
            match self.next() {
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

impl Parse for Symbol {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let token = stream.expect(TokenKind::Ident)?;
        Ok(Symbol::from(&stream.lexer.src()[token.span]))
    }
}

impl Parse for Block {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let start = stream.lexer.current_pos() - 1; // ugly hack to include lbrace in span.
        let mut stmts: ThinVec<Stmt> = thin_vec![];
        let mut is_expr = false;

        loop {
            match stream.peek().kind {
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
        let expr = if is_expr {
            if let &Stmt::Expr(expr) = stmts.last().unwrap() {
                stmts.pop();
                Some(expr)
            } else {
                None
            }
        } else {
            None
        };

        let span = Span::new(start..stream.lexer.current_pos(), stream.lexer.source());
        Ok(Self { stmts, expr, span })
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
            TokenKind::Fn,
            TokenKind::Ident,
            TokenKind::LBracket,
            TokenKind::LParen,
            TokenKind::Not,
            TokenKind::Ampersand,
        ])?;
        let start = any.span;
        let kind = match any.kind {
            TokenKind::Fn => {
                stream.expect(TokenKind::LParen)?;
                let params = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                let ret = if stream.peek().kind == TokenKind::ThinArrow {
                    _ = stream.next();
                    Some(stream.parse()?)
                } else {
                    None
                };
                TyKind::Func { params, ret }
            }
            TokenKind::Not => TyKind::Never,
            TokenKind::Ident => {
                let generics = if stream.peek().kind == TokenKind::Less {
                    _ = stream.next();
                    stream.parse_separated(TokenKind::Comma, TokenKind::Greater)?
                } else {
                    ThinVec::new()
                };
                let symbol = Symbol::from(&stream.lexer.src()[any.span]);
                TyKind::Name { ident: Ident { symbol, span: any.span }, generics }
            }
            TokenKind::LBracket => {
                let of = stream.parse()?;
                stream.expect(TokenKind::RBracket)?;
                TyKind::Array(of)
            }
            TokenKind::LParen => {
                if stream.peek().kind == TokenKind::RParen {
                    _ = stream.next();
                    TyKind::Unit
                } else {
                    let ty = stream.parse();
                    stream.next();
                    return ty;
                }
            }
            TokenKind::Ampersand => TyKind::Ref(stream.parse()?),
            _ => unreachable!(),
        };
        Ok(Self { kind, span: start.with_end(stream.lexer.current_pos()) })
    }
}

impl Parse for Impl {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let start = stream.lexer.span(); // FIXME: include impl tok
        let generics = if stream.peek().kind == TokenKind::Less {
            _ = stream.next();
            stream.parse_separated(TokenKind::Comma, TokenKind::Greater)?
        } else {
            ThinVec::new()
        };
        let ty = stream.parse()?;
        stream.expect(TokenKind::LBrace)?;
        let methods = parse_trait_methods(stream)?;
        let span = start.with_end(stream.lexer.current_pos());
        let methods = methods
            .into_iter()
            .map(|decl| stream.ast.items.push(Item { kind: ItemKind::FnDecl(decl), span }))
            .collect();
        Ok(Self { generics, ty, methods })
    }
}

impl Parse for Trait {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.parse()?;
        stream.expect(TokenKind::LBrace)?;
        let methods = parse_trait_methods(stream)?;
        Ok(Self { ident, methods })
    }
}

fn parse_trait_methods(stream: &mut Stream) -> Result<ThinVec<FnDecl>> {
    let mut methods = ThinVec::new();

    loop {
        let next = stream.any(&[TokenKind::Fn, TokenKind::RBrace])?;
        match next.kind {
            TokenKind::Fn => methods.push(stream.parse()?),
            TokenKind::RBrace => break Ok(methods),
            _ => unreachable!(),
        }
    }
}

impl Parse for FnDecl {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.parse()?;
        let peek = stream.clone().any(&[TokenKind::Less, TokenKind::LParen])?;
        let generics = if peek.kind == TokenKind::Less {
            _ = stream.next();
            stream.parse_separated(TokenKind::Comma, TokenKind::Greater)?
        } else {
            ThinVec::new()
        };

        stream.expect(TokenKind::LParen)?;
        let params = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;

        let mut chosen =
            stream.any(&[TokenKind::LBrace, TokenKind::ThinArrow, TokenKind::Semicolon])?;
        let mut ret = None;
        if chosen.kind == TokenKind::ThinArrow {
            ret = Some(stream.parse()?);
            chosen = stream.any(&[TokenKind::Semicolon, TokenKind::LBrace])?;
        }
        let block = if chosen.kind == TokenKind::Semicolon { None } else { Some(stream.parse()?) };
        Ok(Self { ident, generics, params, ret, block })
    }
}

fn parse_struct(stream: &mut Stream) -> Result<ItemKind> {
    let ident = stream.parse()?;
    let peek = stream.clone().any(&[TokenKind::Less, TokenKind::LParen])?;

    let generics = if peek.kind == TokenKind::Less {
        _ = stream.next();
        stream.parse_separated(TokenKind::Comma, TokenKind::Greater)?
    } else {
        ThinVec::new()
    };

    stream.expect(TokenKind::LParen)?;
    let fields = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;

    Ok(ItemKind::Struct(ident, generics, fields))
}

fn parse_const(stream: &mut Stream) -> Result<ItemKind> {
    let (ident, ty, expr) = parse_var(stream)?;
    Ok(ItemKind::Const(ident, ty, expr))
}

fn parse_let(stream: &mut Stream, let_tok: Token) -> Result<Expr> {
    let (ident, ty, expr) = parse_var(stream)?;
    Ok((ExprKind::Let { ident, ty, expr })
        .with_span(let_tok.span.with_end(stream.lexer.current_pos())))
}

fn parse_var(stream: &mut Stream) -> Result<(Ident, Option<TypeId>, ExprId)> {
    let ident = stream.parse()?;
    let tok = stream.any(&[TokenKind::Colon, TokenKind::Eq])?;
    let mut ty = None;
    if tok.kind == TokenKind::Colon {
        ty = Some(stream.parse()?);
        stream.expect(TokenKind::Eq)?;
    }
    let expr = stream.parse()?;
    Ok((ident, ty, expr))
}

fn parse_while(stream: &mut Stream) -> Result<Expr> {
    let condition = stream.parse()?;
    stream.expect(TokenKind::LBrace)?;
    let block = stream.parse()?;
    Ok((ExprKind::While { condition, block }).todo_span())
}

fn parse_for(stream: &mut Stream) -> Result<Expr> {
    let ident = stream.parse()?;
    stream.expect(TokenKind::In)?;
    let iter = stream.parse()?;
    stream.expect(TokenKind::LBrace)?;
    let body = stream.parse()?;
    Ok((ExprKind::For { ident, iter, body }).todo_span())
}

fn parse_match(stream: &mut Stream, tok: Token) -> Result<Expr> {
    let scrutinee = stream.parse()?;
    stream.expect(TokenKind::LBrace)?;
    let arms = stream.parse_separated(TokenKind::Comma, TokenKind::RBrace)?;
    let end = stream.lexer.current_pos();
    let span = Span::new(tok.span.start()..end, tok.span.source());
    Ok((ExprKind::Match { scrutinee, arms }).with_span(span))
}

fn parse_ifchain(stream: &mut Stream, if_tok: Token) -> Result<Expr> {
    let mut arms = thin_vec![];
    let els = loop {
        let condition = stream.parse()?;
        stream.expect(TokenKind::LBrace)?;
        let body = stream.parse()?;
        arms.push(IfStmt { condition, body });
        if stream.peek().kind != TokenKind::Else {
            break None;
        }
        _ = stream.next();
        if stream.peek().kind == TokenKind::If {
            _ = stream.next();
        } else {
            stream.expect(TokenKind::LBrace)?;
            break Some(stream.parse()?);
        }
    };
    let span = if_tok.span.with_end(stream.lexer.current_pos());
    Ok((ExprKind::If { arms, els }).with_span(span))
}

impl Parse for ArraySeg {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let expr = stream.parse()?;
        let repeated = if stream.peek().kind == TokenKind::Semicolon {
            _ = stream.next();
            Some(stream.parse()?)
        } else {
            None
        };
        Ok(Self { expr, repeated })
    }
}

impl Parse for PatArg {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.parse()?;
        stream.expect(TokenKind::Colon)?;
        let pat = stream.parse()?;
        Ok(Self { ident, pat })
    }
}

impl Parse for Pat {
    fn parse(stream: &mut Stream) -> Result<Self> {
        fn parse_single(stream: &mut Stream) -> Result<Pat> {
            let tok = stream.next();
            let kind = match tok.kind {
                TokenKind::Ident if stream.peek().kind == TokenKind::LParen => {
                    _ = stream.next();
                    let symbol = Symbol::from(&stream.lexer.src()[tok.span]);
                    let args = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                    PatKind::Struct(Ident { symbol, span: tok.span }, args)
                }
                TokenKind::Ident => PatKind::Ident(Symbol::from(&stream.lexer.src()[tok.span])),
                TokenKind::True => PatKind::Bool(true),
                TokenKind::False => PatKind::Bool(false),
                TokenKind::Str => {
                    PatKind::Str(Symbol::from(&stream.lexer.src()[tok.span.shrink(1)]))
                }
                TokenKind::Int => {
                    PatKind::Int(stream.lexer.src()[tok.span].parse::<i64>().unwrap())
                }
                TokenKind::LBrace => {
                    let block: BlockId = stream.parse()?;
                    PatKind::Expr(block)
                }
                TokenKind::LBracket => {
                    PatKind::Array(stream.parse_separated(TokenKind::Comma, TokenKind::RBracket)?)
                }
                TokenKind::If => PatKind::If(stream.parse()?),
                TokenKind::LParen => {
                    let pat = stream.parse()?;
                    stream.expect(TokenKind::RParen)?;
                    return Ok(pat);
                }
                _ => {
                    return Err(errors::error(
                        &format!("expected pattern, found '{}'", tok.kind.repr()),
                        [(stream.lexer.span(), "expected pattern")],
                    ));
                }
            };
            let span = Span::new(
                tok.span.start() as _..stream.lexer.current_pos() as _,
                tok.span.source(),
            );
            Ok(Pat { kind, span })
        }
        let mut single = parse_single(stream)?;
        let single_span = single.span;
        loop {
            let next = stream.peek().kind;
            if !matches!(next, TokenKind::Or | TokenKind::And) {
                return Ok(single);
            }
            let mut patterns = thin_vec![single];
            while stream.peek().kind == next {
                _ = stream.next();
                patterns.push(parse_single(stream)?);
            }
            let span = Span::new(
                single_span.start() as _..stream.lexer.current_pos() as _,
                single_span.source(),
            );
            let kind =
                if next == TokenKind::Or { PatKind::Or(patterns) } else { PatKind::And(patterns) };
            single = Pat { kind, span };
        }
    }
}

impl Parse for MatchArm {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let pat = stream.parse()?;
        stream.expect(TokenKind::FatArrow)?;
        let body = stream.parse()?;
        Ok(Self { pat, body })
    }
}

impl Parse for Param {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.parse()?;

        let mut ty = None;
        let next = stream.clone().any(&[TokenKind::Comma, TokenKind::Colon, TokenKind::RParen])?;
        if next.kind == TokenKind::Colon {
            _ = stream.next();
            ty = Some(stream.parse()?);
        }
        Ok(Self { ident, ty })
    }
}

impl Parse for Field {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.parse()?;
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

            TokenKind::And => Self::And,
            TokenKind::Or => Self::Or,
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

    let expr = match tok.kind {
        TokenKind::Unreachable => Ok(ExprKind::Unreachable.with_span(tok.span)),
        TokenKind::LParen => {
            return Ok(if stream.peek().kind == TokenKind::RParen {
                _ = stream.next();
                stream.ast.exprs.push(ExprKind::Lit(Lit::Unit).todo_span())
            } else {
                let expr = stream.parse()?;
                stream.expect(TokenKind::RParen)?;
                expr
            });
        }
        TokenKind::LBracket => Ok(ExprKind::Lit(Lit::Array {
            segments: stream.parse_separated(TokenKind::Comma, TokenKind::RBracket)?,
        })
        .with_span(tok.span.with_end(stream.lexer.current_pos()))),
        TokenKind::LBrace => Ok(ExprKind::Block(stream.parse()?)
            .with_span(tok.span.with_end(stream.lexer.current_pos()))),
        TokenKind::Break => Ok(ExprKind::Break.with_span(tok.span)),
        TokenKind::Continue => Ok(ExprKind::Continue.with_span(tok.span)),
        TokenKind::Assert => {
            let expr: ExprId = stream.parse()?;
            Ok(ExprKind::Assert(expr).with_span(stream.ast.exprs[expr].span))
        }
        TokenKind::Return => {
            if stream.peek().kind.is_terminator() {
                Ok(ExprKind::Return(None).with_span(tok.span))
            } else {
                let expr = stream.parse()?;
                let span = tok.span.with_end((&stream.ast.exprs[expr] as &Expr).span.end());
                Ok(ExprKind::Return(Some(expr)).with_span(span))
            }
        }
        TokenKind::Let => parse_let(stream, tok),
        TokenKind::While => parse_while(stream),
        TokenKind::For => parse_for(stream),
        TokenKind::Match => parse_match(stream, tok),
        TokenKind::If => parse_ifchain(stream, tok),
        TokenKind::True => lit!(Lit::Bool(true)),
        TokenKind::False => lit!(Lit::Bool(false)),
        TokenKind::Int => lit!(Lit::Int(stream.lexer.src()[tok.span].parse::<i64>().unwrap())),
        TokenKind::Str => parse_string(stream, tok.span),
        TokenKind::Char => {
            // TODO: Escaping
            let str = &stream.lexer.src()[tok.span.shrink(1)];
            lit!(Lit::Char(str.chars().next().unwrap()))
        }
        TokenKind::Ident => {
            let ident = Ident { symbol: stream.lexer.src()[tok.span].into(), span: tok.span };
            let mut path = ast::Path::new_single(ident);
            while stream.peek().kind == TokenKind::PathSep {
                _ = stream.next();
                let next = stream.parse()?;
                path.segments.push(next);
            }
            Ok(ExprKind::Path(path).with_span(tok.span))
        }
        found => {
            return Err(errors::error(
                &format!("expected expression, found '{}'", found.repr()),
                [(stream.lexer.span(), "expected expression")],
            ));
        }
    };
    Ok(stream.ast.exprs.push(expr?))
}

fn parse_string(stream: &mut Stream, outer_span: Span) -> Result<Expr> {
    // FIXME: Bring a cross.
    let span = outer_span.shrink(1); // remove double quotes.
    let raw = &stream.lexer.src()[span];
    let lexer_offset = stream.lexer.offset();
    stream.lexer.set_offset(span.start());
    let mut current_start = span.start();
    let mut current = String::new();
    let mut segments = thin_vec![];

    let mut chars = raw.char_indices();

    let mut escaped = false;
    while let Some((char_pos, char)) = chars.next() {
        match char {
            '$' if !escaped && chars.clone().next().is_some_and(|c| c.1 == '{') => {
                let char_pos = chars.next().unwrap().0 + span.start();
                if !current.is_empty() {
                    let current_span = Span::new(current_start..char_pos, stream.lexer.source());
                    let expr =
                        ExprKind::Lit(Lit::Str(current.as_str().into())).with_span(current_span);
                    segments.push(stream.ast.exprs.push(expr));
                    current.clear();
                }

                stream.lexer.bump(char_pos - current_start + 1);
                let offset = stream.lexer.offset();
                segments.push(stream.parse()?);
                let diff = stream.lexer.offset() - offset;

                chars = chars.as_str()[diff..].char_indices();
                let next = chars.next().unwrap();
                assert_eq!(next.1, '}');
                current_start = next.0 + span.start();
            }
            '\\' if !escaped => escaped = true,
            _ if !escaped => current.push(char),
            _ => {
                escaped = false;
                match char {
                    '\\' => current.push('\\'),
                    'n' => current.push('\n'),
                    '$' => current.push('$'),
                    _ => {
                        let span = Span::new(
                            current_start..span.start() + char_pos + char.len_utf8(),
                            span.source(),
                        );
                        return Err(invalid_escape(span, char));
                    }
                }
            }
        }
    }
    if segments.is_empty() {
        stream.lexer.set_offset(lexer_offset);
        return Ok(ExprKind::Lit(Lit::Str(current.into())).with_span(outer_span));
    }
    if !current.is_empty() {
        let current_span = Span::from_start_len(current_start, raw.len(), stream.lexer.source());
        let expr = ExprKind::Lit(Lit::Str(current.into())).with_span(current_span);
        segments.push(stream.ast.exprs.push(expr));
    }
    stream.lexer.set_offset(lexer_offset);
    Ok(ExprKind::Lit(Lit::FStr(segments)).with_span(outer_span))
}

fn invalid_escape(span: Span, char: char) -> Error {
    errors::error(
        &format!("invalid escape character {char:?}"),
        [(span, "invalid escape character")],
    )
}

impl Parse for Ident {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let span = stream.expect(TokenKind::Ident)?.span;
        Ok(Self { symbol: Symbol::from(&stream.lexer.src()[span]), span })
    }
}

impl ItemKind {
    pub fn with_span(self, span: Span) -> Item {
        Item { kind: self, span }
    }
}

impl Parse for Item {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let tok = stream.next();
        let kind = match tok.kind {
            TokenKind::Module => {
                let ident = stream.parse()?;
                stream.expect(TokenKind::LBrace)?;
                let module = stream.parse_items(TokenKind::RBrace)?;
                ItemKind::Module(ident, Module { items: module })
            }
            TokenKind::Fn => ItemKind::FnDecl(stream.parse()?),
            TokenKind::Struct => parse_struct(stream)?,
            TokenKind::Impl => ItemKind::Impl(stream.parse()?),
            TokenKind::Trait => ItemKind::Trait(stream.parse()?),
            TokenKind::Const => parse_const(stream)?,
            _ => {
                return Err(errors::error(
                    &format!("expected item, found `{}`", tok.kind.repr()),
                    [(tok.span, "expected item")],
                ));
            }
        };
        Ok(kind.with_span(tok.span.with_end(stream.lexer.current_pos())))
    }
}

impl Parse for ItemId {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let item = stream.parse()?;
        Ok(stream.ast.items.push(item))
    }
}

impl Parse for Stmt {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let token = stream.peek();
        match token.kind {
            TokenKind::Fn
            | TokenKind::Struct
            | TokenKind::Const
            | TokenKind::Impl
            | TokenKind::Trait => stream.parse().map(Stmt::Item),
            _ => stream.parse().map(Stmt::Expr),
        }
    }
}
