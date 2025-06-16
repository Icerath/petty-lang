mod expr;
mod lex;
mod token;

use lex::Lexer;
use miette::{Error, IntoDiagnostic, Result};
use thin_vec::{ThinVec, thin_vec};
use token::Token;

use crate::{
    ast::{
        self, ArraySeg, Ast, BinOpKind, Block, BlockId, Expr, ExprId, ExprKind, Field, FnDecl,
        Ident, IfStmt, Impl, Inclusive, Item, ItemId, ItemKind, Lit, MatchArm, Module, Param, Pat,
        PatArg, PatKind, Path, Stmt, Trait, Ty, TyKind, TypeId, Use, UseKind,
    },
    errors,
    source::Source,
    span::Span,
    symbol::Symbol,
};

pub fn parse(src: &str, path: &std::path::Path) -> Result<Ast> {
    let lexer = Lexer::new_root(src, path).into_diagnostic()?;
    let mut ast = Ast::default();
    let mut stream = Stream { lexer, ast: &mut ast };
    ast.root.items = stream.parse_items(Token::Eof)?;
    Ok(ast)
}

struct Stream<'src> {
    lexer: Lexer<'src>,
    ast: &'src mut Ast,
}

impl<'src> Stream<'src> {
    fn new_lexer(&self, ident: Span) -> Result<Lexer<'src>> {
        let file_name = &self.lexer.src()[ident];
        let path = self.lexer.source().path().with_file_name(file_name).with_extension("pty");

        let Ok(source) = Source::with_global(|src| src.init(&path)) else {
            return Err(errors::error(
                &format!("failed to read module {}", path.display()),
                [(ident, format!("failed to read module {}", path.display()))],
            ));
        };
        let src = source.contents().leak();
        Ok(Lexer::new(src, source))
    }

    fn ident(&self, span: Span) -> Ident {
        Ident { span, symbol: self.symbol(span) }
    }
    fn symbol(&self, span: Span) -> Symbol {
        self.lexer.src()[span].into()
    }

    fn parse_items(&mut self, terminator: Token) -> Result<Vec<ItemId>> {
        let mut items = vec![];
        loop {
            match self.peek() {
                kind if kind == terminator => break,
                Token::Semicolon => _ = self.lexer.next(),
                _ => items.push(self.parse()?),
            }
        }
        _ = self.next();
        Ok(items)
    }

    fn next(&mut self) -> Token {
        self.lexer.next()
    }
    fn peek(&mut self) -> Token {
        self.lexer.clone().next()
    }
    fn expect(&mut self, expected: Token) -> Result<()> {
        let token = self.next();
        if token != expected {
            return Err(errors::error(
                &format!("expected `{}`, found: `{}`", expected.repr(), token.repr()),
                [(self.lexer.span(), format!("expected `{}`", expected.repr()))],
            ));
        }
        Ok(())
    }
    fn any(&mut self, toks: &[Token]) -> Result<Token> {
        let token = self.next();
        if toks.contains(&token) {
            return Ok(token);
        }
        Err(self.any_failed(token, toks))
    }
    #[inline(never)]
    #[cold]
    fn any_failed(&self, found: Token, toks: &[Token]) -> Error {
        let toks =
            toks.iter().map(|kind| format!("`{}`", kind.repr())).collect::<Vec<_>>().join(" or ");
        errors::error(
            &format!("expected one of {toks}, found `{}`", found.repr()),
            [(self.lexer.span(), format!("expected one of '{toks}'"))],
        )
    }

    fn parse<T: Parse>(&mut self) -> Result<T> {
        T::parse(self)
    }
    fn parse_separated<T: Parse>(&mut self, sep: Token, term: Token) -> Result<ThinVec<T>> {
        let mut args = thin_vec![];
        loop {
            if self.peek() == term {
                _ = self.next();
                break;
            }
            let expr = self.parse()?;
            args.push(expr);
            match self.next() {
                tok if tok == term => break,
                tok if tok == sep => {}
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
        stream.expect(Token::Ident)?;
        Ok(stream.symbol(stream.lexer.span()))
    }
}

impl Parse for Block {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let start = stream.lexer.span();
        let mut stmts: ThinVec<Stmt> = thin_vec![];
        let mut is_expr = false;

        loop {
            match stream.peek() {
                Token::RBrace => {
                    _ = stream.next();
                    break;
                }
                Token::Semicolon => {
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

        let span = start.with_end(stream.lexer.current_pos());
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
        let token = stream.next();
        let start = stream.lexer.span();
        let kind = match token {
            Token::Fn => {
                stream.expect(Token::LParen)?;
                let params = stream.parse_separated(Token::Comma, Token::RParen)?;
                let ret = if stream.peek() == Token::ThinArrow {
                    _ = stream.next();
                    Some(stream.parse()?)
                } else {
                    None
                };
                TyKind::Func { params, ret }
            }
            Token::Not => TyKind::Never,
            Token::Ident => {
                let path = parse_path(stream, start)?;
                let generics = if stream.peek() == Token::Less {
                    _ = stream.next();
                    stream.parse_separated(Token::Comma, Token::Greater)?
                } else {
                    ThinVec::new()
                };
                TyKind::Name { path, generics }
            }
            Token::LBracket => {
                let of = stream.parse()?;
                stream.expect(Token::RBracket)?;
                TyKind::Array(of)
            }
            Token::LParen => {
                if stream.peek() == Token::RParen {
                    _ = stream.next();
                    TyKind::Unit
                } else {
                    let ty = stream.parse();
                    stream.next();
                    return ty;
                }
            }
            Token::Ampersand => TyKind::Ref(stream.parse()?),
            other => {
                return Err(errors::error(
                    &format!("expected type, found '{}'", other.repr()),
                    [(stream.lexer.span(), "expected type")],
                ));
            }
        };
        Ok(Self { kind, span: start.with_end(stream.lexer.current_pos()) })
    }
}

impl Parse for Impl {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let start = stream.lexer.span(); // FIXME: include impl tok
        let generics = if stream.peek() == Token::Less {
            _ = stream.next();
            stream.parse_separated(Token::Comma, Token::Greater)?
        } else {
            ThinVec::new()
        };
        let ty = stream.parse()?;
        stream.expect(Token::LBrace)?;
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
        stream.expect(Token::LBrace)?;
        let methods = parse_trait_methods(stream)?;
        Ok(Self { ident, methods })
    }
}

fn parse_trait_methods(stream: &mut Stream) -> Result<ThinVec<FnDecl>> {
    let mut methods = ThinVec::new();

    loop {
        let next = stream.any(&[Token::Fn, Token::RBrace])?;
        match next {
            Token::Fn => methods.push(stream.parse()?),
            Token::RBrace => break Ok(methods),
            _ => unreachable!(),
        }
    }
}

impl Parse for FnDecl {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.parse()?;
        let generics = parse_generics(stream)?;
        let params = stream.parse_separated(Token::Comma, Token::RParen)?;

        let mut chosen = stream.any(&[Token::LBrace, Token::ThinArrow, Token::Semicolon])?;
        let mut ret = None;
        if chosen == Token::ThinArrow {
            ret = Some(stream.parse()?);
            chosen = stream.any(&[Token::Semicolon, Token::LBrace])?;
        }
        let block = if chosen == Token::Semicolon { None } else { Some(stream.parse()?) };
        Ok(Self { ident, generics, params, ret, block })
    }
}

/// Parses generics followed by a '('
fn parse_generics(stream: &mut Stream<'_>) -> Result<ThinVec<Ident>, Error> {
    let generics = if stream.any(&[Token::Less, Token::LParen])? == Token::Less {
        let generics = stream.parse_separated(Token::Comma, Token::Greater)?;
        stream.expect(Token::LParen)?;
        generics
    } else {
        ThinVec::new()
    };
    Ok(generics)
}

fn parse_struct(stream: &mut Stream) -> Result<ItemKind> {
    let ident = stream.parse()?;
    let generics = parse_generics(stream)?;
    let fields = stream.parse_separated(Token::Comma, Token::RParen)?;

    Ok(ItemKind::Struct(ident, generics, fields))
}

fn parse_const(stream: &mut Stream) -> Result<ItemKind> {
    let (ident, ty, expr) = parse_var(stream)?;
    Ok(ItemKind::Const(ident, ty, expr))
}

fn parse_let(stream: &mut Stream) -> Result<Expr> {
    let let_span = stream.lexer.span();
    let (ident, ty, expr) = parse_var(stream)?;
    Ok((ExprKind::Let { ident, ty, expr }).with_span(let_span.with_end(stream.lexer.current_pos())))
}

fn parse_var(stream: &mut Stream) -> Result<(Ident, Option<TypeId>, ExprId)> {
    let ident = stream.parse()?;
    let mut ty = None;
    if stream.any(&[Token::Colon, Token::Eq])? == Token::Colon {
        ty = Some(stream.parse()?);
        stream.expect(Token::Eq)?;
    }
    let expr = stream.parse()?;
    Ok((ident, ty, expr))
}

fn parse_while(stream: &mut Stream) -> Result<Expr> {
    let condition = stream.parse()?;
    stream.expect(Token::LBrace)?;
    let block = stream.parse()?;
    Ok((ExprKind::While { condition, block }).todo_span())
}

fn parse_for(stream: &mut Stream) -> Result<Expr> {
    let ident = stream.parse()?;
    stream.expect(Token::In)?;
    let iter = stream.parse()?;
    stream.expect(Token::LBrace)?;
    let body = stream.parse()?;
    Ok((ExprKind::For { ident, iter, body }).todo_span())
}

fn parse_match(stream: &mut Stream) -> Result<Expr> {
    let kw_span = stream.lexer.span();
    let scrutinee = stream.parse()?;
    stream.expect(Token::LBrace)?;
    let arms = stream.parse_separated(Token::Comma, Token::RBrace)?;
    let end = stream.lexer.current_pos();
    Ok((ExprKind::Match { scrutinee, arms }).with_span(kw_span.with_end(end)))
}

fn parse_ifchain(stream: &mut Stream) -> Result<Expr> {
    let start = stream.lexer.span();
    let mut arms = thin_vec![];
    let els = loop {
        let condition = stream.parse()?;
        stream.expect(Token::LBrace)?;
        let body = stream.parse()?;
        arms.push(IfStmt { condition, body });
        if stream.peek() != Token::Else {
            break None;
        }
        _ = stream.next();
        match stream.any(&[Token::If, Token::LBrace])? {
            Token::If => {}
            Token::LBrace => break Some(stream.parse()?),
            _ => unreachable!(),
        }
    };
    let span = start.with_end(stream.lexer.current_pos());
    Ok((ExprKind::If { arms, els }).with_span(span))
}

impl Parse for ArraySeg {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let expr = stream.parse()?;
        let repeated = if stream.peek() == Token::Semicolon {
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
        stream.expect(Token::Colon)?;
        let pat = stream.parse()?;
        Ok(Self { ident, pat })
    }
}

impl Parse for Pat {
    fn parse(stream: &mut Stream) -> Result<Self> {
        fn parse_single(stream: &mut Stream) -> Result<Pat> {
            let tok = stream.next();
            let tok_span = stream.lexer.span();
            let kind = match tok {
                Token::Ident if stream.peek() == Token::LParen => {
                    _ = stream.next();
                    let ident = stream.ident(tok_span);
                    let args = stream.parse_separated(Token::Comma, Token::RParen)?;
                    PatKind::Struct(ident, args)
                }
                Token::Ident => PatKind::Ident(stream.symbol(tok_span)),
                Token::True => PatKind::Bool(true),
                Token::False => PatKind::Bool(false),
                Token::Str => PatKind::Str(stream.symbol(tok_span.shrink(1))),
                Token::Int => PatKind::Int(stream.lexer.src()[tok_span].parse::<i64>().unwrap()),
                Token::LBrace => {
                    let block: BlockId = stream.parse()?;
                    PatKind::Expr(block)
                }
                Token::LBracket => {
                    PatKind::Array(stream.parse_separated(Token::Comma, Token::RBracket)?)
                }
                Token::If => PatKind::If(stream.parse()?),
                Token::LParen => {
                    let pat = stream.parse()?;
                    stream.expect(Token::RParen)?;
                    return Ok(pat);
                }
                _ => {
                    return Err(errors::error(
                        &format!("expected pattern, found '{}'", tok.repr()),
                        [(stream.lexer.span(), "expected pattern")],
                    ));
                }
            };
            let span = tok_span.with_end(stream.lexer.current_pos());
            Ok(Pat { kind, span })
        }
        fn parse_range(stream: &mut Stream) -> Result<Pat> {
            let lhs = parse_single(stream)?;
            match stream.peek() {
                kind @ (Token::DotDot | Token::DotDotEq) => {
                    let inclusive = match kind {
                        Token::DotDotEq => Inclusive::Yes,
                        _ => Inclusive::No,
                    };
                    _ = stream.next();
                    let rhs = parse_single(stream)?;
                    let span = lhs.span.with_end(stream.lexer.current_pos());
                    let kind = PatKind::Range(Box::new([Some(lhs), Some(rhs)]), inclusive);
                    Ok(Pat { kind, span })
                }
                _ => Ok(lhs),
            }
        }
        let mut single = parse_range(stream)?;
        let single_span = single.span;
        loop {
            match stream.peek() {
                op @ (Token::Or | Token::And) => {
                    let mut patterns = thin_vec![single];
                    while stream.peek() == op {
                        _ = stream.next();
                        patterns.push(parse_range(stream)?);
                    }
                    let span = single_span.with_end(stream.lexer.current_pos());
                    let kind = if op == Token::Or {
                        PatKind::Or(patterns)
                    } else {
                        PatKind::And(patterns)
                    };
                    single = Pat { kind, span };
                }
                _ => break Ok(single),
            }
        }
    }
}

impl Parse for MatchArm {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let pat = stream.parse()?;
        stream.expect(Token::FatArrow)?;
        let body = stream.parse()?;
        Ok(Self { pat, body })
    }
}

impl Parse for Param {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.parse()?;

        let mut ty = None;
        if stream.peek() == Token::Colon {
            _ = stream.next();
            ty = Some(stream.parse()?);
        }
        Ok(Self { ident, ty })
    }
}

impl Parse for Field {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident = stream.parse()?;
        stream.expect(Token::Colon)?;
        let ty = stream.parse()?;
        Ok(Self { ident, ty })
    }
}

impl Parse for Use {
    fn parse(stream: &mut Stream) -> Result<Self> {
        let ident: Ident = stream.parse()?;
        let mut path = ast::Path::new_single(ident);

        let kind = loop {
            match stream.peek() {
                Token::PathSep => _ = stream.next(),
                _ => break None,
            }
            let next = stream.next();
            let next_span = stream.lexer.span();
            match next {
                Token::LBrace => {
                    let many = stream.parse_separated(Token::Comma, Token::RBrace)?;
                    break Some(UseKind::Block(many));
                }
                Token::Ident => path.segments.push(stream.ident(next_span)),
                Token::Star => {
                    break Some(UseKind::Wildcard);
                }
                _ => todo!("{:?}", next),
            }
        };
        Ok(Use { path, kind })
    }
}

impl TryFrom<Token> for BinOpKind {
    type Error = ();
    fn try_from(kind: Token) -> Result<Self, Self::Error> {
        Ok(match kind {
            Token::Eq => Self::Assign,
            Token::PlusEq => Self::AddAssign,
            Token::MinusEq => Self::SubAssign,
            Token::MulEq => Self::MulAssign,
            Token::DivEq => Self::DivAssign,
            Token::ModEq => Self::ModAssign,

            Token::Plus => Self::Add,
            Token::Minus => Self::Sub,
            Token::Star => Self::Mul,
            Token::Slash => Self::Div,
            Token::Percent => Self::Mod,

            Token::EqEq => Self::Eq,
            Token::Neq => Self::Neq,
            Token::Greater => Self::Greater,
            Token::Less => Self::Less,
            Token::GreaterEq => Self::GreaterEq,
            Token::LessEq => Self::LessEq,

            Token::DotDot => Self::Range,
            Token::DotDotEq => Self::RangeInclusive,

            Token::And => Self::And,
            Token::Or => Self::Or,
            _ => return Err(()),
        })
    }
}

fn parse_atom_with(stream: &mut Stream, tok: Token) -> Result<ExprId> {
    let start = stream.lexer.span();
    macro_rules! lit {
        ($lit: expr, $span: expr) => {
            Ok(ExprKind::Lit($lit).with_span($span))
        };
        ($lit: expr) => {
            Ok(ExprKind::Lit($lit).with_span(start))
        };
    }

    let expr =
        match tok {
            Token::Unreachable => Ok(ExprKind::Unreachable.with_span(start)),
            Token::LParen => {
                return Ok(if stream.peek() == Token::RParen {
                    _ = stream.next();
                    stream.ast.exprs.push(ExprKind::Lit(Lit::Unit).todo_span())
                } else {
                    let expr = stream.parse()?;
                    stream.expect(Token::RParen)?;
                    expr
                });
            }
            Token::LBracket => Ok(ExprKind::Lit(Lit::Array {
                segments: stream.parse_separated(Token::Comma, Token::RBracket)?,
            })
            .with_span(start.with_end(stream.lexer.current_pos()))),
            Token::LBrace => Ok(ExprKind::Block(stream.parse()?)
                .with_span(start.with_end(stream.lexer.current_pos()))),
            Token::Break => Ok(ExprKind::Break.with_span(start)),
            Token::Continue => Ok(ExprKind::Continue.with_span(start)),
            Token::Assert => {
                let expr: ExprId = stream.parse()?;
                Ok(ExprKind::Assert(expr).with_span(stream.ast.exprs[expr].span))
            }
            Token::Return => {
                if stream.peek().is_terminator() {
                    Ok(ExprKind::Return(None).with_span(start))
                } else {
                    let expr = stream.parse()?;
                    let span = start.with_end((&stream.ast.exprs[expr] as &Expr).span.end());
                    Ok(ExprKind::Return(Some(expr)).with_span(span))
                }
            }
            Token::Let => parse_let(stream),
            Token::While => parse_while(stream),
            Token::For => parse_for(stream),
            Token::Match => parse_match(stream),
            Token::If => parse_ifchain(stream),
            Token::True => lit!(Lit::Bool(true)),
            Token::False => lit!(Lit::Bool(false)),
            Token::Int => lit!(Lit::Int(stream.lexer.src()[start].parse::<i64>().unwrap())),
            Token::Str => parse_string(stream, start),
            Token::Char => {
                // TODO: Escaping
                let str = &stream.lexer.src()[start.shrink(1)];
                lit!(Lit::Char(str.chars().next().unwrap()))
            }
            Token::Ident => {
                let path = parse_path(stream, start)?;
                let span = start.with_end(stream.lexer.current_pos());
                Ok(ExprKind::Path(path).with_span(span))
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

fn parse_path(stream: &mut Stream, ident_span: Span) -> Result<Path> {
    let ident = stream.ident(ident_span);
    let mut path = ast::Path::new_single(ident);
    while stream.peek() == Token::PathSep {
        _ = stream.next();
        let next = stream.parse()?;
        path.segments.push(next);
    }
    Ok(path)
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
        stream.expect(Token::Ident)?;
        let span = stream.lexer.span();
        Ok(stream.ident(span))
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
        let tok_span = stream.lexer.span();
        let kind = match tok {
            Token::Use => ItemKind::Use(stream.parse()?),
            Token::Module => {
                let ident = stream.parse()?;
                let next = stream.any(&[Token::LBrace, Token::Semicolon])?;
                match next {
                    Token::LBrace => {
                        let module = stream.parse_items(Token::RBrace)?;
                        ItemKind::Module(ident, Module { items: module })
                    }
                    Token::Semicolon => {
                        let lexer = stream.new_lexer(ident.span)?;
                        let lexer = std::mem::replace(&mut stream.lexer, lexer);
                        let items = stream.parse_items(Token::Eof)?;
                        stream.lexer = lexer;
                        ItemKind::Module(ident, Module { items })
                    }
                    _ => unreachable!(),
                }
            }
            Token::Fn => ItemKind::FnDecl(stream.parse()?),
            Token::Struct => parse_struct(stream)?,
            Token::Impl => ItemKind::Impl(stream.parse()?),
            Token::Trait => ItemKind::Trait(stream.parse()?),
            Token::Const => parse_const(stream)?,
            _ => {
                return Err(errors::error(
                    &format!("expected item, found `{}`", tok.repr()),
                    [(tok_span, "expected item")],
                ));
            }
        };
        Ok(kind.with_span(tok_span.with_end(stream.lexer.current_pos())))
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
        match stream.peek() {
            Token::Fn | Token::Struct | Token::Const | Token::Impl | Token::Trait | Token::Use => {
                stream.parse().map(Stmt::Item)
            }
            _ => stream.parse().map(Stmt::Expr),
        }
    }
}
