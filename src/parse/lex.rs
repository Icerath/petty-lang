use std::{io, path::Path, str::Chars};

use super::token::{Token, TokenKind};
use crate::{
    source::{Source, SourceId},
    span::Span,
};

#[derive(Clone)]
pub struct Lexer<'src> {
    src: &'src str,
    chars: Chars<'src>,
    token_start: usize,
    source_list: Vec<SourceId>,
}

impl<'src> Lexer<'src> {
    pub fn new_root(src: &'src str, path: &Path) -> io::Result<Self> {
        let source = Source::with_global(|src| {
            let source = src.init(path)?;
            src.root = Some(source);
            Ok::<_, io::Error>(source)
        })?;
        Ok(Self { src, token_start: 0, chars: src.chars(), source_list: vec![source] })
    }
    pub fn new(path: &Path) -> io::Result<Self> {
        let source = Source::with_global(|src| src.init(path))?;
        // TODO: better source handling
        let src = source.contents().leak();
        Ok(Self { src, token_start: 0, chars: src.chars(), source_list: vec![source] })
    }
    #[cfg_attr(debug_assertions, track_caller)]
    pub fn bump(&mut self, bytes: usize) {
        self.chars = self.chars.as_str()[bytes..].chars();
    }
    pub fn offset(&self) -> usize {
        self.src.len() - self.chars.as_str().len()
    }
    pub fn set_offset(&mut self, bytes: usize) {
        self.chars = self.src[bytes..].chars();
    }
    pub const fn src(&self) -> &'src str {
        self.src
    }
    pub fn current_pos(&self) -> usize {
        self.src.len() - self.chars.as_str().len()
    }
    pub fn span(&self) -> Span {
        Span::new(self.token_start()..self.current_pos(), self.source())
    }
    pub fn token_start(&self) -> usize {
        self.token_start as _
    }

    fn try_next(&mut self, expected: char) -> bool {
        match self.chars.clone().next() {
            Some(c) if c == expected => {
                _ = self.chars.next();
                true
            }
            _ => false,
        }
    }
}

impl Lexer<'_> {
    pub fn source(&self) -> SourceId {
        *self.source_list.last().unwrap()
    }
    pub fn next(&mut self) -> Token {
        let char = loop {
            let Some(next) = self.chars.next() else {
                return Token {
                    span: Span::new(self.current_pos()..self.current_pos(), self.source()),
                    kind: TokenKind::Eof,
                };
            };
            match next {
                char if char.is_whitespace() => self.whitespace(),
                '/' if self.chars.clone().next() == Some('/') => self.line_comment(),
                '/' if self.chars.clone().next() == Some('*') => self.block_comment(),
                char => break char,
            }
        };
        self.token_start = self.current_pos() - char.len_utf8();
        let kind = match char {
            // Longer Symbols
            '.' if self.try_next('.') => {
                if self.try_next('=') {
                    TokenKind::DotDotEq
                } else {
                    TokenKind::DotDot
                }
            }
            '=' if self.try_next('>') => TokenKind::FatArrow,
            '-' if self.try_next('>') => TokenKind::ThinArrow,
            '+' if self.try_next('=') => TokenKind::PlusEq,
            '-' if self.try_next('=') => TokenKind::MinusEq,
            '*' if self.try_next('=') => TokenKind::MulEq,
            '/' if self.try_next('=') => TokenKind::DivEq,
            '%' if self.try_next('=') => TokenKind::ModEq,
            '=' if self.try_next('=') => TokenKind::EqEq,
            '!' if self.try_next('=') => TokenKind::Neq,
            '>' if self.try_next('=') => TokenKind::GreaterEq,
            '<' if self.try_next('=') => TokenKind::LessEq,
            ':' if self.try_next(':') => TokenKind::PathSep,
            // Symbols
            '&' => TokenKind::Ampersand,

            '.' => TokenKind::Dot,
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semicolon,
            ':' => TokenKind::Colon,

            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,

            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,
            '*' => TokenKind::Star,
            '/' => TokenKind::Slash,
            '%' => TokenKind::Percent,

            '=' => TokenKind::Eq,
            '!' => TokenKind::Not,
            '>' => TokenKind::Greater,
            '<' => TokenKind::Less,

            '\'' => self.char(),
            '"' => self.str(),
            '0'..='9' => self.int(),
            'a'..='z' | 'A'..='Z' | '_' => self.ident(self.token_start),
            _ => TokenKind::Unknown,
        };
        Token { span: Span::new(self.token_start..self.current_pos(), self.source()), kind }
    }
}

impl Lexer<'_> {
    fn line_comment(&mut self) {
        self.chars.next();
        (&mut self.chars).take_while(|&c| c != '\n').count();
    }
    fn whitespace(&mut self) {
        while (self.chars.clone().next()).is_some_and(char::is_whitespace) {
            self.chars.next();
        }
    }
    fn block_comment(&mut self) {
        _ = self.chars.next();
        let Some(end) = self.chars.as_str().find("*/") else { return };
        self.chars = self.chars.as_str()[end + 2..].chars();
    }
    fn char(&mut self) -> TokenKind {
        if self.chars.next().is_some_and(|c| c == '\\') {
            self.chars.next();
        }
        self.chars.next();
        TokenKind::Char
    }
    fn str(&mut self) -> TokenKind {
        while let Some(next) = self.chars.next() {
            if next == '"' {
                break;
            }
            if next == '$' && self.chars.clone().next().is_some_and(|c| c == '{') {
                let mut d = 0;
                for next in self.chars.by_ref() {
                    match next {
                        '{' => d += 1,
                        '}' => d -= 1,
                        _ => {}
                    }
                    if d == 0 {
                        break;
                    }
                }
            }
            if next == '\\' && self.chars.next().is_some_and(|c| c == '\'') {
                self.chars.next();
            }
        }
        TokenKind::Str
    }
    fn int(&mut self) -> TokenKind {
        while (self.chars.clone().next()).is_some_and(|c| c.is_numeric() || c == '_') {
            self.chars.next();
        }
        TokenKind::Int
    }
    fn ident(&mut self, span_start: usize) -> TokenKind {
        let is_ident_char = |c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9');
        while (self.chars.clone().next()).is_some_and(is_ident_char) {
            self.chars.next();
        }
        let span = Span::new(span_start..self.current_pos(), self.source());
        ident_kind(&self.src()[span])
    }
}

fn ident_kind(str: &str) -> TokenKind {
    match str {
        "and" => TokenKind::And,
        "or" => TokenKind::Or,
        "trait" => TokenKind::Trait,
        "impl" => TokenKind::Impl,
        "unreachable" => TokenKind::Unreachable,
        "in" => TokenKind::In,
        "is" => TokenKind::Is,
        "for" => TokenKind::For,
        "assert" => TokenKind::Assert,
        "break" => TokenKind::Break,
        "continue" => TokenKind::Continue,
        "else" => TokenKind::Else,
        "false" => TokenKind::False,
        "fn" => TokenKind::Fn,
        "if" => TokenKind::If,
        "let" => TokenKind::Let,
        "const" => TokenKind::Const,
        "return" => TokenKind::Return,
        "struct" => TokenKind::Struct,
        "true" => TokenKind::True,
        "while" => TokenKind::While,
        "match" => TokenKind::Match,
        "mod" => TokenKind::Module,
        _ => TokenKind::Ident,
    }
}
