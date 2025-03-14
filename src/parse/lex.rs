use miette::Result;
use std::str::Chars;

use crate::span::Span;

use super::token::{Token, TokenKind};

#[derive(Clone)]
pub struct Lexer<'src> {
    src: &'src str,
    chars: Chars<'src>,
    prev_end: u32,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str) -> Self {
        Self { src, prev_end: 0, chars: src.chars() }
    }
    pub fn current_pos(&self) -> u32 {
        (self.src.len() - self.chars.as_str().len()) as u32
    }
    pub const fn src(&self) -> &'src str {
        self.src
    }
    pub fn span_eof(&self) -> Span {
        Span::from(self.current_pos()..self.src.len() as u32)
    }
    pub fn span(&self) -> Span {
        Span::from(self.prev_end..self.current_pos())
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<Token>;

    #[allow(clippy::too_many_lines)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut span_start;
        let mut char;

        let kind = loop {
            span_start = self.current_pos();
            char = self.chars.next()?;
            let kind = match char {
                // Ignore
                _ if char.is_whitespace() => {
                    self.whitespace();
                    continue;
                }
                '/' if self.chars.clone().next() == Some('/') => {
                    self.line_comment();
                    continue;
                }

                // Longer Symbols
                '-' if self.chars.clone().next() == Some('>') => {
                    self.chars.next();
                    TokenKind::ThinArrow
                }
                '.' if self.chars.clone().next() == Some('.') => {
                    self.chars.next();
                    if self.chars.clone().next() == Some('=') {
                        self.chars.next();
                        TokenKind::DotDotEq
                    } else {
                        TokenKind::DotDot
                    }
                }
                '.' if self.chars.clone().next() == Some('.') => {
                    self.chars.next();
                    TokenKind::DotDot
                }

                '+' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::PlusEq
                }
                '-' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::MinusEq
                }
                '*' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::MulEq
                }
                '/' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::DivEq
                }
                '%' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::ModEq
                }

                '=' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::EqEq
                }

                '!' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::Neq
                }
                '>' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::GreaterEq
                }
                '<' if self.chars.clone().next() == Some('=') => {
                    self.chars.next();
                    TokenKind::LessEq
                }

                // Symbols
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
                'a'..='z' | 'A'..='Z' | '_' => self.ident(span_start),
                _ => {
                    let span = miette::LabeledSpan::at(
                        span_start as usize..self.current_pos() as usize,
                        "here",
                    );

                    return Some(Err(miette::miette!(
                        labels = vec![span],
                        "Unexpected character '{char}'"
                    )
                    .with_source_code(self.src.to_string())));
                }
            };
            self.prev_end = span_start;
            break kind;
        };
        Some(Ok(Token { span: Span::from(span_start..self.current_pos()), kind }))
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
    fn ident(&mut self, span_start: u32) -> TokenKind {
        while (self.chars.clone().next()).is_some_and(|c| c.is_ascii_alphabetic() || c == '_') {
            self.chars.next();
        }
        let span = Span::from(span_start..self.current_pos());
        ident_kind(&self.src()[span])
    }
}

fn ident_kind(str: &str) -> TokenKind {
    match str {
        "true" => TokenKind::True,
        "false" => TokenKind::False,
        "abort" => TokenKind::Abort,
        "let" => TokenKind::Let,
        "while" => TokenKind::While,
        "if" => TokenKind::If,
        "else" => TokenKind::Else,
        "fn" => TokenKind::Fn,
        "return" => TokenKind::Return,
        "break" => TokenKind::Break,
        _ => TokenKind::Ident,
    }
}
