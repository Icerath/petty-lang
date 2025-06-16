use std::str::Chars;

use super::token::Token;
use crate::{source::SourceId, span::Span};

#[derive(Clone)]
pub struct Lexer<'src> {
    src: &'src str,
    chars: Chars<'src>,
    token_start: usize,
    source: SourceId,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str, source: SourceId) -> Self {
        Self { src, token_start: 0, chars: src.chars(), source }
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
        self.token_start
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
        self.source
    }
    pub fn next(&mut self) -> Token {
        let char = loop {
            let Some(next) = self.chars.next() else {
                return Token::Eof;
            };
            match next {
                char if char.is_whitespace() => self.whitespace(),
                '/' if self.chars.clone().next() == Some('/') => self.line_comment(),
                '/' if self.chars.clone().next() == Some('*') => self.block_comment(),
                char => break char,
            }
        };
        self.token_start = self.current_pos() - char.len_utf8();
        match char {
            // Longer Symbols
            '.' if self.try_next('.') => {
                if self.try_next('=') {
                    Token::DotDotEq
                } else {
                    Token::DotDot
                }
            }
            '=' if self.try_next('>') => Token::FatArrow,
            '-' if self.try_next('>') => Token::ThinArrow,
            '+' if self.try_next('=') => Token::PlusEq,
            '-' if self.try_next('=') => Token::MinusEq,
            '*' if self.try_next('=') => Token::MulEq,
            '/' if self.try_next('=') => Token::DivEq,
            '%' if self.try_next('=') => Token::ModEq,
            '=' if self.try_next('=') => Token::EqEq,
            '!' if self.try_next('=') => Token::Neq,
            '>' if self.try_next('=') => Token::GreaterEq,
            '<' if self.try_next('=') => Token::LessEq,
            ':' if self.try_next(':') => Token::PathSep,
            // Symbols
            '&' => Token::Ampersand,

            '.' => Token::Dot,
            ',' => Token::Comma,
            ';' => Token::Semicolon,
            ':' => Token::Colon,

            '{' => Token::LBrace,
            '}' => Token::RBrace,
            '[' => Token::LBracket,
            ']' => Token::RBracket,
            '(' => Token::LParen,
            ')' => Token::RParen,

            '+' => Token::Plus,
            '-' => Token::Minus,
            '*' => Token::Star,
            '/' => Token::Slash,
            '%' => Token::Percent,

            '=' => Token::Eq,
            '!' => Token::Not,
            '>' => Token::Greater,
            '<' => Token::Less,

            '\'' => self.char(),
            '"' => self.str(),
            '0'..='9' => self.int(),
            'a'..='z' | 'A'..='Z' | '_' => self.ident(self.token_start),
            _ => Token::Unknown,
        }
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
    fn char(&mut self) -> Token {
        if self.chars.next().is_some_and(|c| c == '\\') {
            self.chars.next();
        }
        self.chars.next();
        Token::Char
    }
    fn str(&mut self) -> Token {
        while let Some(next) = self.chars.next() {
            if next == '"' {
                break;
            } else if next == '$' && self.chars.clone().next().is_some_and(|c| c == '{') {
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
            } else if next == '\\' {
                self.chars.next();
            }
        }
        Token::Str
    }
    fn int(&mut self) -> Token {
        while (self.chars.clone().next()).is_some_and(|c| c.is_numeric() || c == '_') {
            self.chars.next();
        }
        Token::Int
    }
    fn ident(&mut self, span_start: usize) -> Token {
        let is_ident_char = |c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9');
        while (self.chars.clone().next()).is_some_and(is_ident_char) {
            self.chars.next();
        }
        let span = Span::new(span_start..self.current_pos(), self.source());
        ident_kind(&self.src()[span])
    }
}

fn ident_kind(str: &str) -> Token {
    match str {
        "and" => Token::And,
        "or" => Token::Or,
        "trait" => Token::Trait,
        "impl" => Token::Impl,
        "unreachable" => Token::Unreachable,
        "in" => Token::In,
        "is" => Token::Is,
        "for" => Token::For,
        "assert" => Token::Assert,
        "break" => Token::Break,
        "continue" => Token::Continue,
        "else" => Token::Else,
        "false" => Token::False,
        "fn" => Token::Fn,
        "if" => Token::If,
        "let" => Token::Let,
        "const" => Token::Const,
        "return" => Token::Return,
        "struct" => Token::Struct,
        "true" => Token::True,
        "while" => Token::While,
        "match" => Token::Match,
        "mod" => Token::Module,
        "use" => Token::Use,
        _ => Token::Ident,
    }
}
