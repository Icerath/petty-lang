use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TokenKind {
    // Symbols
    DotDot,
    DotDotEq,

    Dot,
    Comma,
    Semicolon,
    Colon,
    ThinArrow,

    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LParen,
    RParen,

    Plus,
    Minus,
    Star,
    Slash,
    Percent,

    PlusEq,
    MinusEq,
    MulEq,
    DivEq,
    ModEq,

    EqEq,
    Neq,
    GreaterEq,
    LessEq,

    Eq,
    Not,
    Greater,
    Less,
    // Literals
    Char,
    Int,
    Str,
    Ident,
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}

impl TokenKind {
    pub const fn repr(self) -> &'static str {
        match self {
            Self::Char => "character",
            Self::Colon => ":",
            Self::Comma => ",",
            Self::DivEq => "/=",
            Self::Dot => ".",
            Self::DotDot => "..",
            Self::DotDotEq => "..=",
            Self::Eq => "=",
            Self::EqEq => "==",
            Self::Greater => ">",
            Self::GreaterEq => ">=",
            Self::Ident => "identifier",
            Self::Int => "integer",
            Self::LBrace => "{",
            Self::LBracket => "[",
            Self::Less => "<",
            Self::LessEq => "<=",
            Self::LParen => "(",
            Self::Minus => "-",
            Self::MinusEq => "-=",
            Self::ModEq => "%=",
            Self::MulEq => "*=",
            Self::Neq => "!=",
            Self::Not => "!",
            Self::Percent => "%",
            Self::Plus => "+",
            Self::PlusEq => "+=",
            Self::RBrace => "}",
            Self::RBracket => "]",
            Self::RParen => ")",
            Self::Semicolon => ";",
            Self::Slash => "/",
            Self::Star => "*",
            Self::Str => "string",
            Self::ThinArrow => "->",
        }
    }
}
