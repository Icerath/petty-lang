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
    FatArrow,
    Ampersand,

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
    // Keywords
    And,
    Or,
    Assert,
    Continue,
    Break,
    Else,
    False,
    Fn,
    If,
    Is,
    Let,
    Const,
    Return,
    Struct,
    True,
    While,
    For,
    In,
    Match,
    Unreachable,
    Trait,
    Impl,
    // Literals
    Char,
    Int,
    Str,
    Ident,

    Unknown,
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}

impl TokenKind {
    pub const fn repr(self) -> &'static str {
        match self {
            Self::And => "and",
            Self::Or => "or",
            Self::Trait => "trait",
            Self::Impl => "impl",
            Self::Ampersand => "&",
            Self::Unreachable => "unreachable",
            Self::Assert => "assert",
            Self::Break => "break",
            Self::Continue => "continue",
            Self::Let => "let",
            Self::Const => "const",
            Self::While => "while",
            Self::For => "for",
            Self::In => "in",
            Self::Is => "is",
            Self::True => "true",
            Self::False => "false",
            Self::If => "if",
            Self::Else => "else",
            Self::Return => "return",
            Self::Fn => "fn",
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
            Self::FatArrow => "=>",
            Self::Struct => "struct",
            Self::Match => "match",
            Self::Unknown => "unknown",
        }
    }
}

impl TokenKind {
    // returns true if this token can never start an expression
    pub fn is_terminator(self) -> bool {
        matches!(
            self,
            Self::Semicolon
                | Self::Comma
                | Self::Colon
                | Self::RParen
                | Self::RBrace
                | Self::RBracket
        )
    }
}
