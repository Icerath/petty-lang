use crate::span::Span;

#[derive(Debug)]
pub enum TokenKind {
    // Symbols
    Dot,
    Comma,
    Semicolon,
    Colon,

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

#[derive(Debug)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}
