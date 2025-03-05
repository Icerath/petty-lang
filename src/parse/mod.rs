mod lex;
mod token;

use token::Token;

pub fn tokenize(src: &str) -> Vec<Token> {
    lex::Lexer::new(src).map(|x| x.unwrap()).collect()
}
