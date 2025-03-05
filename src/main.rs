mod parse;
mod span;

fn main() {
    let src = include_str!("../examples/brainfuck.pebble");
    for token in parse::tokenize(src) {
        println!("{:?}({})", token.kind, &src[token.span]);
    }
}
