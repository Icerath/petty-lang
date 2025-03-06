mod parse;
mod span;

fn main() {
    let src = include_str!("../examples/brainfuck.pebble");

    macro_rules! try_miette {
        ($expr: expr) => {
            match $expr {
                Ok(ok) => ok,
                Err(err) => {
                    eprintln!("{err:?}");
                    return;
                }
            }
        };
    }

    let ast = try_miette!(parse::parse(src));
    println!("{ast:#?}");
}
