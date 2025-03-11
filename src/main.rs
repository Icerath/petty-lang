mod ast;
mod ast_analysis;
mod ast_lowering;
mod compile;
mod hir;
mod parse;
mod span;
mod symbol;
mod ty;

#[cfg(test)]
mod tests;

fn main() {
    match compile::compile(include_str!("../examples/brainfuck.pebble")) {
        Ok(()) => {}
        Err(err) => eprintln!("{err:?}"),
    }
}
