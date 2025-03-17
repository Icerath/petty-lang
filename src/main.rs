#[cfg(test)]
mod tests;

mod ast;
mod ast_analysis;
mod ast_lowering;
mod compile;
mod hir;
mod hir_lowering;
mod mir;
mod parse;
mod span;
mod symbol;
mod ty;

fn main() {
    match compile::compile(include_str!("../examples/brainfuck.pebble")) {
        Ok(()) => {}
        Err(err) => eprintln!("{err:?}"),
    }
}
