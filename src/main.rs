use std::path::PathBuf;

use clap::Parser;

#[cfg(test)]
mod tests;

mod ast;
mod ast_analysis;
mod ast_lowering;
mod compile;
mod hir;
mod hir_lowering;
mod mir;
mod mir_interpreter;
mod mir_optimizations;
mod parse;
mod span;
mod symbol;
mod ty;

#[derive(Parser)]
struct Args {
    path: PathBuf,
    #[arg(long, short)]
    verbose: bool,
}

fn main() {
    let args = Args::parse();
    let src = std::fs::read_to_string(&args.path).unwrap();
    match compile::compile(&src, args.verbose) {
        Ok(()) => {}
        Err(err) => eprintln!("{err:?}"),
    }
}
