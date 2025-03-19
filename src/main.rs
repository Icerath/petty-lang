use std::{path::PathBuf, time::Instant};

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
    let start = Instant::now();
    match compile::compile_and_dump(&src) {
        Ok(()) => {}
        Err(err) => eprintln!("{err:?}"),
    }
    if args.verbose {
        eprintln!();
        eprintln!("Time taken: {:?}", start.elapsed());
    }
}
