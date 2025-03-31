use std::path::PathBuf;

use clap::Parser;

#[cfg(test)]
mod tests;

mod ast;
mod ast_analysis;
mod ast_lowering;
mod compile;
mod errors;
mod hir;
mod hir_lowering;
mod id;
mod mir;
mod mir_interpreter;
mod mir_optimizations;
mod parse;
mod source;
mod symbol;
mod ty;

pub use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use source::span;

pub const STD: &str = concat!(include_str!("std.pebble"), "\n\n");

#[derive(Parser)]
struct Args {
    path: PathBuf,
    #[arg(long, short)]
    verbose: bool,
}

fn main() {
    let args = Args::parse();
    let src = std::fs::read_to_string(&args.path).unwrap();
    match compile::compile(&src, Some(&*args.path), args.verbose) {
        Ok(()) => {}
        Err(err) => eprintln!("{err:?}"),
    }
}
