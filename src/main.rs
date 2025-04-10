use std::path::PathBuf;

use clap::Parser;

#[cfg(test)]
mod tests;

mod ast;
mod ast_analysis;
mod ast_lowering;
mod codegen_opts;
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

use codegen_opts::CodegenOpts;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use source::span;

const STD: &str = concat!(include_str!("std.pebble"), "\n\n");

#[derive(Parser)]
struct Args {
    path: PathBuf,
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
    #[arg(long, help = "Turns off all optimizations unless overriden")]
    no_default_optimizations: bool,
    #[arg(long, default_value = "true", help = "Dumps the ast/hir/mir to the target directory ")]
    dump: bool,
    #[command(flatten)]
    codegen: CodegenOpts,
}

fn main() {
    let args = Args::parse();
    match compile::compile(&args) {
        Ok(()) => {}
        Err(err) => eprintln!("{err:?}"),
    }
}
