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

pub use codegen_opts::CodegenOpts;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use source::span;

const STD: &str = concat!(include_str!("std.pebble"), "\n\n");

#[derive(Parser)]
struct Args {
    command: Command,
    path: PathBuf,
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
    #[arg(long, help = "Turns off all optimizations unless overriden")]
    no_default_optimizations: bool,
    #[arg(long, default_value = "true", help = "Dumps the ast/hir/mir to the target directory ")]
    dump: bool,
    #[arg(long, default_value = "target", help = "The target directory")]
    target: PathBuf,
    #[command(flatten)]
    codegen: CodegenOpts,
}

#[derive(clap::ValueEnum, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Command {
    Build,
    Run,
}

fn main() {
    let args = Args::parse();
    match compile::compile(&args) {
        Ok(()) => {
            if args.verbose > 0 {
                log!("mir dumped to {}/dump-mir.txt", args.target.display());
            }
        }
        Err(err) => eprintln!("{err:?}"),
    }
}

#[macro_export]
macro_rules! log {
    () => {
        eprintln!()
    };
    ($($arg:tt)*) => {{
        use colored::Colorize;
        eprintln!("{}", format!($($arg)*).as_str().blue())
    }};
}
