#[cfg(test)]
mod tests;

mod ast;
mod ast_analysis;
mod ast_lowering;
mod cli;
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
mod scope;
mod source;
mod symbol;
mod ty;

pub use cli::Args;
pub use codegen_opts::CodegenOpts;
use rustc_hash::FxBuildHasher;
use source::span;

pub type HashMap<K, V> = std::collections::HashMap<K, V, FxBuildHasher>;

const STD: &str = concat!(include_str!("std.pty"), "\n\n");

fn main() {
    let args = Args::parse();
    let mut stdout = std::io::stdout().lock();
    match compile::compile(&args, &mut stdout) {
        Ok(()) => {
            if let Some(target) = args.dump {
                if args.verbose > 0 {
                    log!("mir dumped to {}/dump-mir.txt", target.display());
                }
            }
        }
        Err(errors) => {
            for err in errors {
                eprintln!("{err:?}");
            }
        }
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
