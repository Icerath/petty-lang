use std::{path::Path, time::Instant};

use crate::{
    ast_analysis, ast_lowering, hir_lowering, mir_interpreter, mir_optimizations,
    parse::parse,
    ty::{TyCtx, TyInterner},
};

#[cfg(test)]
pub fn compile_test(src: &str) -> miette::Result<()> {
    compile_inner(src, None, false, 0)
}

pub fn compile(src: &str, file: Option<&Path>, verbose: u8) -> miette::Result<()> {
    compile_inner(src, file, true, verbose)
}

fn compile_inner(src: &str, file: Option<&Path>, dump: bool, verbose: u8) -> miette::Result<()> {
    macro_rules! dump {
        ($name:ident, $what:ident) => {
            if dump {
                _ = std::fs::write(
                    format!("target/dump-{}.txt", stringify!($name)),
                    format!("{}", $what),
                );
            }
        };
        ($what:ident) => {
            dump!($what, $what)
        };
    }
    let start = Instant::now();
    let src = crate::STD.to_string() + src;
    let ast = parse(&src, file)?;
    let ty_intern = TyInterner::default();
    dump!(ast);
    let tcx = TyCtx::new(&ty_intern);
    let analysis = ast_analysis::analyze(file, &src, &ast, &tcx)?;
    let hir = ast_lowering::lower(&src, file, ast, analysis);
    dump!(hir);
    let mut mir = hir_lowering::lower(&hir);
    drop(hir);
    dump!(unoptimized_mir, mir);
    mir_optimizations::optimize(&mut mir);
    dump!(mir);
    if verbose > 1 {
        eprintln!("type interner entries: {}", ty_intern.len());
        eprintln!("type interner cache hits: {}", ty_intern.cache_hits());
    }
    if verbose > 0 {
        eprintln!("compile time: {:?}", start.elapsed());
        eprintln!();
    }
    mir_interpreter::interpret(&mir);
    if verbose > 0 {
        eprintln!();
        eprintln!("total time: {:?}", start.elapsed());
    }
    Ok(())
}
