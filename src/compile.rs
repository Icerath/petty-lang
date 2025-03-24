use std::{path::PathBuf, time::Instant};

use crate::{
    ast_analysis, ast_lowering, hir_lowering, mir_interpreter, mir_optimizations,
    parse::parse,
    ty::{TyCtx, TyInterner},
};

#[cfg(test)]
pub fn compile_test(src: &str) -> miette::Result<()> {
    compile_inner(src, None, false, false)
}

pub fn compile(src: &str, file: Option<PathBuf>, verbose: bool) -> miette::Result<()> {
    compile_inner(src, file, true, verbose)
}

fn compile_inner(
    src: &str,
    file: Option<PathBuf>,
    dump: bool,
    verbose: bool,
) -> miette::Result<()> {
    macro_rules! dump {
        ($name:ident, $what:ident) => {
            if dump {
                _ = std::fs::write(
                    format!("target/dump-{}.txt", stringify!($what)),
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
    let ast = parse(&src, file.as_deref())?;
    let ty_intern = TyInterner::default();
    dump!(ast);
    let tcx = TyCtx::new(&ty_intern);
    let analysis = ast_analysis::analyze(file, &src, &ast, &tcx)?;
    let hir = ast_lowering::lower(ast, analysis, &tcx);
    dump!(hir);
    let mut mir = hir_lowering::lower(&hir);
    drop(hir);
    dump!(unoptimized_mir, mir);
    mir_optimizations::optimize(&mut mir);
    dump!(mir);
    if verbose {
        eprintln!("Time to compile: {:?}", start.elapsed());
    }
    mir_interpreter::interpret(&mir);
    if verbose {
        eprintln!("Total time: {:?}", start.elapsed());
    }
    Ok(())
}
