use std::time::Instant;

use crate::{
    ast_analysis, ast_lowering, hir_lowering, mir_interpreter, mir_optimizations,
    parse::parse,
    ty::{TyCtx, TyInterner},
};

#[cfg(test)]
pub fn compile_test(src: &str) -> miette::Result<()> {
    compile_inner(src, false, false)
}

pub fn compile(src: &str, verbose: bool) -> miette::Result<()> {
    compile_inner(src, true, verbose)
}

fn compile_inner(src: &str, dump: bool, verbose: bool) -> miette::Result<()> {
    macro_rules! dump {
        ($what: ident) => {
            if dump {
                _ = std::fs::write(
                    format!("target/dump-{}.txt", stringify!($what)),
                    format!("{}", $what),
                );
            }
        };
    }
    let start = Instant::now();
    let src = include_str!("std.pebble").to_string() + src;
    let ast = parse(&src)?;
    let ty_intern = TyInterner::default();
    let tcx = TyCtx::new(&ty_intern);
    let analysis = ast_analysis::analyze(&src, &ast, &tcx);
    dump!(ast);
    let hir = ast_lowering::lower(ast, analysis, &tcx);
    dump!(hir);
    let mut mir = hir_lowering::lower(&hir);
    {
        let unoptimized_mir = &mir;
        dump!(unoptimized_mir);
    }
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
