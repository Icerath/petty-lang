use std::time::Instant;

use miette::IntoDiagnostic;

use crate::{
    Args, ast_analysis, ast_lowering, hir_lowering, mir_interpreter, mir_optimizations,
    parse::parse,
    ty::{TyCtx, TyInterner},
};

#[cfg(test)]
pub fn compile_test(path: impl Into<std::path::PathBuf>) -> miette::Result<()> {
    use crate::CodegenOpts;

    let args = Args {
        path: path.into(),
        codegen: CodegenOpts::default(),
        verbose: 0,
        no_default_optimizations: false,
        dump: false,
    };
    compile(&args)
}

pub fn compile(args: &Args) -> miette::Result<()> {
    let src = std::fs::read_to_string(&args.path).into_diagnostic()?;
    macro_rules! dump {
        ($name:ident, $what:ident) => {
            if args.dump {
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
    let src = crate::STD.to_string() + &src;
    let ast = parse(&src, Some(&args.path))?;
    let ty_intern = TyInterner::default();
    dump!(ast);
    let tcx = TyCtx::new(&ty_intern);
    let analysis = ast_analysis::analyze(Some(&args.path), &src, &ast, &tcx)?;
    let hir = ast_lowering::lower(&src, Some(&args.path), ast, analysis);
    dump!(hir);
    let mut mir = hir_lowering::lower(&hir);
    drop(hir);
    dump!(unoptimized_mir, mir);
    mir_optimizations::optimize(&mut mir, &args.codegen);
    dump!(mir);
    if args.verbose > 1 {
        eprintln!("type interner entries: {}", ty_intern.len());
        eprintln!("type interner cache hits: {}", ty_intern.cache_hits());
    }
    if args.verbose > 0 {
        eprintln!("compile time: {:?}", start.elapsed());
        eprintln!();
    }
    mir_interpreter::interpret(&mir);
    if args.verbose > 0 {
        eprintln!();
        eprintln!("total time: {:?}", start.elapsed());
    }
    Ok(())
}
