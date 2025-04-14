use std::{
    fs, io,
    path::{Path, PathBuf},
    time::Instant,
};

use miette::IntoDiagnostic;

use crate::{
    Args, ast_analysis, ast_lowering, hir_lowering, mir_interpreter, mir_optimizations,
    parse::parse,
    ty::{TyCtx, TyInterner},
};

#[cfg(test)]
pub fn compile_test(path: impl Into<std::path::PathBuf>) -> miette::Result<()> {
    let path = path.into();
    let mut args = Args {
        command: crate::Command::Run,
        path: path.clone(),
        verbose: 0,
        no_default_optimizations: false,
        dump: false,
        target: "target".into(),
        codegen: crate::CodegenOpts::all(true),
    };
    compile(&args)?;
    args.codegen = crate::CodegenOpts::all(false);
    compile(&args)
}

pub fn compile(args: &Args) -> miette::Result<()> {
    let src = fs::read_to_string(&args.path).into_diagnostic()?;
    if args.dump {
        create_new_dir(&args.target).into_diagnostic()?;
    }
    macro_rules! dump {
        ($name:ident, $what:ident) => {
            if args.dump {
                let filename = concat!("dump-", stringify!($name), ".txt");
                let content = $what.to_string();
                let path: PathBuf =
                    [args.target.as_path(), filename.as_ref()].into_iter().collect();
                fs::write(path, content).into_diagnostic()?;
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
    mir_optimizations::optimize(&mut mir, &args.codegen, args.verbose);
    dump!(mir);
    if args.verbose > 1 {
        crate::log!("type interner entries: {}", ty_intern.len());
        crate::log!("type interner cache hits: {}", ty_intern.cache_hits());
    }
    if args.verbose > 0 {
        crate::log!("compile time: {:?}", start.elapsed());
    }
    if args.command == crate::Command::Run {
        if args.verbose > 0 {
            crate::log!();
        }
        mir_interpreter::interpret(&mir);
        if args.verbose > 0 {
            crate::log!();
            crate::log!("total time: {:?}", start.elapsed());
        }
    }
    Ok(())
}

fn create_new_dir<P: AsRef<Path>>(path: P) -> io::Result<()> {
    match fs::create_dir(path) {
        Err(err) if err.kind() == io::ErrorKind::AlreadyExists => Ok(()),
        other => other,
    }
}
