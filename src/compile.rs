use std::{
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    time::Instant,
};

use miette::{Error, IntoDiagnostic};
use petty_intern::Interner;

use crate::{
    Args, ast_analysis, ast_lowering, cli::Command, hir_lowering, mir_interpreter,
    mir_optimizations, parse::parse, ty::TyCtx,
};

#[cfg(test)]
pub fn compile_test(path: impl Into<std::path::PathBuf>) -> Result<Vec<u8>, Vec<Error>> {
    use crate::cli::Command;

    let path = path.into();
    let mut args = Args {
        show_auto: false,
        command: Command::Run,
        path,
        verbose: 0,
        dump: None,
        codegen: crate::CodegenOpts::all(true),
    };
    let mut w = vec![];
    compile(&args, &mut w)?;
    let mut w2 = Vec::with_capacity(w.len());
    args.codegen = crate::CodegenOpts::all(false);
    compile(&args, &mut w2)?;
    assert_eq!(w, w2);
    Ok(w2)
}

pub fn compile(args: &Args, w: &mut dyn Write) -> miette::Result<(), Vec<Error>> {
    let src = fs::read_to_string(&args.path).into_diagnostic().map_err(|e| vec![e])?;
    if let Some(target) = &args.dump {
        create_new_dir(target).into_diagnostic().map_err(|e| vec![e])?;
    }

    let ty_intern = Interner::default();
    let tcx = TyCtx::new(&ty_intern);

    macro_rules! dump {
        ($name:ident, $what: expr) => {
            if let Some(target) = &args.dump {
                let filename = concat!("dump-", stringify!($name), ".txt");
                let content = $what;
                let path: PathBuf = [target.as_path(), filename.as_ref()].into_iter().collect();
                fs::write(path, content).into_diagnostic().map_err(|e| vec![e])?;
            }
        };
        ($what:ident) => {
            dump!($what, $what.to_string())
        };
        (@d $what:ident) => {
            dump!($what, $what.display(&tcx).to_string())
        };
    }
    let start = Instant::now();
    let src = crate::STD.to_string() + &src;
    let ast = parse(&src, &args.path).map_err(|e| vec![e])?;
    dump!(ast);
    let analysis = ast_analysis::analyze(&ast, &tcx)?;
    let hir = ast_lowering::lower(ast, analysis);
    dump!(@d hir);
    let mut mir = hir_lowering::lower(&hir, &tcx);
    drop(hir);
    mir_optimizations::optimize(&mut mir, &args.codegen, args.verbose);
    dump!(mir, mir.display(args.show_auto).to_string());
    if args.verbose > 1 {
        crate::log!("type interner entries: {}", ty_intern.len());
    }
    if args.verbose > 0 {
        crate::log!("compile time: {:?}", start.elapsed());
    }
    if args.command == Command::Run {
        if args.verbose > 0 {
            crate::log!();
        }
        mir_interpreter::interpret(&mir, w);
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
