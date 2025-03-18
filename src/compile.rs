use crate::{ast_analysis, ast_lowering, hir_lowering, mir_interpreter, parse::parse, ty::TyCtx};

#[allow(dead_code)]
pub fn compile(src: &str) -> miette::Result<()> {
    compile_inner(src, false)
}

pub fn compile_and_dump(src: &str) -> miette::Result<()> {
    compile_inner(src, true)
}

fn compile_inner(src: &str, dump: bool) -> miette::Result<()> {
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
    let src = include_str!("std.pebble").to_string() + src;
    let ast = parse(&src)?;
    let tcx = TyCtx::default();
    let analysis = ast_analysis::analyze(&ast, &tcx);
    dump!(ast);
    let hir = ast_lowering::lower(ast, analysis, &tcx);
    dump!(hir);
    let mir = hir_lowering::lower(&hir);
    dump!(mir);
    mir_interpreter::interpret(&mir);
    Ok(())
}
