use ty::TyCtx;

mod ast;
mod ast_analysis;
mod ast_lowering;
mod hir;
mod parse;
mod span;
mod symbol;
mod ty;

fn main() {
    macro_rules! try_miette {
        ($expr: expr) => {
            match $expr {
                Ok(ok) => ok,
                Err(err) => {
                    eprintln!("{err:?}");
                    return;
                }
            }
        };
    }

    let std = include_str!("std.pebble").to_string();
    let src = std + include_str!("../examples/brainfuck.pebble");

    let ast = try_miette!(parse::parse(&src));
    let mut tcx = TyCtx::default();
    let analysis = ast_analysis::analyze(&ast, &mut tcx);
    let hir = ast_lowering::lower_ast(ast, analysis, &tcx);
    println!("{hir:?}");
}
