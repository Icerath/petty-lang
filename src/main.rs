use ty::TyCtx;

mod ast;
mod ast_analysis;
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
    println!("{ast}");
    let mut tcx = TyCtx::default();
    let analysis = ast_analysis::analyze(&ast, &mut tcx);
    println!("{analysis:?}");
}
