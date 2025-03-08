use ty::TyCtx;

mod ast_analysis;
mod parse;
mod span;
mod ty;

fn main() {
    let src = include_str!("../examples/brainfuck.pebble");

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

    let ast = try_miette!(parse::parse(src));
    let mut tcx = TyCtx::default();
    let analysis = ast_analysis::analyze(&ast, &mut tcx);
    println!("{analysis:?}");
}
