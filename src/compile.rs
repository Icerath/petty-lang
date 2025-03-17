use crate::{ast_analysis, ast_lowering, hir_lowering, parse::parse, ty::TyCtx};

pub fn compile(src: &str) -> miette::Result<()> {
    let std = include_str!("std.pebble").to_string();
    let src = std + src;

    let ast = parse(&src)?;
    let tcx = TyCtx::default();
    let analysis = ast_analysis::analyze(&ast, &tcx);
    let hir = ast_lowering::lower(ast, analysis, &tcx);
    let mir = hir_lowering::lower(&hir);
    println!("{mir}",);
    Ok(())
}
