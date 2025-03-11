#![expect(dead_code)]

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{
    symbol::Symbol,
    ty::{Ty, TyCtx},
};

#[derive(Default, Debug)]
pub struct Hir {
    pub exprs: IndexVec<ExprId, Expr>,
    pub root: Vec<ExprId>,
}

index_vec::define_index_type! {
    pub struct ExprId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

index_vec::define_index_type! {
    pub struct BlockId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

#[derive(Debug)]
pub struct Expr {
    pub ty: Ty,
    pub kind: ExprKind,
}

impl Expr {
    pub fn unit(tcx: &TyCtx) -> Self {
        Self { ty: tcx.unit().clone(), kind: ExprKind::Literal(Lit::Unit) }
    }
}

#[derive(Debug)]
pub enum ExprKind {
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    Literal(Lit),
    Block(ThinVec<ExprId>),
    // FnDecl { ident: Symbol, params: ThinVec<Param>, body: ExprId }, - Might be better repr
    FnDecl { ident: Symbol, params: ThinVec<Param>, ret: Ty, body: ThinVec<ExprId> },
    Let { ident: Symbol, expr: ExprId },
}

type BinaryOp = crate::ast::BinaryOp;
type UnaryOp = crate::ast::UnaryOp;

#[derive(Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int(i64),
    Char(char),
    String(Symbol),
}

#[derive(Debug)]
pub struct Param {
    pub ident: Symbol,
    pub ty: Ty,
}
