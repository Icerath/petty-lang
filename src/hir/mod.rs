mod display;

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
    Ident(Symbol),
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    Assignment { lhs: LValue, expr: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    Literal(Lit),
    Block(ThinVec<ExprId>),
    FnCall { function: ExprId, args: ThinVec<ExprId> },
    Index { expr: ExprId, index: ExprId },
    FnDecl(Box<FnDecl>),
    Let { ident: Symbol, expr: ExprId },
    If { arms: ThinVec<IfStmt>, els: ThinVec<ExprId> },
    Loop(ThinVec<ExprId>),
    Break,
    Return(ExprId),
}

#[derive(Debug)]
pub struct FnDecl {
    pub ident: Symbol,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub body: ThinVec<ExprId>,
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    Range,
    RangeInclusive,

    Less,
    Greater,
    LessEq,
    GreaterEq,
    Eq,
    Neq,
}

pub type UnaryOp = crate::ast::UnaryOp;

#[derive(Debug)]
pub enum Lit {
    Abort,
    Unit,
    Bool(bool),
    Int(i64),
    Char(char),
    String(Symbol),
    Array { segments: ThinVec<ArraySeg> },
}

#[derive(Debug)]
pub struct ArraySeg {
    pub expr: ExprId,
    pub repeated: Option<ExprId>,
}

#[derive(Debug)]
pub struct Param {
    pub ident: Symbol,
    pub ty: Ty,
}

#[derive(Debug)]
pub struct IfStmt {
    pub condition: ExprId,
    pub body: ThinVec<ExprId>,
}

#[derive(Debug)]
pub enum LValue {
    Name(Symbol),
    Index { indexee: Box<LValue>, index: ExprId },
}
