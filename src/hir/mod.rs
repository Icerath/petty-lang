mod display;

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{
    symbol::Symbol,
    ty::{Ty, TyCtx},
};

#[derive(Default, Debug)]
pub struct Hir<'tcx> {
    pub exprs: IndexVec<ExprId, Expr<'tcx>>,
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
pub struct Expr<'tcx> {
    pub ty: Ty<'tcx>,
    pub kind: ExprKind<'tcx>,
}

impl<'tcx> Expr<'tcx> {
    pub fn unit(tcx: &'tcx TyCtx<'tcx>) -> Self {
        Self { ty: tcx.unit(), kind: ExprKind::Literal(Lit::Unit) }
    }
}

#[derive(Debug)]
pub enum ExprKind<'tcx> {
    Ident(Symbol),
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    Assignment { lhs: LValue, expr: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    Literal(Lit),
    Block(ThinVec<ExprId>),
    FnCall { function: ExprId, args: ThinVec<ExprId> },
    Index { expr: ExprId, index: ExprId },
    FnDecl(Box<FnDecl<'tcx>>),
    Let { ident: Symbol, expr: ExprId },
    If { arms: ThinVec<IfStmt>, els: ThinVec<ExprId> },
    Loop(ThinVec<ExprId>),
    Break,
    Struct { ident: Symbol, fields: ThinVec<Param<'tcx>> },
    Return(ExprId),
}

#[derive(Debug)]
pub struct FnDecl<'tcx> {
    pub ident: Symbol,
    pub params: Vec<Param<'tcx>>,
    pub ret: Ty<'tcx>,
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
pub struct Param<'tcx> {
    pub ident: Symbol,
    pub ty: Ty<'tcx>,
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
