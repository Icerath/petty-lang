mod display;

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{
    define_id,
    symbol::Symbol,
    ty::{Ty, TyKind},
};

#[derive(Default, Debug)]
pub struct Hir<'tcx> {
    pub exprs: IndexVec<ExprId, Expr<'tcx>>,
    pub root: Vec<ExprId>,
}

define_id!(pub ExprId);

#[derive(Debug)]
pub struct Expr<'tcx> {
    pub ty: Ty<'tcx>,
    pub kind: ExprKind<'tcx>,
}

impl Expr<'_> {
    pub const UNIT: Self = Self { ty: &TyKind::Unit, kind: ExprKind::Literal(Lit::Unit) };
    pub const BREAK: Self = Self { ty: &TyKind::Never, kind: ExprKind::Break };
}

#[derive(Debug)]
pub enum ExprKind<'tcx> {
    Unreachable,
    Abort,
    StructInit,
    Field { expr: ExprId, field: usize },
    PrintStr(Symbol), // temporary
    Ident(Symbol),
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    Assignment { lhs: ExprId, expr: ExprId },
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
    Return(ExprId),
}

impl<'tcx> From<FnDecl<'tcx>> for Expr<'tcx> {
    fn from(decl: FnDecl<'tcx>) -> Self {
        ExprKind::FnDecl(Box::new(decl)).with(&TyKind::Unit)
    }
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

    And,
    Or,
}

pub type UnaryOp = crate::ast::UnaryOp;

#[derive(Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int(i64),
    Char(char),
    String(Symbol),
    Array { segments: ThinVec<ArraySeg> },
    FStr { segments: ThinVec<ExprId> },
}

#[derive(Debug)]
pub struct ArraySeg {
    pub expr: ExprId,
    pub repeated: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub struct Param<'tcx> {
    pub ident: Symbol,
    pub ty: Ty<'tcx>,
}

#[derive(Debug)]
pub struct IfStmt {
    pub condition: ExprId,
    pub body: ThinVec<ExprId>,
}

impl<'tcx> ExprKind<'tcx> {
    pub fn with(self, ty: Ty<'tcx>) -> Expr<'tcx> {
        Expr { kind: self, ty }
    }
}

impl<'tcx> ExprId {
    pub fn unary(self, op: UnaryOp) -> ExprKind<'tcx> {
        ExprKind::Unary { op, expr: self }
    }
}
