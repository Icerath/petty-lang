mod display;

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{
    define_id,
    source::span::Span,
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
    pub const UNIT: Self = ExprKind::Literal(Lit::Unit).with(&TyKind::Unit);
    pub const BREAK: Self = ExprKind::Break.with(&TyKind::Never);
    pub const CONTINUE: Self = ExprKind::Continue.with(&TyKind::Never);
}

#[derive(Debug)]
pub enum ExprKind<'tcx> {
    Unreachable,
    Abort { msg: Symbol },
    StructInit,
    Field { expr: ExprId, field: usize },
    Ident(Symbol),
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    OpAssign { place: ExprId, op: OpAssign, expr: ExprId },
    Assignment { lhs: ExprId, expr: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    Literal(Lit),
    Block(ThinVec<ExprId>),
    Method { ty: Ty<'tcx>, method: Symbol },
    FnCall { function: ExprId, args: ThinVec<ExprId> },
    Index { expr: ExprId, index: ExprId, span: Span },
    FnDecl(Box<FnDecl<'tcx>>),
    Let { ident: Symbol, expr: ExprId },
    If { arms: ThinVec<IfStmt>, els: ThinVec<ExprId> },
    Loop(ThinVec<ExprId>),
    ForLoop { ident: Symbol, iter: ExprId, body: ThinVec<ExprId> },
    Break,
    Continue,
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
    pub for_ty: Option<Ty<'tcx>>,
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

#[derive(Debug, Clone, Copy)]
pub enum OpAssign {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
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
    pub const fn with(self, ty: Ty<'tcx>) -> Expr<'tcx> {
        Expr { kind: self, ty }
    }
}

impl<'tcx> ExprId {
    pub fn unary(self, op: UnaryOp) -> ExprKind<'tcx> {
        ExprKind::Unary { op, expr: self }
    }
}

impl TryFrom<crate::ast::BinOpKind> for OpAssign {
    type Error = ();
    fn try_from(op: crate::ast::BinOpKind) -> Result<Self, Self::Error> {
        Ok(match op {
            crate::ast::BinOpKind::AddAssign => OpAssign::Add,
            crate::ast::BinOpKind::SubAssign => OpAssign::Sub,
            crate::ast::BinOpKind::MulAssign => OpAssign::Mul,
            crate::ast::BinOpKind::DivAssign => OpAssign::Div,
            crate::ast::BinOpKind::ModAssign => OpAssign::Mod,
            _ => return Err(()),
        })
    }
}

impl From<OpAssign> for BinaryOp {
    fn from(op: OpAssign) -> Self {
        match op {
            OpAssign::Add => Self::Add,
            OpAssign::Sub => Self::Sub,
            OpAssign::Mul => Self::Mul,
            OpAssign::Div => Self::Div,
            OpAssign::Mod => Self::Mod,
        }
    }
}
