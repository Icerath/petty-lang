mod display;

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{define_id, source::span::Span, symbol::Symbol, ty::Ty};

#[derive(Default, Debug)]
pub struct Hir<'tcx> {
    pub exprs: IndexVec<ExprId, Expr<'tcx>>,
    pub root: Vec<ExprId>,
}

define_id!(pub ExprId);
define_id!(pub LocalId);
define_id!(pub BodyId);

#[derive(Debug)]
pub struct Expr<'tcx> {
    pub ty: Ty<'tcx>,
    pub kind: ExprKind<'tcx>,
}

impl Expr<'_> {
    pub const UNIT: Self = ExprKind::Literal(Lit::Unit).with(Ty::UNIT);
    pub const BREAK: Self = ExprKind::Break.with(Ty::NEVER);
    pub const CONTINUE: Self = ExprKind::Continue.with(Ty::NEVER);
    pub const TRUE: Self = ExprKind::Literal(Lit::Bool(true)).with(Ty::BOOL);
    pub const FALSE: Self = ExprKind::Literal(Lit::Bool(false)).with(Ty::BOOL);
}

#[derive(Debug)]
pub enum ExprKind<'tcx> {
    Unreachable,
    Abort { msg: Symbol },
    StructInit,
    Field { expr: ExprId, field: usize },
    Func(BodyId),
    Path(Path),
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    OpAssign { place: ExprId, op: OpAssign, expr: ExprId },
    Assignment { lhs: ExprId, expr: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    Literal(Lit),
    Block(ThinVec<ExprId>),
    FnCall { function: ExprId, args: ThinVec<ExprId> },
    Index { expr: ExprId, index: ExprId, span: Span },
    FnDecl(Box<FnDecl<'tcx>>),
    Let { ident: Symbol, expr: ExprId },
    If { arms: ThinVec<IfStmt>, els: ThinVec<ExprId> },
    Match { scrutinee: ExprId, arms: ThinVec<MatchArm<'tcx>>, new_scope: bool },
    Loop(ThinVec<ExprId>),
    ForLoop { ident: Symbol, iter: ExprId, body: ThinVec<ExprId> },
    Break,
    Continue,
    Return(ExprId),
}

impl<'tcx> From<FnDecl<'tcx>> for Expr<'tcx> {
    fn from(decl: FnDecl<'tcx>) -> Self {
        ExprKind::FnDecl(Box::new(decl)).with(Ty::UNIT)
    }
}

#[derive(Debug)]
pub struct Path {
    pub segments: ThinVec<Symbol>,
}

#[derive(Debug)]
pub struct MatchArm<'tcx> {
    pub pat: Pat<'tcx>,
    pub body: ExprId,
}

#[derive(Debug)]
pub enum Pat<'tcx> {
    Struct(Ty<'tcx>, ThinVec<PatField<'tcx>>),
    Ident(Symbol),
    Expr(ExprId),
    If(ExprId),
    Or(ThinVec<Pat<'tcx>>),
    And(ThinVec<Pat<'tcx>>),
    Array(ThinVec<Pat<'tcx>>),
    Wildcard,
}

#[derive(Debug)]
pub struct PatField<'tcx> {
    pub ident: Symbol,
    pub pat: Pat<'tcx>,
}

#[derive(Debug)]
pub struct FnDecl<'tcx> {
    pub ident: Symbol,
    pub for_ty: Option<Ty<'tcx>>,
    pub params: Vec<Param<'tcx>>,
    pub ret: Ty<'tcx>,
    pub body: ThinVec<ExprId>,
    pub id: BodyId,
}

impl FnDecl<'_> {
    pub fn is_generic(&self) -> bool {
        let mut is_generic = false;
        self.params.iter().for_each(|param| param.ty.generics(&mut |_| is_generic = true));
        self.ret.generics(&mut |_| is_generic = true);
        is_generic
    }
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
            crate::ast::BinOpKind::AddAssign => Self::Add,
            crate::ast::BinOpKind::SubAssign => Self::Sub,
            crate::ast::BinOpKind::MulAssign => Self::Mul,
            crate::ast::BinOpKind::DivAssign => Self::Div,
            crate::ast::BinOpKind::ModAssign => Self::Mod,
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

impl Path {
    pub fn single(&self) -> Option<Symbol> {
        match &*self.segments {
            &[ident] => Some(ident),
            _ => None,
        }
    }
}
