mod display;

use std::fmt;

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{define_id, span::Span, symbol::Symbol};

#[derive(Default)]
pub struct Ast {
    pub exprs: IndexVec<ExprId, Expr>,
    pub blocks: IndexVec<BlockId, Block>,
    pub types: IndexVec<TypeId, Ty>,
    pub top_level: Vec<ExprId>,
}

define_id!(pub ExprId);
define_id!(pub BlockId);
define_id!(pub TypeId);

impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.top_level.fmt(f)
    }
}

pub struct Block {
    pub stmts: ThinVec<ExprId>,
    /// Will be false if the last expression if followed by a ';' or the block is empty.
    pub is_expr: bool,
    pub span: Span,
}

#[derive(Debug)]
pub struct IfStmt {
    pub condition: ExprId,
    pub body: BlockId,
}

#[derive(Debug)]
pub struct Param {
    pub ident: Symbol,
    pub ty: TypeId,
}

pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind {
    Never,
    Unit,
    Name(Symbol),
    Array(TypeId),
    Func { params: ThinVec<TypeId>, ret: Option<TypeId> },
    Ref(TypeId),
}

#[derive(Debug)]
pub enum ExprKind {
    Unreachable,
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    FnCall { function: ExprId, args: ThinVec<ExprId> },
    MethodCall { expr: ExprId, method: Symbol, args: ThinVec<ExprId> },
    Ident(Symbol),
    Index { expr: ExprId, index: ExprId },
    FieldAccess { expr: ExprId, field: Symbol },
    Lit(Lit),
    Block(BlockId),
    Let { ident: Symbol, ty: Option<TypeId>, expr: ExprId },
    While { condition: ExprId, block: BlockId },
    For { ident: Symbol, iter: ExprId, body: BlockId },
    If { arms: ThinVec<IfStmt>, els: Option<BlockId> },
    Return(Option<ExprId>),
    Assert(ExprId),
    Break,
    FnDecl(FnDecl),
    Struct { ident: Symbol, span: Span, fields: ThinVec<Param> },
}

#[derive(Debug)]
pub struct FnDecl {
    pub ident: Symbol,
    pub generics: ThinVec<Symbol>,
    pub params: ThinVec<Param>,
    pub ret: Option<TypeId>,
    pub block: BlockId,
}

#[derive(Debug)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub struct ArraySeg {
    pub expr: ExprId,
    pub repeated: Option<ExprId>,
}

#[derive(Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int(i64),
    Str(Symbol),
    Char(char),
    Array { segments: ThinVec<ArraySeg> },
}

#[derive(Debug, Clone, Copy)]
pub struct BinaryOp {
    pub kind: BinOpKind,
    #[expect(dead_code)]
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOpKind {
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,

    Add,
    Sub,
    Mul,
    Div,
    Mod,

    Eq,
    Neq,
    Greater,
    Less,
    GreaterEq,
    LessEq,

    Range,
    RangeInclusive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnaryOp {
    Neg,
    Not,
    Ref,
    Deref,
}

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stmts.fmt(f)
    }
}

impl Ast {
    pub fn spans(&self, exprs: impl IntoIterator<Item = ExprId>) -> Span {
        Span::join(exprs.into_iter().map(|expr| self.exprs[expr].span))
    }
}

impl ExprKind {
    pub fn todo_span(self) -> Expr {
        self.with_span(Span::ZERO)
    }
    pub fn with_span(self, span: impl Into<Span>) -> Expr {
        Expr { span: span.into(), kind: self }
    }
}
