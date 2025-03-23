mod display;

use std::fmt;

use crate::{span::Span, symbol::Symbol};
use index_vec::IndexVec;
use thin_vec::ThinVec;

#[derive(Default)]
pub struct Ast {
    pub exprs: IndexVec<ExprId, Expr>,
    pub blocks: IndexVec<BlockId, Block>,
    pub types: IndexVec<TypeId, Ty>,
    pub top_level: Vec<ExprId>,
}

index_vec::define_index_type! {
    pub struct ExprId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

index_vec::define_index_type! {
    pub struct BlockId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

index_vec::define_index_type! {
    pub struct TypeId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

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

#[derive(Debug)]
pub enum Ty {
    Never,
    Unit,
    Name(Symbol),
    Array(TypeId),
}

#[derive(Debug)]
pub enum ExprKind {
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
    If { arms: ThinVec<IfStmt>, els: Option<BlockId> },
    Return(Option<ExprId>),
    Break,
    FnDecl { ident: Symbol, params: ThinVec<Param>, ret: Option<TypeId>, block: BlockId },
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
    Abort,
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
}

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stmts.fmt(f)
    }
}

impl Ast {
    pub fn spans(&self, exprs: impl IntoIterator<Item = ExprId>) -> Span {
        let mut start = u32::MAX;
        let mut end = 0;
        exprs.into_iter().for_each(|expr| {
            let range = self.exprs[expr].span;
            start = start.min(range.start());
            end = start.max(range.end());
        });
        Span::from(start..end)
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
