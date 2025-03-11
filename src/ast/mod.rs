mod display;

use std::fmt;

use crate::symbol::Symbol;
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
    Name(Symbol),
    Array(TypeId),
}

#[derive(Debug)]
pub enum Expr {
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    FnCall { function: ExprId, args: ThinVec<ExprId> },
    MethodCall { expr: ExprId, method: Symbol, args: ThinVec<ExprId> },
    Ident(Symbol),
    Index { expr: ExprId, index: ExprId },
    FieldAccess { expr: ExprId, field: Symbol },
    StructInit { ident: Symbol, args: ThinVec<StructInitField> },
    Lit(Lit),
    Block(BlockId),
    Let { ident: Symbol, ty: Option<TypeId>, expr: ExprId },
    While { condition: ExprId, block: BlockId },
    If { arms: ThinVec<IfStmt>, els: Option<BlockId> },
    FnDecl { ident: Symbol, params: ThinVec<Param>, ret: Option<TypeId>, block: BlockId },
}

#[derive(Debug)]
pub struct StructInitField {
    pub field: Symbol,
    pub expr: Option<ExprId>,
}

#[derive(Debug)]
pub struct ArraySeg {
    pub expr: ExprId,
    pub repeated: Option<ExprId>,
}

#[derive(Debug)]
pub enum Lit {
    Int(i64),
    Str(Symbol),
    Char(char),
    Bool(bool),
    Array { segments: ThinVec<ArraySeg> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinaryOp {
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
