mod display;

use std::{
    cell::{Ref, RefCell},
    fmt,
};

use index_vec::IndexVec;
use thin_vec::ThinVec;
use ustr::Ustr as Symbol;

#[derive(Default)]
pub struct Ast {
    pub exprs: RefCell<IndexVec<ExprId, Expr>>,
    pub top_level: RefCell<Vec<ExprId>>,
}

impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let top = self.top_level.borrow();
        top.fmt(f)
    }
}

impl Ast {
    pub fn push_top(&self, expr: ExprId) {
        self.top_level.borrow_mut().push(expr);
    }
    pub fn add(&self, expr: Expr) -> ExprId {
        let mut exprs = self.exprs.borrow_mut();
        let id = ExprId::from(exprs.len());
        exprs.push(expr);
        id
    }
    pub fn get(&self, id: ExprId) -> Ref<Expr> {
        std::cell::Ref::map(self.exprs.borrow(), |exprs| &exprs[id])
    }
}

pub struct Block {
    pub stmts: ThinVec<ExprId>,
    /// Will be false if the last expression if followed by a ';'.
    pub is_expr: bool,
}

#[derive(Debug)]
pub struct IfStmt {
    pub condition: ExprId,
    pub body: Block,
}

#[derive(Debug)]
pub struct Param {
    pub ident: Symbol,
    pub ty: Ty,
}

#[derive(Debug)]
pub enum Ty {
    Name(Symbol),
    Array(Box<Ty>),
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
    Block(Block),
    Let { ident: Symbol, ty: Option<Ty>, expr: ExprId },
    While { condition: ExprId, block: Block },
    If { arms: ThinVec<IfStmt>, els: Option<Block> },
    FnDecl { ident: Symbol, params: ThinVec<Param>, ret: Option<Ty>, block: Block },
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
index_vec::define_index_type! {
    pub struct ExprId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stmts.fmt(f)
    }
}
