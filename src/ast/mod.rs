use std::{
    cell::{Ref, RefCell},
    fmt,
    ops::{Index, IndexMut},
};

use thin_vec::ThinVec;
use ustr::Ustr as Symbol;

#[derive(Default)]
pub struct Ast {
    pub exprs: RefCell<Vec<Expr>>,
    pub top_level: RefCell<Vec<Stmt>>,
}

impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let top = self.top_level.borrow();
        top.fmt(f)
    }
}

impl Ast {
    pub fn push_top(&self, stmt: Stmt) {
        self.top_level.borrow_mut().push(stmt);
    }
    pub fn add(&self, expr: Expr) -> ExprId {
        let mut exprs = self.exprs.borrow_mut();
        let id = ExprId { index: exprs.len() as u32 };
        exprs.push(expr);
        id
    }
    pub fn get(&self, id: ExprId) -> Ref<Expr> {
        std::cell::Ref::map(self.exprs.borrow(), |exprs| &exprs[id])
    }
}

pub struct Block {
    pub stmts: ThinVec<Stmt>,
}

#[derive(Debug)]
pub enum Stmt {
    Let { ident: Symbol, ty: Option<Ty>, expr: ExprId },
    While { condition: ExprId, block: Block },
    If { arms: ThinVec<IfStmt>, els: Option<Block> },
    FnDecl { ident: Symbol, params: ThinVec<Param>, ret: Option<Ty>, block: Block },
    Expr(ExprId),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExprId {
    index: u32,
}

impl<T> Index<ExprId> for [T] {
    type Output = T;
    fn index(&self, index: ExprId) -> &Self::Output {
        &self[index.index as usize]
    }
}

impl<T> IndexMut<ExprId> for [T] {
    fn index_mut(&mut self, index: ExprId) -> &mut Self::Output {
        &mut self[index.index as usize]
    }
}

impl<T> Index<ExprId> for Vec<T> {
    type Output = T;
    fn index(&self, index: ExprId) -> &Self::Output {
        &self[index.index as usize]
    }
}

impl<T> IndexMut<ExprId> for Vec<T> {
    fn index_mut(&mut self, index: ExprId) -> &mut Self::Output {
        &mut self[index.index as usize]
    }
}

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stmts.fmt(f)
    }
}
