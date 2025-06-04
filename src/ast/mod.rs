mod display;

use std::ops::Deref;

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{define_id, span::Span, symbol::Symbol};

#[derive(Default)]
pub struct Ast {
    pub exprs: IndexVec<ExprId, Expr>,
    pub items: IndexVec<ItemId, Item>,
    pub blocks: IndexVec<BlockId, Block>,
    pub types: IndexVec<TypeId, Ty>,
    pub root: Module,
}

define_id!(pub ExprId);
define_id!(pub ItemId);
define_id!(pub BlockId);
define_id!(pub TypeId);

pub struct Block {
    pub stmts: ThinVec<Stmt>,
    pub expr: Option<ExprId>,
    pub span: Span,
}

pub struct IfStmt {
    pub condition: ExprId,
    pub body: BlockId,
}

#[derive(Clone, Copy)]
pub struct Ident {
    pub symbol: Symbol,
    pub span: Span,
}

pub struct Param {
    pub ident: Ident,
    pub ty: Option<TypeId>,
}

pub struct Field {
    pub ident: Ident,
    pub ty: TypeId,
}

pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

pub enum TyKind {
    Never,
    Unit,
    Name { ident: Ident, generics: ThinVec<TypeId> },
    Array(TypeId),
    Func { params: ThinVec<TypeId>, ret: Option<TypeId> },
    Ref(TypeId),
}

#[derive(Default)]
pub struct Module {
    pub items: Vec<ItemId>,
}

pub struct Item {
    #[expect(unused)]
    pub span: Span,
    pub kind: ItemKind,
}

#[derive(Clone, Copy)]
pub enum Stmt {
    Item(ItemId),
    Expr(ExprId),
}

pub enum ItemKind {
    Module(Ident, Module),
    FnDecl(FnDecl),
    Struct(Ident, ThinVec<Ident>, ThinVec<Field>),
    Const(Ident, Option<TypeId>, ExprId),
    Trait(Trait),
    Impl(Impl),
}

pub enum ExprKind {
    Unreachable,
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    FnCall { function: ExprId, args: ThinVec<ExprId> },
    MethodCall { expr: ExprId, method: Ident, args: ThinVec<ExprId> },
    Ident(Symbol),
    Index { expr: ExprId, index: ExprId },
    FieldAccess { expr: ExprId, field: Ident },
    Lit(Lit),
    Block(BlockId),
    Let { ident: Ident, ty: Option<TypeId>, expr: ExprId },
    While { condition: ExprId, block: BlockId },
    For { ident: Ident, iter: ExprId, body: BlockId },
    If { arms: ThinVec<IfStmt>, els: Option<BlockId> },
    Match { scrutinee: ExprId, arms: ThinVec<MatchArm> },
    Is { scrutinee: ExprId, pat: Pat },
    Return(Option<ExprId>),
    Assert(ExprId),
    Break,
    Continue,
}

pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

pub enum PatKind {
    Bool(bool),
    Int(i64),
    Str(Symbol),
    Expr(BlockId),
    If(ExprId),
    Or(ThinVec<Pat>),
    And(ThinVec<Pat>),
    Ident(Symbol),
    Struct(Ident, ThinVec<PatArg>),
    Array(ThinVec<Pat>),
}

pub struct PatArg {
    pub ident: Ident,
    pub pat: Pat,
}

pub struct MatchArm {
    pub pat: Pat,
    pub body: ExprId,
}

pub struct FnDecl {
    pub ident: Ident,
    pub generics: ThinVec<Ident>,
    pub params: ThinVec<Param>,
    pub ret: Option<TypeId>,
    pub block: Option<BlockId>,
}

pub struct Trait {
    pub ident: Ident,
    pub methods: ThinVec<FnDecl>,
}

pub struct Impl {
    pub generics: ThinVec<Ident>,
    pub ty: TypeId,
    pub methods: ThinVec<ItemId>,
}

pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

pub struct ArraySeg {
    pub expr: ExprId,
    pub repeated: Option<ExprId>,
}

pub enum Lit {
    Unit,
    Bool(bool),
    Int(i64),
    Str(Symbol),
    FStr(ThinVec<ExprId>),
    Char(char),
    Array { segments: ThinVec<ArraySeg> },
}

#[derive(Clone, Copy)]
pub struct BinaryOp {
    pub kind: BinOpKind,
    pub span: Span,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnaryOp {
    Neg,
    Not,
    Ref,
    Deref,
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

impl BinOpKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::Add | Self::AddAssign => "add",
            Self::Sub | Self::SubAssign => "subtract",
            Self::Mul | Self::MulAssign => "multiply",
            Self::Div | Self::DivAssign => "divide",
            Self::Mod | Self::ModAssign => "mod",
            Self::Less | Self::LessEq | Self::Greater | Self::GreaterEq | Self::Neq | Self::Eq => {
                "compare"
            }
            Self::Assign => "assign",
            Self::Range | Self::RangeInclusive => "produce a range of",
            Self::And => "and",
            Self::Or => "or",
        }
    }

    pub fn symbol(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::AddAssign => "+=",
            Self::Div => "/",
            Self::DivAssign => "/=",
            Self::Eq => "==",
            Self::Greater => ">",
            Self::GreaterEq => ">=",
            Self::Less => "<",
            Self::LessEq => "<=",
            Self::Mod => "%",
            Self::ModAssign => "%=",
            Self::Mul => "*",
            Self::MulAssign => "*=",
            Self::Neq => "!=",
            Self::Range => "..",
            Self::RangeInclusive => "..=",
            Self::Sub => "-",
            Self::SubAssign => "-=",
            Self::Assign => "=",
            Self::And => "and",
            Self::Or => "or",
        }
    }
}

impl BinOpKind {
    pub fn is_op_assign(self) -> bool {
        matches!(
            self,
            Self::AddAssign | Self::SubAssign | Self::MulAssign | Self::DivAssign | Self::ModAssign
        )
    }
    pub fn is_arithmetic(self) -> bool {
        matches!(self, Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Mod)
    }
    pub fn is_compare(self) -> bool {
        matches!(self, Self::Less | Self::Greater | Self::LessEq | Self::GreaterEq) || self.is_eq()
    }
    pub fn is_eq(self) -> bool {
        matches!(self, Self::Eq | Self::Neq)
    }
    pub fn is_range(self) -> bool {
        matches!(self, Self::Range | Self::RangeInclusive)
    }
    pub fn is_add(self) -> bool {
        matches!(self, Self::Add | Self::AddAssign)
    }
    pub fn is_logical(self) -> bool {
        matches!(self, Self::And | Self::Or)
    }
}

impl Deref for BinaryOp {
    type Target = BinOpKind;
    fn deref(&self) -> &Self::Target {
        &self.kind
    }
}
