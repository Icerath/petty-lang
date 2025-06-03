mod display;

use std::{fmt, ops::Deref};

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{define_id, span::Span, symbol::Symbol};

#[derive(Default)]
pub struct Ast {
    pub exprs: IndexVec<ExprId, Expr>,
    pub blocks: IndexVec<BlockId, Block>,
    pub types: IndexVec<TypeId, Ty>,
    pub root: Module,
}

define_id!(pub ExprId);
define_id!(pub BlockId);
define_id!(pub TypeId);

impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.root.fmt(f)
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

#[derive(Debug, Clone, Copy)]
pub struct Identifier {
    pub symbol: Symbol,
    pub span: Span,
}

#[derive(Debug)]
pub struct Param {
    pub ident: Identifier,
    pub ty: Option<TypeId>,
}

#[derive(Debug)]
pub struct Field {
    pub ident: Identifier,
    pub ty: TypeId,
}

#[derive(Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind {
    Never,
    Unit,
    Name { ident: Identifier, generics: ThinVec<TypeId> },
    Array(TypeId),
    Func { params: ThinVec<TypeId>, ret: Option<TypeId> },
    Ref(TypeId),
}

#[derive(Debug, Default)]
pub struct Module {
    pub name: Option<Symbol>,
    pub items: Vec<ExprId>,
}

#[derive(Debug)]
pub enum ExprKind {
    Unreachable,
    Module(Module),
    Binary { lhs: ExprId, op: BinaryOp, rhs: ExprId },
    Unary { op: UnaryOp, expr: ExprId },
    FnCall { function: ExprId, args: ThinVec<ExprId> },
    MethodCall { expr: ExprId, method: Identifier, args: ThinVec<ExprId> },
    Ident(Symbol),
    Index { expr: ExprId, index: ExprId },
    FieldAccess { expr: ExprId, field: Identifier },
    Lit(Lit),
    Block(BlockId),
    Let { ident: Identifier, ty: Option<TypeId>, expr: ExprId },
    Const { ident: Identifier, ty: Option<TypeId>, expr: ExprId },
    While { condition: ExprId, block: BlockId },
    For { ident: Identifier, iter: ExprId, body: BlockId },
    If { arms: ThinVec<IfStmt>, els: Option<BlockId> },
    Match { scrutinee: ExprId, arms: ThinVec<MatchArm> },
    Is { scrutinee: ExprId, pat: Pat },
    Return(Option<ExprId>),
    Assert(ExprId),
    Break,
    Continue,
    Trait(Trait),
    Impl(Impl),
    FnDecl(FnDecl),
    Struct { ident: Identifier, generics: ThinVec<Identifier>, fields: ThinVec<Field> },
}

#[derive(Debug)]
pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum PatKind {
    Bool(bool),
    Int(i64),
    Str(Symbol),
    Expr(BlockId),
    If(ExprId),
    Or(ThinVec<Pat>),
    And(ThinVec<Pat>),
    Ident(Symbol),
    Struct(Identifier, ThinVec<PatArg>),
    Array(ThinVec<Pat>),
}

#[derive(Debug)]
pub struct PatArg {
    pub ident: Identifier,
    pub pat: Pat,
}

#[derive(Debug)]
pub struct MatchArm {
    pub pat: Pat,
    pub body: ExprId,
}

#[derive(Debug)]
pub struct FnDecl {
    pub ident: Identifier,
    pub generics: ThinVec<Identifier>,
    pub params: ThinVec<Param>,
    pub ret: Option<TypeId>,
    pub block: Option<BlockId>,
}

#[derive(Debug)]
pub struct Trait {
    pub ident: Identifier,
    pub methods: ThinVec<FnDecl>,
}

#[derive(Debug)]
pub struct Impl {
    pub generics: ThinVec<Identifier>,
    pub ty: TypeId,
    pub methods: ThinVec<ExprId>,
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
    FStr(ThinVec<ExprId>),
    Char(char),
    Array { segments: ThinVec<ArraySeg> },
}

#[derive(Debug, Clone, Copy)]
pub struct BinaryOp {
    pub kind: BinOpKind,
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
