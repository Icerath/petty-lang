#![expect(dead_code)]

mod display;

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::symbol::Symbol;

index_vec::define_index_type! {
    pub struct BodyId = u32;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

index_vec::define_index_type! {
    pub struct BlockId = u16;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

index_vec::define_index_type! {
    #[derive(Default)]
    pub struct Place = u16;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

impl BlockId {
    pub const PLACEHOLDER: Self = Self { _raw: u16::MAX };
}

#[derive(Default, Debug)]
pub struct Mir {
    pub bodies: IndexVec<BodyId, Body>,
}

#[derive(Debug)]
pub struct Body {
    pub blocks: IndexVec<BlockId, Block>,
    pub places: Place,
}

impl Body {
    pub fn new(num_params: usize) -> Self {
        Self { blocks: IndexVec::default(), places: num_params.into() }
    }
    pub fn new_place(&mut self) -> Place {
        self.places += 1;
        self.places - 1
    }
}
#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Terminator {
    Goto(BlockId),
    Branch { condition: Operand, fals: BlockId, tru: BlockId },
    Return(Operand),
}

#[derive(Debug)]
pub enum Statement {
    Assign { place: Place, rvalue: RValue },
    DerefAssign { place: Place, rvalue: RValue },
}

#[derive(Debug)]
pub enum RValue {
    Extend { array: Place, value: Operand, repeat: Operand },
    Index { indexee: Operand, index: Operand },
    IndexRef { indexee: Operand, index: Operand },
    Abort,
    Use(Operand),
    BinaryExpr { lhs: Operand, op: BinaryOp, rhs: Operand },
    UnaryExpr { op: UnaryOp, operand: Operand },
    Call { function: Operand, args: ThinVec<Operand> },
    Instrinsic(Instrinsic),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Operand {
    Constant(Constant),
    Place(Place),
    Deref(Place),
}

impl Operand {
    pub const UNIT: Self = Self::Constant(Constant::Unit);

    // returns an operand to read to nth argument, used in intrinsics
    pub fn arg(nth: usize) -> Self {
        Self::Place(nth.into())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Constant {
    Unit,
    EmptyArray,
    Bool(bool),
    Int(i64),
    Char(char),
    Str(Symbol),
    Func(BodyId),
}

pub type BinaryOp = crate::hir::BinaryOp;

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug)]
pub enum Instrinsic {
    Strlen(Operand),
    StrFind(Operand, Operand),
    StrRFind(Operand, Operand),
    IntToStr(Operand),
    PrintStr(Operand),
}
