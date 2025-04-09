mod display;
mod with_places;

use index_vec::IndexVec;
use thin_vec::ThinVec;

use crate::{define_id, symbol::Symbol};

define_id!(pub BodyId);
define_id!(pub BlockId = u16);
define_id!(pub Local = u16);

#[derive(Debug, Clone, Hash)]
pub struct Place {
    pub local: Local,
    pub projections: Vec<Projection>,
}

impl Place {
    pub fn local(local: Local) -> Self {
        Self { local, projections: vec![] }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Projection {
    Deref,
    Field(u32),
    Index(Local),
}

impl BlockId {
    pub const PLACEHOLDER: Self = Self { _raw: u16::MAX };
}

#[derive(Default, Debug)]
pub struct Mir {
    pub bodies: IndexVec<BodyId, Body>,
    pub main_body: Option<BodyId>,
    pub num_intrinsics: usize,
}

#[derive(Debug, Hash)]
pub struct Body {
    pub blocks: IndexVec<BlockId, Block>,
    pub params: usize,
    pub locals: Local,
}

impl Body {
    pub fn new(params: usize) -> Self {
        Self { blocks: IndexVec::default(), params, locals: params.into() }
    }
    pub fn new_local(&mut self) -> Local {
        self.locals += 1;
        self.locals - 1
    }
}
#[derive(Debug, Hash)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone, Hash)]
pub enum Terminator {
    Goto(BlockId),
    Branch { condition: Operand, fals: BlockId, tru: BlockId },
    Return(Operand),
    Abort,
}

impl Terminator {
    pub fn with_operands_mut(&mut self, f: &mut impl FnMut(&mut Operand)) {
        match self {
            Self::Branch { condition: operand, .. } | Self::Return(operand) => f(operand),
            Self::Goto(..) | Self::Abort => {}
        }
    }
    pub fn mutates_local(&self, local: Local) -> bool {
        match self {
            Self::Return(operand) | Self::Branch { condition: operand, .. } => {
                operand.mutates_local(local)
            }
            Self::Goto(..) | Self::Abort => false,
        }
    }
    pub fn mentions_place(&self, place: &Place) -> bool {
        match self {
            Self::Abort | Self::Goto(..) => false,
            Self::Branch { condition, .. } => condition.mentions_place(place),
            Self::Return(operand) => operand.mentions_place(place),
        }
    }
    pub fn with_jumps(&self, mut f: impl FnMut(BlockId)) {
        match *self {
            Self::Abort | Self::Return(..) => {}
            Self::Goto(jump) => f(jump),
            Self::Branch { fals, tru, .. } => {
                f(fals);
                f(tru);
            }
        }
    }
    pub fn with_jumps_mut(&mut self, mut f: impl FnMut(&mut BlockId)) {
        match self {
            Self::Abort | Self::Return(..) => {}
            Self::Goto(jump) => f(jump),
            Self::Branch { fals, tru, .. } => {
                f(fals);
                f(tru);
            }
        }
    }
}

#[derive(Debug, Hash)]
pub enum Statement {
    Assign { place: Place, rvalue: RValue },
}

#[must_use]
#[derive(Debug, Hash)]
pub enum RValue {
    Extend { array: Local, value: Operand, repeat: Operand },
    Use(Operand),
    BinaryExpr { lhs: Operand, op: BinaryOp, rhs: Operand },
    UnaryExpr { op: UnaryOp, operand: Operand },
    Call { function: Operand, args: ThinVec<Operand> },
}

impl RValue {
    pub fn local(local: Local) -> Self {
        Self::Use(Operand::local(local))
    }
    pub fn is_unreachable(&self) -> bool {
        matches!(self, Self::Use(Operand::Unreachable))
    }
}

#[derive(Debug, Clone, Hash)]
pub enum Operand {
    Constant(Constant),
    Ref(Place),
    Place(Place),
    Unreachable,
}

impl Operand {
    pub const UNIT: Self = Self::Constant(Constant::Unit);

    pub fn local(local: Local) -> Self {
        Self::Place(Place::local(local))
    }

    // returns an operand to read to nth argument, used in intrinsics
    pub fn arg(nth: usize) -> Self {
        Self::local(nth.into())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Constant {
    Unit,
    EmptyArray,
    UninitStruct { size: u32 },
    Bool(bool),
    Int(i64),
    Char(char),
    Str(Symbol),
    Func(BodyId),
}

#[derive(Debug, PartialEq, PartialOrd, Hash, Clone, Copy)]
pub enum BinaryOp {
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,
    IntLess,
    IntGreater,
    IntLessEq,
    IntGreaterEq,
    IntEq,
    IntNeq,
    IntRange,
    IntRangeInclusive,

    CharEq,
    CharNeq,

    StrEq,
    StrNeq,
    StrFind,
    StrRFind,
    StrIndex,
    StrIndexSlice,

    ArrayIndexRange,
    ArrayPush,
    ArrayPop,
}

#[derive(Debug, Clone, Copy, Hash)]
pub enum UnaryOp {
    BoolNot,

    IntToStr,
    IntNeg,

    Chr,
    PrintChar,

    StrLen,
    StrPrint,

    ArrayLen,
    StrJoin,

    Deref,
}

impl Statement {
    pub fn rvalue(&self) -> &RValue {
        match self {
            Self::Assign { rvalue, .. } => rvalue,
        }
    }
    pub fn rvalue_mut(&mut self) -> &mut RValue {
        match self {
            Self::Assign { rvalue, .. } => rvalue,
        }
    }
}

impl RValue {
    pub fn mentions_place(&self, place: &Place) -> bool {
        match self {
            Self::BinaryExpr { lhs, rhs, .. } => {
                lhs.mentions_place(place) || rhs.mentions_place(place)
            }
            Self::Call { function, args } => {
                function.mentions_place(place) || args.iter().any(|arg| arg.mentions_place(place))
            }
            Self::Use(operand) | Self::UnaryExpr { operand, .. } => operand.mentions_place(place),
            Self::Extend { array, value, repeat } => {
                *array == place.local || value.mentions_place(place) || repeat.mentions_place(place)
            }
        }
    }
    // could this rvalue potentially mutate local
    pub fn mutates_local(&self, local: Local) -> bool {
        match self {
            Self::BinaryExpr { lhs, rhs, .. } => {
                lhs.mutates_local(local) || rhs.mutates_local(local)
            }
            Self::UnaryExpr { operand, .. } | Self::Use(operand) => operand.mutates_local(local),
            Self::Extend { array, value, repeat } => {
                *array == local || value.mutates_local(local) || repeat.mutates_local(local)
            }
            Self::Call { function, args } => {
                function.mutates_local(local) || args.iter().any(|arg| arg.mutates_local(local))
            }
        }
    }

    pub fn with_operands_mut(&mut self, f: &mut impl FnMut(&mut Operand)) {
        match self {
            Self::UnaryExpr { operand, .. } | Self::Use(operand) => f(operand),
            Self::Extend { value, repeat, .. } => {
                f(value);
                f(repeat);
            }
            Self::BinaryExpr { lhs, rhs, .. } => {
                f(lhs);
                f(rhs);
            }
            Self::Call { function, args } => {
                f(function);
                args.iter_mut().for_each(f);
            }
        }
    }
}

impl Operand {
    pub fn mentions_place(&self, target: &Place) -> bool {
        // FIXME: This seems iffy.
        match self {
            Self::Ref(place) | Self::Place(place) => target.local == place.local,
            _ => false,
        }
    }
    pub fn mutates_local(&self, local: Local) -> bool {
        match self {
            Self::Ref(place) => place.local == local,
            _ => false,
        }
    }
}

impl From<Constant> for RValue {
    fn from(value: Constant) -> Self {
        Self::Use(Operand::Constant(value))
    }
}

impl From<Local> for Place {
    fn from(local: Local) -> Self {
        Self::local(local)
    }
}
