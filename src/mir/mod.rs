mod display;
mod with_places;

use std::ops::Range;

use arcstr::ArcStr;
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
    ConstantIndex(u32),
}

impl BlockId {
    pub const PLACEHOLDER: Self = Self { _raw: u16::MAX };

    pub fn complete(&mut self, new: Self) {
        if *self == Self::PLACEHOLDER {
            *self = new;
        }
    }
}

#[derive(Default, Debug)]
pub struct Mir {
    pub bodies: IndexVec<BodyId, Body>,
    pub main_body: Option<BodyId>,
}

#[derive(Debug, Hash)]
pub struct Body {
    pub name: Option<Symbol>,
    pub auto: bool,
    pub blocks: IndexVec<BlockId, Block>,
    pub params: usize,
    pub locals: Local,
}

impl Body {
    pub fn new(name: Option<Symbol>, params: usize) -> Self {
        Self { name, blocks: IndexVec::default(), params, locals: params.into(), auto: false }
    }
    pub fn with_auto(mut self, auto: bool) -> Self {
        self.auto = auto;
        self
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
    Abort { msg: Symbol },
    Unreachable,
}

impl Terminator {
    pub fn complete(&mut self, block: BlockId) {
        match self {
            Self::Abort { .. } | Self::Unreachable | Self::Return(..) => {}
            Self::Goto(placeholder) => placeholder.complete(block),
            Self::Branch { fals, tru, .. } => _ = (fals.complete(block), tru.complete(block)),
        }
    }
    pub fn with_operands_mut(&mut self, f: &mut impl FnMut(&mut Operand)) {
        match self {
            Self::Branch { condition: operand, .. } | Self::Return(operand) => f(operand),
            Self::Goto(..) | Self::Abort { .. } | Self::Unreachable => {}
        }
    }
    pub fn mutates_local(&self, local: Local) -> bool {
        match self {
            Self::Return(operand) | Self::Branch { condition: operand, .. } => {
                operand.mutates_local(local)
            }
            Self::Goto(..) | Self::Abort { .. } | Self::Unreachable => false,
        }
    }
    pub fn mentions_place(&self, place: &Place) -> bool {
        match self {
            Self::Abort { .. } | Self::Goto(..) | Self::Unreachable => false,
            Self::Branch { condition, .. } => condition.mentions_place(place),
            Self::Return(operand) => operand.mentions_place(place),
        }
    }
    pub fn with_jumps(&self, mut f: impl FnMut(BlockId)) {
        match *self {
            Self::Abort { .. } | Self::Return(..) | Self::Unreachable => {}
            Self::Goto(jump) => f(jump),
            Self::Branch { fals, tru, .. } => {
                f(fals);
                f(tru);
            }
        }
    }
    pub fn with_jumps_mut(&mut self, mut f: impl FnMut(&mut BlockId)) {
        match self {
            Self::Abort { .. } | Self::Return(..) | Self::Unreachable => {}
            Self::Goto(jump) => f(jump),
            Self::Branch { fals, tru, .. } => {
                f(fals);
                f(tru);
            }
        }
    }
}

#[derive(Debug, Hash, Clone)]
pub enum Statement {
    Assign { place: Place, rvalue: RValue },
}

#[must_use]
#[derive(Debug, Hash, Clone)]
pub enum RValue {
    Use(Operand),
    Binary { lhs: Operand, op: BinaryOp, rhs: Operand },
    Unary { op: UnaryOp, operand: Operand },
    Call { function: Operand, args: ThinVec<Operand> },
    BuildArray(Vec<(Operand, Option<Operand>)>),
    StrJoin(Vec<Operand>),
}

impl RValue {
    pub const UNIT: Self = Self::Use(Operand::UNIT);

    pub fn local(local: Local) -> Self {
        Self::Use(Operand::local(local))
    }

    pub fn side_effect(&self) -> bool {
        match self {
            Self::StrJoin(..) | Self::BuildArray(..) | Self::Use(..) => false,
            Self::Binary { op, .. } => op.side_effect(),
            Self::Unary { op, .. } => op.side_effect(),
            Self::Call { .. } => true,
        }
    }
}

#[derive(Debug, Clone, Hash)]
pub enum Operand {
    Constant(Constant),
    Ref(Place),
    Place(Place),
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
    EmptyArray { cap: usize },
    UninitStruct { size: u32 },
    Bool(bool),
    Int(i64),
    Range(Range<i64>),
    Char(char),
    Str(ArcStr),
    Func(BodyId),
}

#[derive(Debug, PartialEq, PartialOrd, Eq, Hash, Clone, Copy)]
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
    StrAdd,
    StrFind,
    StrRFind,
    StrIndex,
    StrIndexSlice,

    ArrayIndexRange,
    ArrayPush,
}

impl BinaryOp {
    pub fn side_effect(self) -> bool {
        matches!(self, Self::ArrayPush)
    }
}

#[derive(Debug, Clone, Copy, Hash)]
pub enum UnaryOp {
    BoolNot,
    BoolToStr,

    IntToStr,
    IntNeg,
    Chr,

    Ord,
    CharToStr,

    StrLen,
    Print,

    ArrayLen,
    StrJoin,

    RangeToStr,
    RangeStart,
    RangeEnd,

    ArrayPop,
    ArrayStrFmt,
}

impl UnaryOp {
    pub fn side_effect(self) -> bool {
        matches!(self, Self::Print | Self::ArrayPop)
    }
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
            Self::StrJoin(operands) => operands.iter().any(|o| o.mentions_place(place)),
            Self::Binary { lhs, rhs, .. } => lhs.mentions_place(place) || rhs.mentions_place(place),
            Self::Call { function, args } => {
                function.mentions_place(place) || args.iter().any(|arg| arg.mentions_place(place))
            }
            Self::Use(operand) | Self::Unary { operand, .. } => operand.mentions_place(place),
            Self::BuildArray(segments) => segments.iter().any(|(elem, repeat)| {
                elem.mentions_place(place)
                    || repeat.as_ref().is_some_and(|repeat| repeat.mentions_place(place))
            }),
        }
    }
    // could this rvalue potentially mutate local
    pub fn mutates_local(&self, local: Local) -> bool {
        match self {
            Self::StrJoin(operands) => operands.iter().any(|o| o.mutates_local(local)),
            Self::BuildArray(segments) => segments.iter().any(|(elem, repeat)| {
                elem.mutates_local(local)
                    || repeat.as_ref().is_some_and(|repeat| repeat.mutates_local(local))
            }),
            Self::Binary { lhs, rhs, .. } => lhs.mutates_local(local) || rhs.mutates_local(local),
            Self::Unary { operand, .. } | Self::Use(operand) => operand.mutates_local(local),
            Self::Call { function, args } => {
                function.mutates_local(local) || args.iter().any(|arg| arg.mutates_local(local))
            }
        }
    }

    pub fn with_operands_mut(&mut self, f: &mut impl FnMut(&mut Operand)) {
        match self {
            Self::StrJoin(operands) => operands.iter_mut().for_each(f),
            Self::BuildArray(arr) => {
                for (elem, repeat) in arr {
                    f(elem);
                    if let Some(repeat) = repeat {
                        f(repeat);
                    }
                }
            }
            Self::Unary { operand, .. } | Self::Use(operand) => f(operand),
            Self::Binary { lhs, rhs, .. } => {
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
            Self::Constant(..) => false,
        }
    }
    pub fn mutates_local(&self, local: Local) -> bool {
        match self {
            Self::Ref(place) => place.local == local,
            _ => false,
        }
    }
}

impl From<Operand> for RValue {
    fn from(operand: Operand) -> Self {
        Self::Use(operand)
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

impl From<Constant> for Operand {
    fn from(value: Constant) -> Self {
        Self::Constant(value)
    }
}
