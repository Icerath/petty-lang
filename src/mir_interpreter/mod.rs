use std::{cell::Cell, fmt, ops::Range, rc::Rc};

use arcstr::ArcStr;
use index_vec::IndexSlice;
use thin_vec::ThinVec;

macro_rules! value {
    ($ty:ident, $value: expr) => {{
        ($value).with(|kind| match kind {
            ValueKind::$ty(out) => out.clone(),
            other => unreachable!("Expected {}, found {other:?}", stringify!($ty)),
        })
    }};
}
impl Value {
    fn unwrap_bool(&self) -> bool {
        value!(Bool, self)
    }
    fn unwrap_int(&self) -> i64 {
        value!(Int, self)
    }
    fn unwrap_int_usize(&self) -> usize {
        let int = self.unwrap_int();
        int.try_into().unwrap_or_else(|_| panic!("{int}"))
    }
    fn unwrap_char(&self) -> char {
        value!(Char, self)
    }
    fn unwrap_str(&self) -> ArcStr {
        value!(Str, self)
    }
    fn unwrap_range(&self) -> Range<i64> {
        self.with(|kind| match kind {
            ValueKind::Range(out) => Range::clone(out),
            other => unreachable!("Expected {}, found {other:?}", stringify!($ty)),
        })
    }
    fn unwrap_range_usize(&self) -> Range<usize> {
        let range = self.unwrap_range();
        usize::try_from(range.start).unwrap()..usize::try_from(range.end).unwrap()
    }
    fn unwrap_fn(&self) -> BodyId {
        value!(Fn, self)
    }
    fn unwrap_with_arrayref<T>(&self, f: impl FnOnce(&mut ThinVec<Value>) -> T) -> T {
        self.with(|kind| match kind {
            ValueKind::Array(array) => f(array),
            other => unreachable!("Expected {}, found {other:?}", "array"),
        })
    }
}

use crate::mir::{
    BinaryOp, BlockId, BodyId, Constant, Mir, Operand, Place, RValue, Statement, Terminator,
    UnaryOp,
};

pub fn interpret(mir: &Mir) {
    let Some(main) = mir.main_body else { return };
    let bool = [ValueKind::Bool(false).into(), ValueKind::Bool(true).into()];
    let mut interpreter = Interpreter { mir, unit: ValueKind::Unit.into(), bool };
    interpreter.run(main, vec![]);
}

struct Interpreter<'mir> {
    mir: &'mir Mir,
    unit: Value,
    bool: [Value; 2],
}

impl Interpreter<'_> {
    fn bool(&self, bool: bool) -> Value {
        self.bool[usize::from(bool)].clone()
    }
    fn unit(&self) -> Value {
        self.unit.clone()
    }
}

#[derive(Clone, Debug)]
enum ValueKind {
    Unit,
    Array(ThinVec<Value>),
    Bool(bool),
    Int(i64),
    Range(Box<Range<i64>>),
    Char(char),
    Str(ArcStr),
    Fn(BodyId),
}

impl From<ValueKind> for Value {
    fn from(kind: ValueKind) -> Self {
        Self { ptr: Rc::new(Cell::new(kind)) }
    }
}

#[derive(Clone)]
struct Value {
    ptr: Rc<Cell<ValueKind>>,
}

impl Value {
    fn with<T>(&self, f: impl FnOnce(&mut ValueKind) -> T) -> T {
        let mut kind = self.ptr.replace(ValueKind::Unit);
        let out = f(&mut kind);
        self.ptr.set(kind);
        out
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = self.ptr.replace(ValueKind::Unit);
        let result = kind.fmt(f);
        self.ptr.set(kind);
        result
    }
}

impl Interpreter<'_> {
    fn run(&mut self, body_id: BodyId, args: Vec<Value>) -> Value {
        let body = &self.mir.bodies[body_id];
        let mut block_id = BlockId::from(0);
        let mut places = index_vec::index_vec![self.unit(); body.places.index()];
        for (i, arg) in args.into_iter().enumerate() {
            places[i] = arg;
        }

        loop {
            let block = &body.blocks[block_id];
            for stmt in &block.statements {
                match *stmt {
                    Statement::DerefAssign { place, ref rvalue }
                    | Statement::Assign { place, ref rvalue } => {
                        // let deref = matches!(stmt, Statement::DerefAssign { .. });
                        // assert!(!deref);
                        places[place] = self.rvalue(rvalue, &mut places);
                    }
                }
            }
            match block.terminator {
                Terminator::Goto(block) => block_id = block,
                Terminator::Branch { ref condition, fals, tru } => {
                    let condition = self.operand(condition, &places).unwrap_bool();
                    block_id = if condition { tru } else { fals };
                }
                Terminator::Return(ref operand) => return self.operand(operand, &places),
            };
        }
    }
    fn rvalue(&mut self, rvalue: &RValue, places: &mut IndexSlice<Place, [Value]>) -> Value {
        match rvalue {
            RValue::Abort => panic!("abort"),
            RValue::Use(operand) => self.operand(operand, places),
            RValue::Extend { array, value, repeat } => {
                let value = self.operand(value, places);
                let repeat: usize = self.operand(repeat, places).unwrap_int().try_into().unwrap();
                places[*array]
                    .unwrap_with_arrayref(|array| array.extend(std::iter::repeat_n(value, repeat)));
                self.unit()
            }
            RValue::Call { function, args } => {
                let call_body = self.operand(function, places).unwrap_fn();
                let args = args.iter().map(|arg| self.operand(arg, places)).collect();
                self.run(call_body, args)
            }
            RValue::BinaryExpr { lhs, op, rhs } => {
                let lhs = self.operand(lhs, places);
                let rhs = self.operand(rhs, places);
                match op {
                    BinaryOp::IntAdd => ValueKind::Int(lhs.unwrap_int() + rhs.unwrap_int()).into(),
                    BinaryOp::IntSub => ValueKind::Int(lhs.unwrap_int() - rhs.unwrap_int()).into(),
                    BinaryOp::IntMul => ValueKind::Int(lhs.unwrap_int() * rhs.unwrap_int()).into(),
                    BinaryOp::IntDiv => ValueKind::Int(lhs.unwrap_int() / rhs.unwrap_int()).into(),
                    BinaryOp::IntMod => ValueKind::Int(lhs.unwrap_int() % rhs.unwrap_int()).into(),
                    BinaryOp::IntLess => self.bool(lhs.unwrap_int() < rhs.unwrap_int()),
                    BinaryOp::IntGreater => self.bool(lhs.unwrap_int() > rhs.unwrap_int()),
                    BinaryOp::IntLessEq => self.bool(lhs.unwrap_int() <= rhs.unwrap_int()),
                    BinaryOp::IntGreaterEq => self.bool(lhs.unwrap_int() >= rhs.unwrap_int()),
                    BinaryOp::IntEq => self.bool(lhs.unwrap_int() == rhs.unwrap_int()),
                    BinaryOp::IntNeq => self.bool(lhs.unwrap_int() != rhs.unwrap_int()),
                    BinaryOp::IntRange => {
                        ValueKind::Range(Box::new(lhs.unwrap_int()..rhs.unwrap_int())).into()
                    }
                    BinaryOp::IntRangeInclusive =>
                    {
                        #[expect(clippy::range_plus_one)]
                        ValueKind::Range(Box::new(lhs.unwrap_int()..rhs.unwrap_int() + 1)).into()
                    }

                    BinaryOp::CharEq => self.bool(lhs.unwrap_char() == rhs.unwrap_char()),
                    BinaryOp::CharNeq => self.bool(lhs.unwrap_char() != rhs.unwrap_char()),

                    BinaryOp::StrEq => self.bool(lhs.unwrap_str() == rhs.unwrap_str()),
                    BinaryOp::StrNeq => self.bool(lhs.unwrap_str() != rhs.unwrap_str()),
                    BinaryOp::StrIndex => {
                        ValueKind::Char(lhs.unwrap_str().as_bytes()[rhs.unwrap_int_usize()] as char)
                            .into()
                    }
                    BinaryOp::StrIndexSlice => {
                        ValueKind::Str(lhs.unwrap_str()[rhs.unwrap_range_usize()].into()).into()
                    }
                    BinaryOp::StrFind => ValueKind::Int(
                        lhs.unwrap_str()
                            .find(rhs.unwrap_str().as_str())
                            .unwrap()
                            .try_into()
                            .unwrap(),
                    )
                    .into(),
                    BinaryOp::StrRFind => ValueKind::Int(
                        lhs.unwrap_str()
                            .rfind(rhs.unwrap_str().as_str())
                            .unwrap()
                            .try_into()
                            .unwrap(),
                    )
                    .into(),
                    BinaryOp::ArrayIndexRange => todo!(),
                    BinaryOp::ArrayIndexRef | BinaryOp::ArrayIndex => {
                        let index = rhs.unwrap_int_usize();
                        lhs.unwrap_with_arrayref(|array| array[index].clone())
                    }
                }
            }
            RValue::UnaryExpr { op, operand } => {
                let operand = self.operand(operand, places);
                match op {
                    UnaryOp::BoolNot => self.bool(!operand.unwrap_bool()),
                    UnaryOp::IntNeg => ValueKind::Int(-operand.unwrap_int()).into(),
                    UnaryOp::IntToStr => {
                        ValueKind::Str(operand.unwrap_int().to_string().into()).into()
                    }
                    UnaryOp::StrPrint => {
                        println!("{}", operand.unwrap_str());
                        self.unit()
                    }
                    UnaryOp::StrLen => {
                        ValueKind::Int(operand.unwrap_str().len().try_into().unwrap()).into()
                    }
                }
            }
        }
    }

    fn operand(&self, operand: &Operand, places: &IndexSlice<Place, [Value]>) -> Value {
        match *operand {
            Operand::Constant(ref constant) => match *constant {
                Constant::Unit => self.unit(),
                Constant::EmptyArray => ValueKind::Array(ThinVec::default()).into(),
                Constant::Bool(bool) => self.bool(bool),
                Constant::Int(int) => ValueKind::Int(int).into(),
                Constant::Char(char) => ValueKind::Char(char).into(),
                Constant::Str(str) => ValueKind::Str(str.as_str().into()).into(),
                Constant::Func(body) => ValueKind::Fn(body).into(),
            },
            Operand::Deref(_place) => todo!(),
            Operand::Place(place) => places[place].clone(),
        }
    }
}
