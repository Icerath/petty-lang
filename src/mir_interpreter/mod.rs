mod array;
mod value;

use std::{io::Write, ops::Range};

use arcstr::ArcStr;
use array::Array;
use index_vec::{IndexSlice, IndexVec};
use value::Allocation;
pub use value::Value;

use crate::mir::{
    BinaryOp, BlockId, BodyId, Constant, Local, Mir, Operand, Place, Projection, RValue, Statement,
    Terminator, UnaryOp,
};

type Places = IndexSlice<Local, [Allocation]>;

pub fn interpret(mir: &Mir, w: &mut dyn Write) {
    let Some(main) = mir.main_body else { return };
    let mut interpreter = Interpreter { mir, allocs: vec![], w };
    interpreter.run(main, vec![]);
}

struct Interpreter<'mir, 'w> {
    mir: &'mir Mir,
    allocs: Vec<Allocation>,
    w: &'w mut dyn Write,
}

impl Interpreter<'_, '_> {
    pub fn alloc_locals(&mut self, size: usize) -> IndexVec<Local, Allocation> {
        std::iter::repeat_with(|| {
            self.allocs.pop().unwrap_or_else(|| Allocation::from(Value::Unit))
        })
        .take(size)
        .collect()
    }

    pub fn dealloc_locals(&mut self, stack: IndexVec<Local, Allocation>) {
        for alloc in stack.into_iter().rev() {
            if alloc.count() == 1 {
                self.allocs.push(alloc);
            }
        }
    }

    fn run(&mut self, body_id: BodyId, args: Vec<Value>) -> Value {
        let body = &self.mir.bodies[body_id];
        let mut block_id = BlockId::from(0);
        let locals = self.alloc_locals(body.locals.index());
        for (i, arg) in args.into_iter().enumerate() {
            *locals[i].borrow() = arg;
        }
        let output = loop {
            let block = &body.blocks[block_id];
            for stmt in &block.statements {
                let Statement::Assign { place, rvalue } = stmt;
                let rvalue = self.rvalue(rvalue, &locals);
                let alloc = self.load_place(place, &locals);
                *alloc.borrow() = rvalue;
            }
            match block.terminator {
                Terminator::Unreachable => unreachable!(),
                Terminator::Abort { msg } => panic!("{}", msg),
                Terminator::Goto(block) => block_id = block,
                Terminator::Branch { ref condition, fals, tru } => {
                    let condition = self.operand(condition, &locals).unwrap_bool();
                    block_id = if condition { tru } else { fals };
                }
                Terminator::Return(ref operand) => break self.operand(operand, &locals),
            }
        };
        self.dealloc_locals(locals);
        output
    }
    #[allow(clippy::too_many_lines)]
    fn rvalue(&mut self, rvalue: &RValue, locals: &Places) -> Value {
        match rvalue {
            RValue::StrJoin(segments) => {
                let mut s = String::new();
                for seg in segments {
                    s.push_str(self.operand(seg, locals).unwrap_str());
                }
                Value::Str(s.into())
            }
            RValue::BuildArray(segments) => {
                let array = Array::default();
                for (elem, repeat) in segments {
                    let elem = self.operand(elem, locals);
                    let repeat = repeat
                        .as_ref()
                        .map_or(1, |repeat| self.operand(repeat, locals).unwrap_int_usize());
                    array.extend(elem, repeat);
                }
                Value::Array(array)
            }
            RValue::Use(operand) => self.operand(operand, locals),
            RValue::Call { function, args } => {
                let call_body = self.operand(function, locals).unwrap_fn();
                let args = args.iter().map(|arg| self.operand(arg, locals)).collect();
                self.run(call_body, args)
            }
            RValue::Binary { lhs, op, rhs } => {
                let lhs = self.operand(lhs, locals);
                let rhs = self.operand(rhs, locals);
                binary_op(lhs, *op, rhs)
            }
            RValue::Unary { op, operand } => unary_op(*op, self.operand(operand, locals), self.w),
        }
    }

    fn operand(&self, operand: &Operand, locals: &Places) -> Value {
        match operand {
            Operand::Ref(place) => Value::Ref(self.load_place(place, locals)),
            Operand::Constant(constant) => const_value(constant),
            Operand::Place(place) => self.load_place(place, locals).clone_raw(),
        }
    }

    #[expect(clippy::unused_self)]
    fn load_place(&self, place: &Place, locals: &Places) -> Allocation {
        let mut alloc = locals[place.local].clone();
        for projection in &place.projections {
            alloc = match *projection {
                Projection::Deref => alloc.borrow().unwrap_ref().clone(),
                Projection::Field(field) => alloc.borrow().unwrap_struct()[field as usize].clone(),
                Projection::Index(index) => {
                    let index = locals[index].borrow().unwrap_int_usize();
                    alloc.borrow().unwrap_array().get(index).unwrap().clone()
                }
                Projection::ConstantIndex(index) => {
                    alloc.borrow().unwrap_array().get(index as _).unwrap().clone()
                }
            };
        }
        alloc
    }
}

#[expect(clippy::needless_pass_by_value)]
pub fn unary_op(op: UnaryOp, operand: Value, w: &mut dyn Write) -> Value {
    match op {
        UnaryOp::ArrayStrFmt => {
            let mut string = String::new();
            string.push('[');
            let array = operand.unwrap_array();
            for i in 0..array.len() {
                if i != 0 {
                    string.push_str(", ");
                }
                string.push_str(array.get(i).unwrap().borrow().unwrap_str());
            }
            string.push(']');
            Value::Str(string.into())
        }
        UnaryOp::StrJoin => {
            let mut string = String::new();
            let array = operand.unwrap_array();
            array.for_each(|value| string.push_str(value.clone_raw().unwrap_str()));
            Value::Str(string.into())
        }
        UnaryOp::ArrayLen => Value::Int(operand.unwrap_ref_array().len().try_into().unwrap()),
        UnaryOp::ArrayPop => operand.unwrap_ref_array().pop(),

        UnaryOp::BoolNot => Value::Bool(!operand.unwrap_bool()),
        UnaryOp::BoolToStr => Value::Str(bool_to_str(operand.unwrap_bool())),

        UnaryOp::IntNeg => Value::Int(-operand.unwrap_int()),
        UnaryOp::IntToStr => Value::Str(operand.unwrap_int().to_string().into()),
        UnaryOp::Chr => Value::Char(u8::try_from(operand.unwrap_int()).unwrap() as char),

        UnaryOp::Ord => Value::Int(i64::from(u32::from(operand.unwrap_char()))),
        UnaryOp::CharToStr => Value::Str(operand.unwrap_char().to_string().into()),

        UnaryOp::Print => {
            _ = write!(w, "{}", operand.unwrap_str());
            Value::Unit
        }
        UnaryOp::StrLen => Value::Int(operand.unwrap_str().len().try_into().unwrap()),

        UnaryOp::RangeToStr => {
            let Range { start, end } = operand.unwrap_range();
            Value::Str(arcstr::format!("{start}..{end}"))
        }
        UnaryOp::RangeStart => Value::Int(operand.unwrap_range().start),
        UnaryOp::RangeEnd => Value::Int(operand.unwrap_range().end),
    }
}

fn bool_to_str(bool: bool) -> ArcStr {
    if bool { arcstr::literal!("true") } else { arcstr::literal!("false") }
}

#[expect(clippy::needless_pass_by_value)]
pub fn binary_op(lhs: Value, op: BinaryOp, rhs: Value) -> Value {
    match op {
        BinaryOp::BoolEq => Value::Bool(lhs.unwrap_bool() == rhs.unwrap_bool()),
        BinaryOp::BoolNeq => Value::Bool(lhs.unwrap_bool() != rhs.unwrap_bool()),
        BinaryOp::BoolAnd => Value::Bool(lhs.unwrap_bool() && rhs.unwrap_bool()),

        BinaryOp::IntAdd => Value::Int(lhs.unwrap_int() + rhs.unwrap_int()),
        BinaryOp::IntSub => Value::Int(lhs.unwrap_int() - rhs.unwrap_int()),
        BinaryOp::IntMul => Value::Int(lhs.unwrap_int() * rhs.unwrap_int()),
        BinaryOp::IntDiv => Value::Int(lhs.unwrap_int() / rhs.unwrap_int()),
        BinaryOp::IntMod => Value::Int(lhs.unwrap_int() % rhs.unwrap_int()),
        BinaryOp::IntLess => Value::Bool(lhs.unwrap_int() < rhs.unwrap_int()),
        BinaryOp::IntGreater => Value::Bool(lhs.unwrap_int() > rhs.unwrap_int()),
        BinaryOp::IntLessEq => Value::Bool(lhs.unwrap_int() <= rhs.unwrap_int()),
        BinaryOp::IntGreaterEq => Value::Bool(lhs.unwrap_int() >= rhs.unwrap_int()),
        BinaryOp::IntEq => Value::Bool(lhs.unwrap_int() == rhs.unwrap_int()),
        BinaryOp::IntNeq => Value::Bool(lhs.unwrap_int() != rhs.unwrap_int()),
        BinaryOp::IntRange => Value::Range(Box::new(lhs.unwrap_int()..rhs.unwrap_int())),
        BinaryOp::IntRangeInclusive =>
        {
            #[expect(clippy::range_plus_one)]
            Value::Range(Box::new(lhs.unwrap_int()..rhs.unwrap_int() + 1))
        }

        BinaryOp::CharEq => Value::Bool(lhs.unwrap_char() == rhs.unwrap_char()),
        BinaryOp::CharNeq => Value::Bool(lhs.unwrap_char() != rhs.unwrap_char()),

        BinaryOp::StrEq => Value::Bool(lhs.unwrap_str() == rhs.unwrap_str()),
        BinaryOp::StrNeq => Value::Bool(lhs.unwrap_str() != rhs.unwrap_str()),
        BinaryOp::StrAdd => Value::Str((lhs.unwrap_str().to_string() + rhs.unwrap_str()).into()),
        BinaryOp::StrIndex => {
            Value::Char(lhs.unwrap_str().as_bytes()[rhs.unwrap_int_usize()] as char)
        }
        BinaryOp::StrIndexSlice => Value::Str(lhs.unwrap_str()[rhs.unwrap_range_usize()].into()),
        BinaryOp::StrFind => Value::Int(
            lhs.unwrap_str().find(rhs.unwrap_str().as_str()).unwrap().try_into().unwrap(),
        ),
        BinaryOp::StrRFind => Value::Int(
            lhs.unwrap_str().rfind(rhs.unwrap_str().as_str()).unwrap().try_into().unwrap(),
        ),
        BinaryOp::ArrayIndexRange => todo!(),
        BinaryOp::ArrayPush => lhs.unwrap_ref_array().push(rhs).into(),
    }
}

pub fn const_value(constant: &Constant) -> Value {
    match *constant {
        Constant::UninitStruct { size } => Value::Struct(
            std::iter::repeat_with(|| Allocation::from(Value::Unit)).take(size as _).collect(),
        ),
        Constant::Unit => Value::Unit,
        Constant::EmptyArray { cap } => Value::Array(Array::with_capacity(cap)),
        Constant::Bool(bool) => Value::Bool(bool),
        Constant::Int(int) => Value::Int(int),
        Constant::Range(ref range) => Value::Range(Box::new(range.clone())),
        Constant::Char(char) => Value::Char(char),
        Constant::Str(ref str) => Value::Str(str.clone()),
        Constant::Func(body) => Value::Fn(body),
    }
}
