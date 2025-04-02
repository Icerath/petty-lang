mod array;
mod value;

use std::io::{self, Write};

use array::Array;
use index_vec::IndexSlice;
use value::{Allocation, Value};

use crate::mir::{
    BinaryOp, BlockId, BodyId, Constant, Mir, Operand, Place, RValue, Statement, Terminator,
    UnaryOp,
};

pub fn interpret(mir: &Mir) {
    let Some(main) = mir.main_body else { return };
    let mut interpreter = Interpreter { mir, unit: Value::Unit.into() };
    interpreter.run(main, vec![]);
}

struct Interpreter<'mir> {
    mir: &'mir Mir,
    unit: Allocation,
}

impl Interpreter<'_> {
    fn unit(&self) -> Allocation {
        self.unit.clone()
    }
    fn run(&mut self, body_id: BodyId, args: Vec<Value>) -> Value {
        let body = &self.mir.bodies[body_id];
        let mut block_id = BlockId::from(0);
        let mut places = index_vec::index_vec![self.unit(); body.places.index()];
        for (i, arg) in args.into_iter().enumerate() {
            places[i] = arg.into();
        }
        loop {
            let block = &body.blocks[block_id];
            for stmt in &block.statements {
                match *stmt {
                    Statement::Assign { place, deref, ref rvalue } => {
                        let rvalue = self.rvalue(rvalue, &mut places);
                        if deref {
                            match &*places[place].borrow() {
                                Value::Ref(value) => *value.borrow() = rvalue,
                                _ => unreachable!(),
                            }
                        } else {
                            places[place] = rvalue.into();
                        }
                    }
                }
            }
            match block.terminator {
                #[cfg(test)]
                Terminator::Abort => std::panic::panic_any("assertion failed"),
                #[cfg(not(test))]
                Terminator::Abort => std::process::exit(1),
                Terminator::Goto(block) => block_id = block,
                Terminator::Branch { ref condition, fals, tru } => {
                    let condition = Self::operand(condition, &places).unwrap_bool();
                    block_id = if condition { tru } else { fals };
                }
                Terminator::Return(ref operand) => return Self::operand(operand, &places),
            }
        }
    }
    #[allow(clippy::too_many_lines)]
    fn rvalue(&mut self, rvalue: &RValue, places: &mut IndexSlice<Place, [Allocation]>) -> Value {
        match rvalue {
            RValue::Use(operand) => Self::operand(operand, places),
            RValue::Extend { array, value, repeat } => {
                let value = Self::operand(value, places);
                let repeat: usize = Self::operand(repeat, places).unwrap_int().try_into().unwrap();
                places[*array].unwrap_array().extend(value, repeat);
                Value::Unit
            }
            RValue::Call { function, args } => {
                let call_body = Self::operand(function, places).unwrap_fn();
                let args = args.iter().map(|arg| Self::operand(arg, places)).collect();
                self.run(call_body, args)
            }
            RValue::BinaryExpr { lhs, op, rhs } => {
                let mut lhs = Self::operand(lhs, places);
                let mut rhs = Self::operand(rhs, places);
                match op {
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
                    BinaryOp::IntRange => {
                        Value::Range(Box::new(lhs.unwrap_int()..rhs.unwrap_int()))
                    }
                    BinaryOp::IntRangeInclusive =>
                    {
                        #[expect(clippy::range_plus_one)]
                        Value::Range(Box::new(lhs.unwrap_int()..rhs.unwrap_int() + 1))
                    }

                    BinaryOp::CharEq => Value::Bool(lhs.unwrap_char() == rhs.unwrap_char()),
                    BinaryOp::CharNeq => Value::Bool(lhs.unwrap_char() != rhs.unwrap_char()),

                    BinaryOp::StrEq => Value::Bool(lhs.unwrap_str() == rhs.unwrap_str()),
                    BinaryOp::StrNeq => Value::Bool(lhs.unwrap_str() != rhs.unwrap_str()),
                    BinaryOp::StrIndex => {
                        Value::Char(lhs.unwrap_str().as_bytes()[rhs.unwrap_int_usize()] as char)
                    }
                    BinaryOp::StrIndexSlice => {
                        Value::Str(lhs.unwrap_str()[rhs.unwrap_range_usize()].into())
                    }
                    BinaryOp::StrFind => Value::Int(
                        lhs.unwrap_str()
                            .find(rhs.unwrap_str().as_str())
                            .unwrap()
                            .try_into()
                            .unwrap(),
                    ),
                    BinaryOp::StrRFind => Value::Int(
                        lhs.unwrap_str()
                            .rfind(rhs.unwrap_str().as_str())
                            .unwrap()
                            .try_into()
                            .unwrap(),
                    ),
                    BinaryOp::ArrayIndexRange => todo!(),
                    BinaryOp::ArrayIndex => {
                        let index = rhs.unwrap_int_usize();
                        lhs.unwrap_array().get(index).unwrap().clone_raw()
                    }
                    BinaryOp::ArrayIndexRef => {
                        Value::Ref(lhs.unwrap_array().get(rhs.unwrap_int_usize()).unwrap())
                    }
                    BinaryOp::StructField => {
                        let index = rhs.unwrap_int_usize();
                        lhs.unwrap_struct().get(index).unwrap().clone_raw()
                    }
                    BinaryOp::StructFieldRef => {
                        let fields = lhs.unwrap_struct().clone();
                        Value::Ref(fields.get(rhs.unwrap_int_usize()).unwrap())
                    }
                }
            }
            RValue::UnaryExpr { op, operand } => {
                let mut operand = Self::operand(operand, places);
                match op {
                    UnaryOp::Deref => operand.unwrap_ref().clone_raw(),
                    UnaryOp::BoolNot => Value::Bool(!operand.unwrap_bool()),

                    UnaryOp::IntNeg => Value::Int(-operand.unwrap_int()),
                    UnaryOp::IntToStr => Value::Str(operand.unwrap_int().to_string().into()),
                    UnaryOp::Chr => {
                        Value::Char(u8::try_from(operand.unwrap_int()).unwrap() as char)
                    }

                    UnaryOp::PrintChar => {
                        let mut stdout = io::stdout().lock();
                        _ = write!(stdout, "{}", operand.unwrap_char());
                        _ = stdout.flush();
                        Value::Unit
                    }

                    UnaryOp::StrPrint => {
                        println!("{}", operand.unwrap_str());
                        Value::Unit
                    }
                    UnaryOp::StrLen => Value::Int(operand.unwrap_str().len().try_into().unwrap()),
                }
            }
        }
    }

    fn operand(operand: &Operand, places: &IndexSlice<Place, [Allocation]>) -> Value {
        match *operand {
            Operand::Ref(place) => Value::Ref(places[place].clone()),
            Operand::Constant(ref constant) => match *constant {
                Constant::Unit => Value::Unit,
                Constant::EmptyArray => Value::Array(Array::default()),
                Constant::Bool(bool) => Value::Bool(bool),
                Constant::Int(int) => Value::Int(int),
                Constant::Char(char) => Value::Char(char),
                Constant::Str(str) => Value::Str(str.as_str().into()),
                Constant::Func(body) => Value::Fn(body),
                Constant::StructInit => Value::Struct(places.iter().cloned().collect()),
            },
            Operand::Place(place) => places[place].clone_raw(),
            Operand::Unreachable => unreachable!(),
        }
    }
}
