use super::utils::blocks_mut;
use crate::{
    mir::{self, Constant, Mir, Operand, RValue},
    mir_interpreter::{self, Value},
};

pub fn optimize(mir: &mut Mir, body_id: mir::BodyId) {
    let body = &mut mir.bodies[body_id];

    for block in blocks_mut(body) {
        for statement in &mut block.statements {
            let new_value = match statement.rvalue() {
                RValue::BinaryExpr { lhs, op, rhs } => {
                    let Some(lhs) = value_of(lhs) else { continue };
                    let Some(rhs) = value_of(rhs) else { continue };
                    let value = mir_interpreter::binary_op(lhs, *op, rhs);
                    constant_of(&value)
                }
                _ => continue,
            };
            let Some(new_value) = new_value else { continue };
            *statement.rvalue_mut() = RValue::Use(new_value);
        }
    }
}

pub fn value_of(operand: &Operand) -> Option<Value> {
    match operand {
        Operand::Constant(constant) => Some(mir_interpreter::const_value(constant)),
        _ => None,
    }
}

pub fn constant_of(value: &Value) -> Option<Operand> {
    let constant = match *value {
        Value::Unit => Constant::Unit,
        Value::Bool(bool) => Constant::Bool(bool),
        Value::Int(int) => Constant::Int(int),
        Value::Char(char) => Constant::Char(char),
        Value::Str(ref str) => Constant::Str(str.as_str().into()),
        Value::Array(ref array) if array.is_empty() => Constant::EmptyArray,
        Value::Fn(body) => Constant::Func(body),
        _ => return None,
    };
    Some(Operand::Constant(constant))
}
