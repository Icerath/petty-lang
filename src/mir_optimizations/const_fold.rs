use super::utils::blocks_mut;
use crate::{
    mir::{self, Constant, Mir, Operand, RValue},
    mir_interpreter::{self, Value},
};

pub fn optimize(mir: &mut Mir, body_id: mir::BodyId) {
    let body = &mut mir.bodies[body_id];

    for block in blocks_mut(body) {
        for statement in &mut block.statements {
            let Some(new_value) = try_compute(statement.rvalue()) else { continue };
            *statement.rvalue_mut() = RValue::Use(new_value);
        }
    }
}

pub fn try_compute(rvalue: &RValue) -> Option<Operand> {
    if rvalue.side_effect() {
        return None;
    }
    match rvalue {
        RValue::BinaryExpr { lhs, op, rhs } => {
            let lhs = value_of(lhs)?;
            let rhs = value_of(rhs)?;
            let value = mir_interpreter::binary_op(lhs, *op, rhs);
            constant_of(&value)
        }
        RValue::UnaryExpr { op, operand } => {
            let operand = value_of(operand)?;
            let value = mir_interpreter::unary_op(*op, operand);
            constant_of(&value)
        }
        RValue::StrJoin(segments) => {
            let mut fstring = String::new();
            for seg in segments {
                let Value::Str(s) = value_of(seg)? else { unreachable!() };
                fstring.push_str(&s);
            }
            Some(Operand::Constant(Constant::Str(fstring.into())))
        }
        _ => None,
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
        Value::Range(ref range) => Constant::Range((**range).clone()),
        Value::Array(ref array) if array.is_empty() => {
            Constant::EmptyArray { cap: array.capacity() }
        }
        Value::Fn(body) => Constant::Func(body),
        _ => return None,
    };
    Some(Operand::Constant(constant))
}
