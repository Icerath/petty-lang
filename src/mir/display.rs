use std::fmt;

use super::{Constant, Mir, Operand, RValue, Statement, Terminator};

impl fmt::Display for Mir {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, body) in self.bodies.iter_enumerated().skip(1 + self.num_intrinsics) {
            writeln!(f, "fn{id:?}() {{")?;
            for (id, block) in body.blocks.iter_enumerated() {
                writeln!(f, "{}bb{id:?}: {{", Indent(1))?;
                for statement in &block.statements {
                    write!(f, "{}", Indent(2))?;
                    match statement {
                        Statement::Assign { place, deref, rvalue } => {
                            if *deref {
                                write!(f, "deref ")?;
                            }
                            write!(f, "_{place:?} = ")?;
                            match rvalue {
                                RValue::Abort => write!(f, "abort"),
                                RValue::BinaryExpr { lhs, op, rhs } => {
                                    write!(f, "{op:?}({lhs}, {rhs})")
                                }
                                RValue::Use(arg) => write!(f, "{arg}"),
                                RValue::Call { function, args } => {
                                    write!(f, "call {function}")?;
                                    write!(f, "(")?;
                                    for (i, arg) in args.iter().enumerate() {
                                        write!(f, "{}{arg}", if i == 0 { "" } else { ", " })?;
                                    }
                                    write!(f, ")")
                                }
                                RValue::Extend { array, value, repeat } => {
                                    write!(f, "extend _{array:?}[{value}; {repeat}]")
                                }
                                RValue::UnaryExpr { op, operand } => {
                                    write!(f, "{op:?}({operand})")
                                }
                            }?;
                        }
                    }
                    writeln!(f)?;
                }
                write!(f, "{}", Indent(2))?;
                match &block.terminator {
                    Terminator::Goto(to) => write!(f, "goto bb{to:?}"),
                    Terminator::Branch { condition, fals, tru } => {
                        write!(f, "branch {condition}[false: bb{fals:?}, true: bb{tru:?}]")
                    }
                    Terminator::Return(arg) => write!(f, "return {arg}"),
                }?;
                writeln!(f, "\n{}}}", Indent(1))?;
            }
            writeln!(f, "}}")?;
        }
        Ok(())
    }
}

struct Indent(u8);

impl fmt::Display for Indent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..self.0 {
            write!(f, "    ")?;
        }
        Ok(())
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Place(place) => write!(f, "_{place:?}"),
            Self::Constant(constant) => write!(f, "{constant}"),
            Self::Unreachable => write!(f, "unreachable"),
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !matches!(self, Self::Func(..)) {
            write!(f, "const ")?;
        }
        match self {
            Self::EmptyArray => write!(f, "[]"),
            Self::Unit => write!(f, "()"),
            Self::Bool(bool) => write!(f, "{bool}"),
            Self::Int(int) => write!(f, "{int}"),
            Self::Char(char) => write!(f, "{char:?}"),
            Self::Str(str) => write!(f, "{str:?}"),
            Self::Func(id) => write!(f, "fn{id:?}"),
        }
    }
}
