use std::{fmt, fmt::Write};

use super::{Constant, Mir, Operand, Place, Projection, RValue, Statement, Terminator};

impl fmt::Display for Mir {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, body) in self.bodies.iter_enumerated() {
            if body.auto {
                continue;
            }
            write!(f, "fn ")?;
            match body.name {
                Some(name) => write!(f, "{name}"),
                None => write!(f, "{}", id.raw()),
            }?;
            writeln!(f, "() {{")?;
            for (id, block) in body.blocks.iter_enumerated() {
                writeln!(f, "{}bb{id:?}: {{", Indent(1))?;
                for statement in &block.statements {
                    write!(f, "{}", Indent(2))?;
                    match statement {
                        Statement::Assign { place, rvalue } => {
                            write!(f, "{place} = ")?;
                            match rvalue {
                                RValue::BinaryExpr { lhs, op, rhs } => {
                                    write!(
                                        f,
                                        "{op:?}({}, {})",
                                        lhs.display(self),
                                        rhs.display(self)
                                    )
                                }
                                RValue::Use(arg) => write!(f, "{}", arg.display(self)),
                                RValue::Call { function, args } => {
                                    write!(f, "call {}", function.display(self))?;
                                    write!(f, "(")?;
                                    for (i, arg) in args.iter().enumerate() {
                                        let sep = if i == 0 { "" } else { ", " };
                                        write!(f, "{sep}{}", arg.display(self))?;
                                    }
                                    write!(f, ")")
                                }
                                RValue::Extend { array, value, repeat } => {
                                    write!(
                                        f,
                                        "extend _{array:?}[{}; {}]",
                                        value.display(self),
                                        repeat.display(self)
                                    )
                                }
                                RValue::UnaryExpr { op, operand } => {
                                    write!(f, "{op:?}({})", operand.display(self))
                                }
                            }?;
                        }
                    }
                    writeln!(f)?;
                }
                write!(f, "{}", Indent(2))?;
                match &block.terminator {
                    Terminator::Unreachable => write!(f, "unreachable"),
                    Terminator::Abort => write!(f, "abort"),
                    Terminator::Goto(to) => write!(f, "goto bb{to:?}"),
                    Terminator::Branch { condition, fals, tru } => {
                        write!(
                            f,
                            "branch {}[false: bb{fals:?}, true: bb{tru:?}]",
                            condition.display(self)
                        )
                    }
                    Terminator::Return(arg) => write!(f, "return {}", arg.display(self)),
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

struct OperandDisplay<'a, 'b>(&'a Mir, &'b Operand);
struct ConstDisplay<'a, 'b>(&'a Mir, &'b Constant);

impl fmt::Display for OperandDisplay<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1 {
            Operand::Ref(place) => write!(f, "&{place}"),
            Operand::Place(place) => write!(f, "{place}"),
            Operand::Constant(constant) => write!(f, "{}", constant.display(self.0)),
        }
    }
}

impl Operand {
    pub fn display(&self, mir: &Mir) -> impl fmt::Display {
        OperandDisplay(mir, self)
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut end = String::new();

        for projection in &self.projections {
            match projection {
                Projection::Deref => write!(f, "*")?,
                Projection::Field(field) => write!(end, ".{field}")?,
                Projection::Index(index) => write!(end, "[_{index:?}]")?,
            }
        }

        write!(f, "_{:?}", self.local)?;
        f.write_str(&end)
    }
}

impl fmt::Display for ConstDisplay<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !matches!(self.1, Constant::Func(..)) {
            write!(f, "const ")?;
        }
        match self.1 {
            Constant::UninitStruct { size } => write!(f, "struct {{ {size:?} }}"),
            Constant::EmptyArray => write!(f, "[]"),
            Constant::Unit => write!(f, "()"),
            Constant::Bool(bool) => write!(f, "{bool}"),
            Constant::Int(int) => write!(f, "{int}"),
            Constant::Char(char) => write!(f, "{char:?}"),
            Constant::Str(str) => write!(f, "{str:?}"),
            Constant::Func(id) => match self.0.bodies[*id].name {
                Some(name) => write!(f, "{name}"),
                None => write!(f, "fn({})", id.raw()),
            },
        }
    }
}
impl Constant {
    pub fn display(&self, mir: &Mir) -> impl fmt::Display {
        ConstDisplay(mir, self)
    }
}
