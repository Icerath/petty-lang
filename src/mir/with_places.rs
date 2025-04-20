use super::{Block, Local, Operand, Place, Projection, RValue, Statement, Terminator};

macro_rules! copy {
    ($func:ident ) => {
        |t| $func(t)
    };
}

impl Block {
    pub fn with_locals(&self, mut f: impl FnMut(Local)) {
        for statement in &self.statements {
            let Statement::Assign { place, rvalue } = statement;
            place.with_locals(copy!(f));
            rvalue.with_locals(copy!(f));
        }
        self.terminator.with_locals(f);
    }
    pub fn with_locals_mut(&mut self, mut f: impl FnMut(&mut Local)) {
        for statement in &mut self.statements {
            let Statement::Assign { place, rvalue } = statement;
            place.with_locals_mut(copy!(f));
            rvalue.with_locals_mut(copy!(f));
        }
        self.terminator.with_locals_mut(f);
    }
}

impl RValue {
    pub fn with_locals(&self, mut f: impl FnMut(Local)) {
        match self {
            Self::StrJoin(operands) => operands.iter().for_each(|o| o.with_locals(copy!(f))),
            Self::BinaryExpr { lhs, rhs, .. } => {
                lhs.with_locals(copy!(f));
                rhs.with_locals(copy!(f));
            }
            Self::Call { function, args } => {
                function.with_locals(copy!(f));
                args.iter().for_each(|arg| arg.with_locals(copy!(f)));
            }
            Self::BuildArray(segments) => {
                for (elem, repeat) in segments {
                    elem.with_locals(copy!(f));
                    if let Some(repeat) = repeat {
                        repeat.with_locals(copy!(f));
                    }
                }
            }
            Self::UnaryExpr { operand, .. } | Self::Use(operand) => operand.with_locals(f),
        }
    }
    pub fn with_locals_mut(&mut self, mut f: impl FnMut(&mut Local)) {
        match self {
            Self::StrJoin(operands) => {
                operands.iter_mut().for_each(|o| o.with_locals_mut(copy!(f)));
            }
            Self::BinaryExpr { lhs, rhs, .. } => {
                lhs.with_locals_mut(copy!(f));
                rhs.with_locals_mut(copy!(f));
            }
            Self::Call { function, args } => {
                function.with_locals_mut(copy!(f));
                args.iter_mut().for_each(|arg| arg.with_locals_mut(copy!(f)));
            }
            Self::BuildArray(segments) => {
                for (elem, repeat) in segments {
                    elem.with_locals_mut(copy!(f));
                    if let Some(repeat) = repeat {
                        repeat.with_locals_mut(copy!(f));
                    }
                }
            }
            Self::UnaryExpr { operand, .. } | Self::Use(operand) => operand.with_locals_mut(f),
        }
    }
}

impl Operand {
    pub fn with_locals(&self, f: impl FnMut(Local)) {
        match self {
            Self::Place(place) | Self::Ref(place) => place.with_locals(f),
            Self::Constant(..) => {}
        }
    }
    pub fn with_locals_mut(&mut self, f: impl FnMut(&mut Local)) {
        match self {
            Self::Place(place) | Self::Ref(place) => place.with_locals_mut(f),
            Self::Constant(..) => {}
        }
    }
}

impl Terminator {
    pub fn with_locals(&self, f: impl FnMut(Local)) {
        match self {
            Self::Branch { condition, .. } => condition.with_locals(f),
            Self::Return(operand) => operand.with_locals(f),
            Self::Goto(..) | Self::Abort { .. } | Self::Unreachable => {}
        }
    }
    pub fn with_locals_mut(&mut self, f: impl FnMut(&mut Local)) {
        match self {
            Self::Branch { condition, .. } => condition.with_locals_mut(f),
            Self::Return(operand) => operand.with_locals_mut(f),
            Self::Goto(..) | Self::Abort { .. } | Self::Unreachable => {}
        }
    }
}

impl Place {
    pub fn with_locals(&self, mut f: impl FnMut(Local)) {
        f(self.local);
        self.projections.iter().for_each(|proj| proj.with_locals(copy!(f)));
    }
    pub fn with_locals_mut(&mut self, mut f: impl FnMut(&mut Local)) {
        f(&mut self.local);
        self.projections.iter_mut().for_each(|proj| proj.with_locals_mut(copy!(f)));
    }
}

impl Projection {
    pub fn with_locals(&self, mut f: impl FnMut(Local)) {
        match self {
            Self::Deref | Self::Field(..) | Self::ConstantIndex(..) => {}
            Self::Index(local) => f(*local),
        }
    }
    pub fn with_locals_mut(&mut self, mut f: impl FnMut(&mut Local)) {
        match self {
            Self::Deref | Self::Field(..) | Self::ConstantIndex(..) => {}
            Self::Index(local) => f(local),
        }
    }
}
