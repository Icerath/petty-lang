use crate::mir::{self, Mir, Operand, Terminator};

pub fn optimize(mir: &mut Mir, body_id: mir::BodyId) {
    let body = &mut mir.bodies[body_id];
    for block in &mut body.blocks {
        let Terminator::Branch { condition, fals, tru } = &block.terminator else { continue };
        block.terminator = match condition {
            Operand::Constant(mir::Constant::Bool(false)) => Terminator::Goto(*fals),
            Operand::Constant(mir::Constant::Bool(true)) => Terminator::Goto(*tru),
            _ if fals == tru => Terminator::Goto(*fals),
            _ => continue,
        };
    }
}
