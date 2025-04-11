use crate::mir::{BlockId, BodyId, Mir, Terminator};

pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];
    let Some(entry) = body.blocks.first() else { return };
    if !entry.statements.is_empty() {
        return;
    }
    let Terminator::Goto(next) = entry.terminator else { return };
    // FIXME: This should adapt to more cases
    if next.index() != 1 {
        return;
    }
    body.blocks.remove(BlockId::from(0));
    body.blocks.iter_mut().for_each(|block| {
        block.terminator.with_jumps_mut(|jump| *jump = jump.index().saturating_sub(1).into());
    });
}
