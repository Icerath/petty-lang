use crate::HashMap;
use crate::mir::{self, Mir, Terminator};

pub fn optimize(mir: &mut Mir, body_id: mir::BodyId) {
    // FIXME: horrendously naive algorithm.
    let body = &mut mir.bodies[body_id];

    let mut replacements = HashMap::default();

    for (block_id, block) in body.blocks.iter_enumerated() {
        if !block.statements.is_empty() {
            continue;
        }
        let Terminator::Goto(goto) = block.terminator else {
            continue;
        };
        replacements.insert(block_id, goto);
    }
    for block in &mut body.blocks {
        block.terminator.with_jumps_mut(|jump| {
            while let Some(next) = replacements.get(jump) {
                *jump = *next;
            }
        });
    }
}
