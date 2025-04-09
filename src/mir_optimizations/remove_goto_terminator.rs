use crate::{
    HashMap,
    mir::{self, Mir, Terminator},
};

pub fn optimize(mir: &mut Mir, body_id: mir::BodyId) {
    let body = &mut mir.bodies[body_id];

    let mut replacements = HashMap::default();

    for (block_id, block) in body.blocks.iter_enumerated() {
        if !block.statements.is_empty() {
            continue;
        }
        replacements.insert(block_id, block.terminator.clone());
    }
    for block in &mut body.blocks {
        let Terminator::Goto(goto_block) = &block.terminator else { continue };
        let Some(new_terminator) = replacements.get(goto_block) else { continue };
        block.terminator = new_terminator.clone();
    }
}
