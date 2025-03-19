use std::{collections::HashSet, mem};

use crate::mir::{BlockId, BodyId, Mir};

pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];
    let mut referenced_blocks = HashSet::new();
    referenced_blocks.insert(BlockId::from(0));
    for block in &body.blocks {
        block.terminator.with_jumps(|jump| _ = referenced_blocks.insert(jump));
    }
    let mut referenced_blocks: Vec<_> = referenced_blocks.into_iter().collect();
    referenced_blocks.sort_unstable();
    for block in &mut body.blocks {
        block.terminator.with_jumps_mut(|jump| {
            let new = referenced_blocks.binary_search(jump).unwrap();
            *jump = new.into();
        });
    }
    body.blocks = mem::take(&mut body.blocks)
        .into_iter_enumerated()
        .filter_map(|(id, block)| referenced_blocks.contains(&id).then_some(block))
        .collect();
}
