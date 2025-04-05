use std::mem;

use index_vec::IndexVec;

use crate::mir::{BlockId, BodyId, Mir};

pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];
    let visited = super::utils::visited(body);

    let (new_blocks, new_ids): (_, IndexVec<BlockId, _>) = mem::take(&mut body.blocks)
        .into_iter_enumerated()
        .filter_map(|(id, block)| visited[id].then_some((block, id)))
        .collect();
    body.blocks = new_blocks;

    for block in &mut body.blocks.iter_mut() {
        block.terminator.with_jumps_mut(|jump| {
            *jump = new_ids.binary_search(jump).unwrap();
        });
    }
}
