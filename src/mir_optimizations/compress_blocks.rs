use std::mem;

use index_vec::IndexVec;

use crate::mir::{BlockId, Body, BodyId, Mir};

pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];
    if body.blocks.is_empty() {
        return;
    }
    let visisted = accessible_blocks(body);
    let accessible: Vec<_> =
        visisted.iter_enumerated().filter_map(|(id, &visible)| visible.then_some(id)).collect();
    for (id, block) in &mut body.blocks.iter_mut_enumerated() {
        if !visisted[id] {
            continue;
        }
        block.terminator.with_jumps_mut(|jump| {
            *jump = accessible.binary_search(jump).unwrap().into();
        });
    }
    body.blocks = mem::take(&mut body.blocks)
        .into_iter_enumerated()
        .filter_map(|(id, block)| visisted[id].then_some(block))
        .collect();
}

fn accessible_blocks(body: &Body) -> IndexVec<BlockId, bool> {
    let mut visisted = vec![false; body.blocks.len()].into();
    fill_visisted(body, BlockId::from(0), &mut visisted);
    visisted
}

fn fill_visisted(body: &Body, block: BlockId, visisted: &mut IndexVec<BlockId, bool>) {
    if mem::replace(&mut visisted[block], true) {
        return;
    }
    body.blocks[block].terminator.with_jumps(|block| fill_visisted(body, block, visisted));
}
