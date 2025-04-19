use index_vec::IndexVec;

use super::utils::blocks;
use crate::mir::{BlockId, BodyId, Mir, Terminator};

pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];

    if body.blocks.is_empty() {
        return;
    }

    let mut access_counts: IndexVec<BlockId, u32> = index_vec::index_vec![0; body.blocks.len()];
    access_counts[0] = 1;

    for block in blocks(body) {
        match block.terminator {
            Terminator::Goto(to) => access_counts[to] += 1,
            ref other => other.with_jumps(|to| access_counts[to] = 2),
        }
    }

    for block in 0..body.blocks.len() {
        let Terminator::Goto(goto) = body.blocks[block].terminator else { continue };
        if access_counts[goto] > 1 {
            continue;
        }
        let Ok([current, goto]) =
            body.blocks.as_raw_slice_mut().get_disjoint_mut([block, goto.index()])
        else {
            continue;
        };
        current.statements.extend_from_slice(&goto.statements);
        current.terminator = goto.terminator.clone();
    }
}
