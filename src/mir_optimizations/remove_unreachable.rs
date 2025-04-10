use index_vec::IndexSlice;

use super::utils::block_ids;
use crate::mir::{BlockId, Body, BodyId, Mir, Terminator};

pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];
    let block_ids = block_ids(body).into_iter().collect::<Vec<_>>();
    let mut cache = index_vec::index_vec![None; body.blocks.len()];
    for id in block_ids {
        recurse(body, id, &mut cache);
    }
}

pub fn recurse(
    body: &mut Body,
    block_id: BlockId,
    cache: &mut IndexSlice<BlockId, [Option<bool>]>,
) -> bool {
    if let Some(cached) = cache[block_id] {
        return cached;
    }
    cache[block_id] = Some(false); // prevents cycles
    let block = &mut body.blocks[block_id];
    let is_unreachable = match block.terminator {
        Terminator::Unreachable => true,
        Terminator::Goto(goto) => recurse(body, goto, cache),
        Terminator::Branch { fals, tru, .. } => 'branch: {
            let false_is_unreachable = recurse(body, fals, cache);
            let true_is_unreachable = recurse(body, tru, cache);

            if false_is_unreachable && true_is_unreachable {
                break 'branch true;
            }
            let block = &mut body.blocks[block_id];
            if false_is_unreachable {
                block.terminator = Terminator::Goto(tru);
            } else if true_is_unreachable {
                block.terminator = Terminator::Goto(fals);
            }
            false
        }
        Terminator::Return(_) | Terminator::Abort => false,
    };
    let block = &mut body.blocks[block_id];
    if is_unreachable {
        block.terminator = Terminator::Unreachable;
    }
    cache[block_id] = Some(is_unreachable);
    is_unreachable
}
