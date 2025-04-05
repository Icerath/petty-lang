use std::mem;

use index_vec::IndexVec;

use crate::mir::{Block, BlockId, Body, Local};

pub fn block_ids(body: &Body) -> impl IntoIterator<Item = BlockId> {
    visited(body).into_iter_enumerated().filter_map(|(id, visited)| visited.then_some(id))
}

pub fn blocks(body: &Body) -> impl IntoIterator<Item = &Block> {
    let visited = visited(body);
    body.blocks.iter_enumerated().filter_map(move |(id, block)| visited[id].then_some(block))
}

pub fn blocks_mut(body: &mut Body) -> impl IntoIterator<Item = &mut Block> {
    let visited = visited(body);
    body.blocks.iter_mut_enumerated().filter_map(move |(id, block)| visited[id].then_some(block))
}

pub fn visited(body: &Body) -> IndexVec<BlockId, bool> {
    let mut visited = vec![false; body.blocks.len()].into();
    if body.blocks.is_empty() {
        return visited;
    }
    visited[0] = true;
    let mut queue = vec![BlockId::from(0)];
    while let Some(next) = queue.pop() {
        body.blocks[next].terminator.with_jumps(|jump| {
            if !mem::replace(&mut visited[jump], true) {
                queue.push(jump);
            }
        });
    }
    visited
}

pub fn visited_locals(body: &Body) -> IndexVec<Local, bool> {
    let mut visited = vec![false; body.locals.index()];
    visited.iter_mut().take(body.params).for_each(|v| *v = true);
    for block in &body.blocks {
        block.with_locals(|local| visited[local.index()] = true);
    }
    visited.into()
}
