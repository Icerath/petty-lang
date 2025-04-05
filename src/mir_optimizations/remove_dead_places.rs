use index_vec::IndexVec;

use super::utils::visited_locals;
use crate::mir::{BodyId, Local, Mir};

pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];

    let visited = visited_locals(body);
    let num_places = visited.iter().filter(|visited| **visited).count();
    let new_places: IndexVec<Local, _> = visited
        .into_iter_enumerated()
        .filter_map(|(local, visited)| visited.then_some(local))
        .collect();

    for block in &mut body.blocks.iter_mut() {
        block.with_locals_mut(|local| *local = new_places.binary_search(local).unwrap());
    }

    body.locals = num_places.into();
}
