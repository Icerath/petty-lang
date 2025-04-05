use crate::mir::{BodyId, Mir};

mod const_prop;
mod not_branch;
mod redundant_blocks;
mod redundant_branch;
mod remove_dead_blocks;
mod remove_dead_places;
mod utils;

pub fn optimize(mir: &mut Mir) {
    for body in 0..mir.bodies.len() {
        optimize_body(mir, body.into());
    }
}

pub fn optimize_body(mir: &mut Mir, body: BodyId) {
    not_branch::optimize(mir, body);
    const_prop::optimize(mir, body);
    redundant_branch::optimize(mir, body);
    redundant_blocks::optimize(mir, body);
    remove_dead_blocks::optimize(mir, body);
    remove_dead_places::optimize(mir, body);
}
