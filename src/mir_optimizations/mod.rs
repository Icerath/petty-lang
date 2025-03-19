use crate::mir::{BodyId, Mir};

mod compress_blocks;
mod not_branch;
mod redundant_blocks;

pub fn optimize(mir: &mut Mir) {
    for body in 0..mir.bodies.len() {
        optimize_body(mir, body.into());
    }
}

pub fn optimize_body(mir: &mut Mir, body: BodyId) {
    not_branch::optimize(mir, body);
    redundant_blocks::optimize(mir, body);
    compress_blocks::optimize(mir, body);
}
