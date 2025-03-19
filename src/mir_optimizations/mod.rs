use crate::mir::{BodyId, Mir};

mod compress_blocks;
mod redundant_blocks;

pub fn optimize(mir: &mut Mir) {
    for body in 0..mir.bodies.len() {
        optimize_body(mir, body.into());
    }
}

pub fn optimize_body(mir: &mut Mir, body: BodyId) {
    redundant_blocks::optimize(mir, body);
    compress_blocks::optimize(mir, body);
}
