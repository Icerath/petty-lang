use std::hash::BuildHasher;

use rustc_hash::FxBuildHasher;

use crate::mir::{BodyId, Mir};

mod const_fold;
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
    const_prop_fold(mir, body);
    redundant_branch::optimize(mir, body);
    redundant_blocks::optimize(mir, body);
    remove_dead_blocks::optimize(mir, body);
    remove_dead_places::optimize(mir, body);
}

fn const_prop_fold(mir: &mut Mir, body: BodyId) {
    const MAX_ITERS: usize = 16;
    let mut current_hash = FxBuildHasher.hash_one(&mir.bodies[body]);
    for _ in 0..MAX_ITERS {
        const_prop::optimize(mir, body);
        const_fold::optimize(mir, body);
        let new_hash = FxBuildHasher.hash_one(&mir.bodies[body]);
        if current_hash == new_hash {
            break;
        }
        current_hash = new_hash;
    }
}
