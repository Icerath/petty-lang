use std::hash::BuildHasher;

use rustc_hash::FxBuildHasher;

use crate::{
    codegen_opts::CodegenOpts,
    mir::{BodyId, Mir},
};

mod const_fold;
mod const_prop;
mod fix_entry_block;
mod not_branch;
mod redundant_blocks;
mod redundant_branch;
mod remove_dead_assignments;
mod remove_dead_blocks;
mod remove_dead_places;
mod remove_goto_terminator;
mod remove_unreachable;
mod utils;

pub fn optimize(mir: &mut Mir, opts: &CodegenOpts, v: u8) {
    for body in 0..mir.bodies.len() {
        optimize_body(mir, body.into(), opts, v);
    }
    if v > 1 {
        crate::log!();
    }
}

pub fn optimize_body(mir: &mut Mir, body: BodyId, opts: &CodegenOpts, v: u8) {
    const MAX_ITERS: usize = 16;
    let mut current_hash = FxBuildHasher.hash_one(&mir.bodies[body]);
    let mut num_iters = 0;
    for iter in 0..MAX_ITERS {
        num_iters = iter;
        optimize_body_once(mir, body, opts);
        let new_hash = FxBuildHasher.hash_one(&mir.bodies[body]);
        if current_hash == new_hash {
            break;
        }
        current_hash = new_hash;
    }
    // log required opt len
    if v > 1 {
        if let Some(name) = mir.bodies[body].name {
            if !mir.bodies[body].auto || v > 2 {
                crate::log!("roptlen: {name} = {num_iters}");
            }
        } else if v > 3 {
            crate::log!("roptlen: {body:?} = {num_iters}");
        }
    }
}

pub fn optimize_body_once(mir: &mut Mir, body: BodyId, opts: &CodegenOpts) {
    macro_rules! optimize {
        ($($name:ident),* $(,)*) => {
            $(if opts.$name {
                $name::optimize(mir, body);
            })*
        };
    }

    optimize!(remove_unreachable);
    if opts.const_prop {
        const_prop_fold(mir, body);
    }
    optimize!(
        not_branch,
        redundant_branch,
        redundant_blocks,
        remove_goto_terminator,
        remove_dead_blocks,
        remove_dead_assignments,
        remove_dead_places,
        fix_entry_block,
    );
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
