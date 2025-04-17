use super::utils::{blocks, blocks_mut};
use crate::mir::{BodyId, Local, Mir, Statement, Terminator};

pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];

    let mut access_counts = index_vec::index_vec![0; body.locals.index()];
    for param in 0..body.params {
        access_counts[param] += 1;
    }

    for block in blocks(body) {
        let mut incr = |local: Local| access_counts[local] += 1;
        for statement in &block.statements {
            let Statement::Assign { place, rvalue } = statement;
            rvalue.with_locals(&mut incr);
            place.with_locals(&mut incr);
        }
        block.terminator.with_locals(incr);
    }

    for block in blocks_mut(body) {
        block.statements.retain(|statement| {
            let Statement::Assign { place, rvalue } = statement;
            if access_counts[place.local] > 1
                || rvalue.side_effect()
                || !place.projections.is_empty()
            {
                return true;
            }
            false
        });
    }

    for block in blocks_mut(body) {
        let term_op = match &block.terminator {
            Terminator::Return(operand) => Some(operand),
            Terminator::Abort => None,
            _ => continue,
        };
        let statements = block.statements.clone();
        let mut i = 0;
        block.statements.retain(|statement| {
            i += 1;

            let Statement::Assign { place, rvalue } = statement;
            if !place.projections.is_empty() {
                return true;
            }

            if rvalue.side_effect() {
                return true;
            }

            let rem = &statements[i..];
            let mut used = rem.iter().any(|stmt| {
                let Statement::Assign { place: _, rvalue } = stmt;
                let mut used = false;
                rvalue.with_locals(|local| used = used || local == place.local);
                place.with_locals(|local| used = used || local == place.local);
                used
            });
            if let Some(term_op) = term_op {
                term_op.with_locals(|local| used = used || local == place.local);
            }

            used
        });
    }
}
