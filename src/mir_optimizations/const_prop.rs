use index_vec::IndexVec;

use crate::mir::{self, Local, Mir, Operand, RValue, Statement};

pub fn optimize(mir: &mut Mir, body_id: mir::BodyId) {
    let body = &mut mir.bodies[body_id];

    let mut mutated_locals: IndexVec<Local, u32> = vec![0; body.locals.index()].into();
    let mut local_rvalues: IndexVec<Local, Option<Operand>> =
        vec![None; body.locals.index()].into();

    for (_, block) in body.blocks.iter_enumerated() {
        for statement in &block.statements {
            let Statement::Assign { place, rvalue } = statement;
            mutated_locals[place.local] += 1;
            if let RValue::Use(operand) = rvalue {
                local_rvalues[place.local] = Some(operand.clone());
            }
            for local in 0..body.locals.index() {
                mutated_locals[local] += u32::from(rvalue.mutates_local(local.into()));
            }
        }
    }

    for (_, block) in body.blocks.iter_mut_enumerated() {
        for statement in &mut block.statements {
            let Statement::Assign { place: _, rvalue } = statement;

            rvalue.with_operands_mut(&mut |operand| {
                let Operand::Place(place) = operand else { return };
                let Some(new_operand) = &local_rvalues[place.local] else { return };
                if mutated_locals[place.local] > 1 || !place.projections.is_empty() {
                    return;
                }
                *operand = new_operand.clone();
            });
        }
    }
}
