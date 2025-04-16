use index_vec::IndexVec;

use super::utils::{blocks, blocks_mut};
use crate::mir::{self, Local, Mir, Operand, Projection, RValue, Statement};

pub fn optimize(mir: &mut Mir, body_id: mir::BodyId) {
    let body = &mut mir.bodies[body_id];

    let mut mutated_locals: IndexVec<Local, u32> = vec![0; body.locals.index()].into();
    let mut local_rvalues: IndexVec<Local, Option<Operand>> =
        vec![None; body.locals.index()].into();

    for i in 0..body.params {
        mutated_locals[i] += 1;
    }

    for block in blocks(body) {
        for statement in &block.statements {
            let Statement::Assign { place, rvalue } = statement;
            mutated_locals[place.local] += 1;

            if let RValue::Use(operand) = rvalue {
                if place.projections.is_empty() {
                    local_rvalues[place.local] = Some(operand.clone());
                }
            }
            for local in 0..body.locals.index() {
                mutated_locals[local] += u32::from(rvalue.mutates_local(local.into()));
            }
        }
        for local in 0..body.locals.index() {
            mutated_locals[local] += u32::from(block.terminator.mutates_local(local.into()));
        }
    }

    for block in blocks_mut(body) {
        let replace = &mut |operand: &mut Operand| {
            let Operand::Place(place) = operand else { return };
            let Some(new_operand) = &local_rvalues[place.local] else { return };
            if mutated_locals[place.local] > 1 || !place.projections.is_empty() {
                return;
            }
            *operand = new_operand.clone();
        };
        for statement in &mut block.statements {
            statement.rvalue_mut().with_operands_mut(replace);
        }
        block.terminator.with_operands_mut(replace);
    }

    let mut cache: IndexVec<_, Option<&Operand>> = (0..body.locals.index()).map(|_| None).collect();
    for block in blocks_mut(body) {
        cache.as_raw_slice_mut().fill_with(|| None);

        macro_rules! replace {
            () => {
                &mut |operand: &mut Operand| {
                    let Operand::Place(place) = operand else { return };
                    let Some(cached) = cache[place.local] else { return };
                    match cached {
                        // TODO: This should handle more cases
                        Operand::Ref(to) if place.projections == [Projection::Deref] => {
                            *operand = Operand::Place(to.clone())
                        }
                        _ if place.projections.is_empty() => *operand = cached.clone(),
                        _ => {}
                    }
                }
            };
        }

        for statement in &mut block.statements {
            let Statement::Assign { place, rvalue } = statement;

            rvalue.with_operands_mut(replace!());
            rvalue.with_locals(|local| {
                if rvalue.mutates_local(local) {
                    cache[local] = None;
                }
            });
            cache[place.local] = None;
            let RValue::Use(operand) = rvalue else { continue };
            if !place.projections.is_empty() {
                continue;
            }
            cache[place.local] = Some(&*operand);
        }
        block.terminator.with_operands_mut(replace!());
    }
}
