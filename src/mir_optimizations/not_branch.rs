use super::utils::block_ids;
use crate::mir::{BodyId, Mir, Operand, RValue, Statement, Terminator, UnaryOp};

// Looks for cases where the output of a unary not is immediately fed into a branch.
pub fn optimize(mir: &mut Mir, body_id: BodyId) {
    let body = &mut mir.bodies[body_id];
    let block_ids = block_ids(body).into_iter().collect::<Vec<_>>();

    'outer: for &block_id in &block_ids {
        let block = &body.blocks[block_id];
        let Terminator::Branch { condition, fals, tru } = &block.terminator else { continue };
        let Operand::Place(cplace) = condition else { continue };
        let Some(Statement::Assign { place, rvalue }) = block.statements.last() else {
            continue;
        };
        if cplace != place {
            continue;
        }
        let RValue::UnaryExpr { op: UnaryOp::BoolNot, operand } = rvalue else { continue };

        // use condition inside of the not rvalue and swap false/true branches
        let (condition, tru, fals) = (operand.clone(), *fals, *tru);
        // filter assignments to a place read elsewhere
        {
            for &inner_block_id in &block_ids {
                let inner_block = &body.blocks[inner_block_id];
                if inner_block
                    .statements
                    .iter()
                    .any(|statement| statement.rvalue().mentions_place(place))
                {
                    continue 'outer;
                }
                if inner_block_id != block_id && inner_block.terminator.mentions_place(place) {
                    continue 'outer;
                }
            }
        }
        let block = &mut body.blocks[block_id];
        block.statements.pop();
        block.terminator = Terminator::Branch { condition, fals, tru }
    }
}
