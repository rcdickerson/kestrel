use crate::crel::ast::*;
use crate::crel::mapper::*;
use crate::eggroll::to_crel::*;
use uuid::Uuid;
use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct AlignedCRel { }

impl AlignedCRel {
  pub fn new() -> Self {
    AlignedCRel { }
  }
}

impl Task for AlignedCRel {
  fn name(&self) -> String { "aligned-crel".to_string() }
  fn run(&self, context: &mut Context) {
    let reps = context.aligned_eggroll_repetitions.clone()
      .unwrap_or(GuardedRepetitions::new());
    let aligned_crel = eggroll_to_crel(
      &context.aligned_eggroll().to_string(),
      &Config::default(),
      &reps)
      .map(&mut LoopIdReassigner{});
    context.aligned_crel.replace(aligned_crel);
  }
}

struct LoopIdReassigner { }
impl CRelMapper for LoopIdReassigner {
  fn map_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
      Statement::While{runoff_link_id, invariants, condition, body, is_runoff, is_merged, ..} => {
        Statement::While {
          id: Uuid::new_v4(),
          runoff_link_id: runoff_link_id.clone(),
          invariants: invariants.clone(),
          condition: condition.clone(),
          body: body.clone(),
          is_runoff: is_runoff.clone(),
          is_merged: is_merged.clone(),
        }
      },
      _ => stmt.clone(),
    }
  }
}
