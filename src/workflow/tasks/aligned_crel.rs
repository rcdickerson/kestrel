use crate::eggroll::to_crel::*;
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
    let mut aligned_crel = eggroll_to_crel(
      &context.aligned_eggroll().to_string(),
      &Config::default(),
      &reps);
    aligned_crel.assign_loop_ids();
    context.aligned_crel.replace(aligned_crel);
  }
}
