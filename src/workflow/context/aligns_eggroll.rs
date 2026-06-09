use crate::eggroll::ast::Eggroll;
use crate::eggroll::to_crel::GuardedRepetitions;
use egg::RecExpr;

pub trait AlignsEggroll {
  fn unaligned_eggroll(&self) -> &Option<String>;
  fn accept_unaligned_eggroll(&mut self, eggroll: String);

  fn aligned_eggroll(&self) -> &Option<RecExpr<Eggroll>>;
  fn accept_aligned_eggroll(&mut self, eggroll: RecExpr<Eggroll>);

  fn aligned_eggroll_repetitions(&self) -> &Option<GuardedRepetitions>;
  fn accept_aligned_eggroll_repetitions(&mut self, reps: GuardedRepetitions);
}
