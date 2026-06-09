use crate::elaenia::tasks::elaenia_context::*;
use crate::elaenia::tasks::syntactic_alignment::ElaeniaCostFunction;
use crate::workflow::task::*;

pub struct SetParameters {
  unroll_loops: bool,
  ast_depth: usize,
  cost_function: ElaeniaCostFunction
}

impl SetParameters {
  pub fn new(unroll_loops: bool, ast_depth: usize, cost_function: ElaeniaCostFunction) -> Self {
    SetParameters { unroll_loops, ast_depth, cost_function }
  }
}

impl Task<ElaeniaContext> for SetParameters {
  fn name(&self) -> String { "set-parameters".to_string() }

  fn run(&self, context: &mut ElaeniaContext) {
    context.set_add_unrolls(self.unroll_loops);
    context.set_ast_depth(self.ast_depth);
    context.set_cost_function(self.cost_function.clone());
  }
}
