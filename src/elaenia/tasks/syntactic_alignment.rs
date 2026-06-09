use crate::elaenia::cost_functions::optimize_choice::*;
use crate::elaenia::cost_functions::optimize_complexity::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;

use super::elaenia_context::ElaeniaContext;

#[derive(Clone)]
pub enum ElaeniaCostFunction {
  OptimizeStructure,
  OptimizeChoice,
}

impl ElaeniaCostFunction {
  pub fn name(&self) -> &str {
    match self {
      Self::OptimizeStructure => "optimize_structure",
      Self::OptimizeChoice => "optimize_choice",
    }
  }
}

impl std::fmt::Display for ElaeniaCostFunction {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", match self {
      ElaeniaCostFunction::OptimizeStructure => "structure",
      ElaeniaCostFunction::OptimizeChoice => "choice-information",
    })
  }
}

pub struct ElaeniaSyntacticAlignmentTask { }

impl ElaeniaSyntacticAlignmentTask {
  pub fn new() -> Self {
    ElaeniaSyntacticAlignmentTask { }
  }
}

impl Task<ElaeniaContext> for ElaeniaSyntacticAlignmentTask {
  fn name(&self) -> String { "elaenia-syntactic-alignment".to_string() }
  fn run(&self, context: &mut ElaeniaContext) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().as_ref()
                 .expect("Missing unaligned Eggroll")
                 .parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites());
    match context.cost_function() {
      ElaeniaCostFunction::OptimizeStructure => {
        let extractor = Extractor::new(&runner.egraph, ElaeniaOptimizeStructureCostFunction);
        let(_, best) = extractor.find_best(runner.roots[0]);
        context.accept_aligned_eggroll(best);
      },
      ElaeniaCostFunction::OptimizeChoice => {
        let extractor = Extractor::new(&runner.egraph, ElaeniaOptimizeChoiceCostFunction);
        let(_, best) = extractor.find_best(runner.roots[0]);
        context.accept_aligned_eggroll(best);
      }
    };
    println!("Computed alignment by local loop counting.");

  }
}
