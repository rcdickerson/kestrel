use crate::elaenia::cost_functions::optimize_choice::ElaeniaOptimizeChoiceCostFunction;
use crate::elaenia::cost_functions::syntactic_cost::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;

pub struct ElaeniaSyntacticAlignmentTask { }

impl ElaeniaSyntacticAlignmentTask {
  pub fn new() -> Self {
    ElaeniaSyntacticAlignmentTask {}
  }
}

impl <Ctx: AlignsEggroll> Task<Ctx> for ElaeniaSyntacticAlignmentTask {
  fn name(&self) -> String { "elaenia-syntactic-alignment".to_string() }
  fn run(&self, context: &mut Ctx) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().as_ref()
                 .expect("Missing unaligned Eggroll")
                 .parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites());
//    let extractor = Extractor::new(&runner.egraph, ElaeniaSyntacticCostFunction);
    let extractor = Extractor::new(&runner.egraph, ElaeniaOptimizeChoiceCostFunction);
    let (_, best) = extractor.find_best(runner.roots[0]);
    println!("Computed alignment by local loop counting.");
    context.accept_aligned_eggroll(best);
  }
}
