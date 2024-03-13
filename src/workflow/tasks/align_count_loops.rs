use crate::eggroll::cost_functions::minloops::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;

pub struct AlignCountLoops { }

impl AlignCountLoops {
  pub fn new() -> Self {
    AlignCountLoops {}
  }
}

impl Task for AlignCountLoops {
  fn run(&self, context: &mut Context) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites(false));
    let extractor = Extractor::new(&runner.egraph, MinLoops);
    let (_, best) = extractor.find_best(runner.roots[0]);
    println!("Computed alignment by local loop counting.");
    context.aligned_eggroll.replace(best);
  }
}
