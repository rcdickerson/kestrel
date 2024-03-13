use crate::eggroll::milp_extractor::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;

pub struct AlignMilp { }

impl AlignMilp {
  pub fn new() -> Self {
    AlignMilp {}
  }
}

impl Task for AlignMilp {
  fn run(&self, context: &mut Context) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites(true));
    let mut extractor = MilpExtractor::new(&runner.egraph);
    context.aligned_eggroll.replace(extractor.solve(runner.roots[0]));
  }
}
