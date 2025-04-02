//! Extracts an aligned program from the [Context]'s e-graph using the
//! [MinLoops] cost function.

//! [MinLoops] is a *local* cost function (each node cost depends only
//! on the cost of its direct children), leading to very efficient
//! extraction. However, it only considers syntactic properties around
//! the number of merged loops, and is not capable of finding
//! alignments with desirable semantic properties which require
//! operations such as loop scheduling or unrolling.

use crate::eggroll::cost_functions::minloops::*;
use crate::workflow::Context;
use crate::workflow::task::*;
use egg::*;

pub struct AlignCountLoops { }

impl AlignCountLoops {
  pub fn new() -> Self {
    AlignCountLoops {}
  }
}

impl <Ctx: Context> Task<Ctx> for AlignCountLoops {
  fn name(&self) -> String { "align-count-loops".to_string() }
  fn run(&self, context: &mut Ctx) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites());
    let extractor = Extractor::new(&runner.egraph, MinLoops);
    let (_, best) = extractor.find_best(runner.roots[0]);
    println!("Computed alignment by local loop counting.");
    context.accept_aligned_eggroll(best);
  }
}
