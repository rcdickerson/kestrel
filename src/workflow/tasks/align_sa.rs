//! Extracts an aligned program using simulated annealing over
//! candidate programs taken from the [Context]'s e-graph. The
//! simulated annealing takes much longer to converge to an extraction
//! than, e.g., counting fused loops, but is able to find alignments
//! with desirable semantic properties which require operations like
//! loops scheduling and unrolling.

use crate::anneal::*;
use crate::crel::eval::*;
use crate::eggroll::cost_functions::sa::*;
use crate::eggroll::eggroll_jumper::EggrollJumper;
use crate::workflow::Context;
use crate::workflow::kestrel_context::*;
use crate::workflow::task::*;
use egg::*;

pub struct AlignSa {
  start_random: bool,
  max_iterations: usize,
  ablate_fusion: bool,
  ablate_runoffs: bool,
}

impl AlignSa {
  pub fn new(start_random: bool, max_iterations: usize) -> Self {
    AlignSa {
      start_random,
      max_iterations,
      ablate_fusion: false,
      ablate_runoffs: false,
   }
  }

  pub fn ablate_fusion(&mut self) {
    self.ablate_fusion = true;
  }

  pub fn ablate_runoffs(&mut self) {
    self.ablate_runoffs = true;
  }
}

impl Task<KestrelContext> for AlignSa {
  fn name(&self) -> String { "align-sa".to_string() }

  fn run(&self, context: &mut KestrelContext) {
    if context.verified {
      println!("Verification complete; skipping simulated annealing alignment");
      return;
    }

    let num_trace_states = 10;
    let trace_fuel = 100000;
    let init = if self.start_random { None } else { context.aligned_eggroll.clone() };
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites());
    let generator = context.unaligned_crel().fundefs.get(&"_test_gen".to_string());
    let decls = context.unaligned_crel().global_decls_and_params();
    let trace_states = rand_states_satisfying(
      num_trace_states, &context.spec().pre, Some(&decls), generator, 100000);
    let mut jumper = EggrollJumper::new(&runner.egraph);
    let annealer = Annealer::new();
    let (best, meta) = annealer.find_best(self.max_iterations, init, &mut jumper,
        |expr, meta| { sa_score(&trace_states, trace_fuel, expr, meta,
                                self.ablate_fusion,
                                self.ablate_runoffs) },
    );
    context.aligned_eggroll.replace(best);
    context.aligned_eggroll_repetitions.replace(meta);
  }
}
