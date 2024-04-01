use crate::annealer::*;
use crate::crel::eval::*;
use crate::eggroll::cost_functions::sa::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;

pub struct AlignSa {
  start_random: bool,
  max_iterations: usize,
}

impl AlignSa {
  pub fn new(start_random: bool, max_iterations: usize) -> Self {
    AlignSa {
      start_random,
      max_iterations,
    }
  }
}

impl Task for AlignSa {
  fn name(&self) -> String { "align-sa".to_string() }

  fn run(&self, context: &mut Context) {
    if context.verified {
      println!("Verification complete; skipping simulated annealing alignment");
      return;
    }

    let num_trace_states = 10;
    let trace_fuel = 10000;

    let init = if self.start_random { None } else { context.aligned_eggroll.clone() };
    let runner = Runner::default()
      .with_expr(&init.clone().unwrap_or(context.unaligned_eggroll().parse().unwrap()))
      .run(&crate::eggroll::rewrite::rewrites(true));
    let generator = context.unaligned_crel().fundefs.get(&"_test_gen".to_string());
    let decls = context.unaligned_crel().global_decls_and_params();
    let trace_states = rand_states_satisfying(
      num_trace_states, &context.spec().pre, Some(&decls), generator, 1000);
    let annealer = Annealer::new(&runner.egraph);
    let best = annealer.find_best(self.max_iterations, runner.roots[0], init,
                                  |expr| { sa_score(&trace_states, trace_fuel, expr) });
    context.aligned_eggroll.replace(best);
  }
}
