use crate::anneal::*;
use crate::crel::eval::*;
use crate::eggroll::cost_functions::sa2::*;
use crate::eggroll::eggroll_jumper::EggrollJumper;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;

pub struct AlignSa2 {
  start_random: bool,
  max_iterations: usize,
  af_merge_count: bool,
  af_runoff_execs: bool,
}

impl AlignSa2 {
  pub fn new(start_random: bool, max_iterations: usize) -> Self {
    AlignSa2 {
      start_random,
      max_iterations,
      af_merge_count: true,
      af_runoff_execs: true,
   }
  }

  pub fn ablate_merge_count(&mut self) {
    self.af_merge_count = false;
  }

  pub fn ablate_runoff_execs(&mut self) {
    self.af_runoff_execs = false;
  }
}

impl Task for AlignSa2 {
  fn name(&self) -> String { "align-sa".to_string() }

  fn run(&self, context: &mut Context) {
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
        |expr, meta| { sa_score_ablate(&trace_states, trace_fuel, expr, meta,
                                       self.af_merge_count,
                                       self.af_runoff_execs) },
        |expr, meta| { sa_score_ablate_debug(&trace_states, trace_fuel, expr, meta,
                                       self.af_merge_count,
                                       self.af_runoff_execs) },

    );
    context.aligned_eggroll.replace(best);
    context.aligned_eggroll_repetitions.replace(meta);
  }
}
