use crate::anneal::*;
use crate::crel::eval::*;
use crate::eggroll::cost_functions::sa::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;

pub struct AlignSa {
  start_random: bool,
  max_iterations: usize,
  af_relation_size: bool,
  af_update_matching: bool,
  af_loop_head_matching: bool,
  af_loop_double_updates: bool,
  af_loop_executions: bool,
}

impl AlignSa {
  pub fn new(start_random: bool, max_iterations: usize) -> Self {
    AlignSa {
      start_random,
      max_iterations,
      af_relation_size: true,
      af_update_matching: true,
      af_loop_head_matching: true,
      af_loop_double_updates: true,
      af_loop_executions: true,
    }
  }

  pub fn ablate_relation_size(&mut self) {
    self.af_relation_size = false;
  }

  pub fn ablate_update_matching(&mut self) {
    self.af_update_matching = false;
  }

  pub fn ablate_loop_head_matching(&mut self) {
    self.af_loop_head_matching = false;
  }

  pub fn ablate_loop_double_updates(&mut self) {
    self.af_loop_double_updates = false;
  }

  pub fn ablate_loop_executions(&mut self) {
    self.af_loop_executions = false;
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
    let trace_fuel = 100000000;

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
                                  |expr| { sa_score_ablate(&trace_states, trace_fuel, expr,
                                                           self.af_relation_size,
                                                           self.af_update_matching,
                                                           self.af_loop_head_matching,
                                                           self.af_loop_double_updates,
                                                           self.af_loop_executions) },
                                  |expr| { sa_score_ablate_debug(&trace_states, trace_fuel, expr,
                                                           self.af_relation_size,
                                                           self.af_update_matching,
                                                           self.af_loop_head_matching,
                                                           self.af_loop_double_updates,
                                                           self.af_loop_executions) },

    );
    context.aligned_eggroll.replace(best);
  }
}
