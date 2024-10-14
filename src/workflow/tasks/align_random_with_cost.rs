use crate::anneal::choice_graph::*;
use crate::anneal::choice_path::*;
use crate::crel::eval::*;
use crate::eggroll::ast::*;
use crate::eggroll::cost_functions::sa2::*;
use crate::eggroll::to_crel::GuardedRepetitions;
use crate::workflow::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

pub struct AlignRandomWithCost {
  max_samples: usize,
}

impl AlignRandomWithCost {
  pub fn new() -> Self {
    AlignRandomWithCost {
      max_samples: 100000,
    }
  }

  fn random_path(&self, choice_graph: &ChoiceGraph<Eggroll>) -> Option<ChoicePath<Eggroll>> {
    let (tx, rx) = mpsc::channel();
    thread::scope(|scope| {
      scope.spawn(|| {
        let path = choice_graph.random_path(&|_| true);
        tx.send(path).unwrap()
      });
    });
    match rx.recv_timeout(Duration::from_secs(10)) {
      Ok(path) => Some(path),
      _ => None,
    }
  }

  fn to_rec_expr(&self, path: &ChoicePath<Eggroll>) -> Option<RecExpr<Eggroll>> {
    let (tx, rx) = mpsc::channel();
    thread::scope(|scope| {
      scope.spawn(|| {
        let expr = path.to_rec_expr();
        tx.send(expr).unwrap()
      });
    });
    match rx.recv_timeout(Duration::from_secs(10)) {
      Ok(path) => Some(path),
      _ => None,
    }
  }

  fn attempt_verification(&self, rec_expr: RecExpr<Eggroll>, context: &Context) -> Option<bool> {
    let (tx, rx) = mpsc::channel();
    thread::scope(|scope| {
      scope.spawn(|| {
        let mut new_ctx = context.clone();
        new_ctx.aligned_eggroll.replace(rec_expr);
        let mut verification_workflow = Workflow::new(&mut new_ctx);
        verification_workflow.add_task(AlignedCRel::new());
        verification_workflow.add_task(InvarsDaikon::new(Some(60)));
        verification_workflow.add_task(Houdafny::new(Some(60)));
        verification_workflow.execute();
        tx.send(if verification_workflow.context().timed_out { None } else {
          Some(verification_workflow.context().verified)
        }).unwrap();
      });
    });
    match rx.recv_timeout(Duration::from_secs(120)) {
      Ok(result) => result,
      _ => None,
    }
  }
}

impl Task for AlignRandomWithCost {
  fn name(&self) -> String { "align-random".to_string() }
  fn run(&self, context: &mut Context) {
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      .run(&crate::eggroll::rewrite::rewrites());
    let choice_graph = ChoiceGraph::new(&runner.egraph, |_| None);

    let num_trace_states = 10;
    let trace_fuel = 100000;

    let generator = context.unaligned_crel().fundefs.get(&"_test_gen".to_string());
    let decls = context.unaligned_crel().global_decls_and_params();
    let trace_states = rand_states_satisfying(
      num_trace_states, &context.spec().pre, Some(&decls), generator, 100000);

    let init_path = choice_graph.random_path(&|_| true);
    let init_expr = init_path.to_rec_expr();
    let init_reps = assign_random_reps(&init_expr);

    let mut best_reps = init_reps.clone();
    let mut best_expr = init_expr.clone();
    let mut best_cost = sa_score_ablate(&trace_states, trace_fuel, &init_expr, &init_reps, true, true);

    println!("Trying to verify with random elements.");
    for i in 0..self.max_samples {
      println!("Try {}", i);
      if best_cost < 0.0000001 {
        context.aligned_eggroll.replace(best_expr.clone());
        context.aligned_eggroll_repetitions.replace(best_reps.clone());
        println!("Found a zero cost term on try {}", i);
      }
      println!("  Finding random path...");
      let random_path = choice_graph.random_path(&|_| true);
      println!("  Converting to expression...");
      let random_expr = random_path.to_rec_expr();
      println!("  Assigning random reps...");
      let random_reps = assign_random_reps(&random_expr);
      println!("  Calculating cost...");
      let cost = sa_score_ablate(&trace_states, trace_fuel, &random_expr, &random_reps, true, true);
      if cost < best_cost {
        println!("New best at {}: {}", i, cost);
        best_reps = random_reps.clone();
        best_expr = random_expr.clone();
        best_cost = cost;
      }
    }

    context.aligned_eggroll.replace(best_expr);
    context.aligned_eggroll_repetitions.replace(best_reps);
  }
}

fn assign_random_reps(expr: &RecExpr<Eggroll>) -> GuardedRepetitions {
  let mut reps = GuardedRepetitions::new();
  for node in expr.as_ref() {
    match node {
      Eggroll::GuardedRepeat(children) => {
        // Since guardedRepeat x can be rewritten to (guardedRepeat x);(guardedRepeat x),
        // treat all guarded repeats as 1 unroll.
        match &expr.as_ref()[usize::from(children[0])] {
          Eggroll::RawString(id) => reps.set_repetitions(id.to_string(), 1),
          _ => (),
        }
      }
      Eggroll::GuardedRepeatWhile(children) => {
        // Cap at 10:1 ratio.
        match &expr.as_ref()[usize::from(children[0])] {
          Eggroll::RawString(id) => {
            reps.set_loop_repetitions(id.to_string(), 1, 1);
          },
          _ => (),
        }
      }
      _ => (),
    }
  }
  reps
}
