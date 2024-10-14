use crate::crel::count_loops::*;
use crate::crel::ast::CRel;
use crate::crel::eval::*;
use crate::eggroll::ast::*;
use crate::eggroll::to_crel;
use egg::*;

/// Computes and stores the score for a program execution.
pub struct SAScore2 {
  pub runoff_iterations: f32,
  pub merged_loops: f32,
  pub af_merge_count: bool,
  pub af_runoff_execs: bool,
}

impl SAScore2 {

  pub fn new(program: &CRel, trace: &Trace,
             af_merge_count: bool,
             af_runoff_execs: bool) -> Self {
    let runoff_iterations = score_runoff_iterations(program, trace);
    let merged_loops = score_merged_loops(program, trace);
    SAScore2 {
      runoff_iterations,
      merged_loops,
      af_merge_count,
      af_runoff_execs,
    }
  }

  pub fn total(&self) -> f32 {
    // if self.merged_loops > 0.75 {
    //   (0.5 * self.runoff_iterations) + (0.5 * self.merged_loops)
    // } else {
    //   self.runoff_iterations
    // }
    (0.5 * self.runoff_iterations) + (0.5 * self.merged_loops)
  }

  pub fn print(&self) {
    println!("SA Score:");
    println!("  Runoff Iterations: {}", self.runoff_iterations);
    println!("  Merged Loops: {}", self.merged_loops);
    println!("  ====================");
    println!("  Total: {}", self.total());
  }
}

/// The number of runoff loop iterations as a ratio of total loop iterations.
/// Goal: Favor programs whose post-lockstep "runoffs" do not execute.
fn score_runoff_iterations(program: &CRel, trace: &Trace) -> f32 {
  let mut total_count = 0;
  let mut runoff_count = 0;
  for item in &trace.items {
    match item.tag {
      Tag::LoopHead(..) => {
        total_count += 1;
      },
      Tag::MergedHead{..} => {
        total_count += 1;
      },
      Tag::RunoffHead {..} => {
        runoff_count += 1;
        total_count += 1;
      },
      _ => (),
    }
  }
  if total_count == 0 { 1.0 } else {
    (runoff_count as f32) / (total_count as f32)
  }
}

/// The number of unmerged loops as a percentage of total loops.
/// Goal: Favor programs which merge loops.
fn score_merged_loops(program: &CRel, trace: &Trace) -> f32 {
  let mut unmerged_count = 0;
  let mut merged_count = 0;
  for item in &trace.items {
    match item.tag {
      Tag::LoopStart(..) => {
        unmerged_count += 1;
      },
      Tag::MergedStart{..} => {
        merged_count += 1;
      },
      _ => (),
    }
  }
  let total_count = merged_count + unmerged_count;
  if total_count == 0 { 1.0 } else {
    (unmerged_count as f32) / (total_count as f32)
  }
}

//fn score_merged_ifs(program: &CRel, trace: &Trace) -> f32 {
//}

pub fn sa_score_ablate(trace_states: &Vec<State>,
                       trace_fuel: usize,
                       expr: &RecExpr<Eggroll>,
                       repetitions: &to_crel::GuardedRepetitions,
                       af_merge_count: bool,
                       af_runoff_execs: bool) -> f32 {
  let crel = crate::eggroll::to_crel::eggroll_to_crel(&expr.to_string(),
                                                      &to_crel::Config::default(),
                                                      repetitions);
  let fundefs = crate::crel::fundef::extract_fundefs(&crel).1;
  let body = fundefs
    .get(&"main".to_string())
    .expect("Missing main function")
    .body.clone();

  let score_state = |state: &State| -> f32 {
    let exec = run(&body, state.clone(), trace_fuel, Some(&fundefs));
    SAScore2::new(&crel, &exec.trace, af_merge_count, af_runoff_execs).total()
  };

  let score = trace_states.iter().map(score_state).sum::<f32>() / (trace_states.len() as f32);
  score
}

pub fn sa_score_ablate_debug(trace_states: &Vec<State>,
                             trace_fuel: usize,
                             expr: &RecExpr<Eggroll>,
                             repetitions: &to_crel::GuardedRepetitions,
                             af_merge_count: bool,
                             af_runoff_execs: bool) {
  let crel = crate::eggroll::to_crel::eggroll_to_crel(&expr.to_string(),
                                                      &to_crel::Config::default(),
                                                      repetitions);
  let fundefs = crate::crel::fundef::extract_fundefs(&crel).1;
  let body = fundefs
    .get(&"main".to_string())
    .expect("Missing main function")
    .body.clone();

  for state in trace_states {
    let exec = run(&body, state.clone(), trace_fuel, Some(&fundefs));
    SAScore2::new(&crel, &exec.trace, af_merge_count, af_runoff_execs).print();
  }
}

pub fn sa_score(trace_states: &Vec<State>,
                trace_fuel: usize,
                expr: &RecExpr<Eggroll>,
                repetitions: &to_crel::GuardedRepetitions) -> f32 {
  sa_score_ablate(trace_states, trace_fuel, expr, repetitions, true, true)
}
