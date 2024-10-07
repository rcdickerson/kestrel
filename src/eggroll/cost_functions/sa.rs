use crate::crel::count_loops::*;
use crate::crel::ast::CRel;
use crate::crel::eval::*;
use crate::eggroll::ast::*;
use crate::eggroll::to_crel;
use egg::*;
use std::collections::HashMap;
use std::collections::HashSet;

/// Computes and stores the score for a program execution.
pub struct SAScore {
  pub relation_size: f32,
  pub update_matching: f32,
  pub loop_head_matching: f32,
  pub loop_double_updates: f32,
  pub loop_executions: f32,
}

impl SAScore {

  pub fn new(program: &CRel, trace: &Trace) -> Self {
    let rel_change_summary = relations_change_summary(trace);
    let loop_change_summaries = loop_change_summaries(trace);
    let relation_size = score_avg_rel_size(&rel_change_summary);
    let update_matching = score_rel_update_left_right_match(&rel_change_summary);
    let (loop_head_matching, loop_double_updates) =
      score_loop_head_similarity(&loop_change_summaries);
    let loop_executions = score_loop_executions(program, trace);
    SAScore {
      relation_size,
      update_matching,
      loop_head_matching,
      loop_double_updates,
      loop_executions,
    }
  }

  /// Constructor for ablation study.
  pub fn new_ablation(program: &CRel, trace: &Trace,
                      af_relation_size: bool,
                      af_update_matching: bool,
                      af_loop_head_matching: bool,
                      af_loop_double_updates: bool,
                      af_loop_executions: bool) -> Self {
    let rel_change_summary = relations_change_summary(trace);
    let loop_change_summaries = loop_change_summaries(trace);
    let relation_size = if af_relation_size { score_avg_rel_size(&rel_change_summary) } else { 0.0 };
    let update_matching = if af_update_matching { score_rel_update_left_right_match(&rel_change_summary) } else { 0.0 };
    let (loop_head_matching, loop_double_updates) =
      if af_loop_head_matching && af_loop_double_updates {
        score_loop_head_similarity(&loop_change_summaries)
      } else if af_loop_head_matching {
        let (lhm, _) = score_loop_head_similarity(&loop_change_summaries);
        (lhm, 0.0)
      } else if af_loop_double_updates {
        let (_, ldu) = score_loop_head_similarity(&loop_change_summaries);
        (0.0, ldu)
      } else {
        (0.0, 0.0)
      };
    let loop_executions = if af_loop_executions { score_loop_executions(program, trace) } else { 0.0 };
    SAScore {
      relation_size,
      update_matching,
      loop_head_matching,
      loop_double_updates,
      loop_executions,
    }
  }

  pub fn total(&self) -> f32 {
    (0.2 * self.relation_size)
      + (0.2 * self.update_matching)
      + (0.2 * self.loop_head_matching)
      + (0.2 * self.loop_double_updates)
      + (0.2 * self.loop_executions)
  }

  pub fn print(&self) {
    println!("SA Score:");
    println!("  Relation Size:        {}", self.relation_size);
    println!("  Relation Matching:    {}", self.update_matching);
    println!("  Loop Head Matching:   {}", self.loop_head_matching);
    println!("  Loop Double Updates:  {}", self.loop_double_updates);
    println!("  Loop Executions:      {}", self.loop_executions);
    println!("  ====================");
    println!("  Total: {}", self.total());
  }
}

/// Summarizes the state changes that occurred accross a collection of states.
#[derive(Clone, Debug)]
struct VariableChangeSummary {
  /// The number of state changes being summarized.
  num_state_changes: usize,

  // Maps go from variable name -> state number -> value at that state.
  left_deltas:  HashMap<String, HashMap<usize, TraceStateValue>>,
  right_deltas: HashMap<String, HashMap<usize, TraceStateValue>>,

  /// All the left and right variable names (without the l_ and r_ prefixes)
  /// encountered in the summarized states.
  all_vars: HashSet<String>,

  /// The variables (without l_ and r_ prefixes) whose value was changed on
  /// the left, on the right, or both somewhere in the summarized states.
  changed_vars: HashSet<String>,
}
impl<'a> VariableChangeSummary {
  pub fn new(states: &Vec<(&'a TraceState, &'a TraceState)>) -> Self {
    let mut num_state_changes = 0;
    let mut left_deltas:  HashMap<String, HashMap<usize, TraceStateValue>> = HashMap::new();
    let mut right_deltas: HashMap<String, HashMap<usize, TraceStateValue>> = HashMap::new();
    let mut all_vars:     HashSet<String> = HashSet::new();
    let mut changed_vars: HashSet<String> = HashSet::new();

    for (state_num, (before_state, after_state)) in states.iter().enumerate() {
      num_state_changes += 1;
      for (exec_var, after_value) in after_state.iter() {
        if exec_var.len() < 3 { continue; } // "Global" vars are not prefixed by execution, skip.

        let(exec, var) = (&exec_var[..1], &exec_var[2..]);
        let delta_map = match exec {
          "l" => &mut left_deltas,
          "r" => &mut right_deltas,
          _ => continue,
        };
        all_vars.insert(var.to_string());

        let (delta, initialized) = match before_state.get(exec_var) {
          None => (after_value.clone(), true),
          Some(before_value) => (after_value.minus(before_value), false),
        };
        if !delta.is_zero() || initialized {
          changed_vars.insert(var.to_string());
          match delta_map.get_mut(var) {
            None => {
              let mut map = HashMap::new();
              map.insert(state_num, delta);
              delta_map.insert(var.to_string(), map);
            }
            Some(map) => { map.insert(state_num, delta); },
          }
        }
      }
    }
    VariableChangeSummary {
      num_state_changes,
      left_deltas,
      right_deltas,
      all_vars,
      changed_vars,
    }
  }

  pub fn left_delta(&self, var: &String, state_num: usize) -> Option<&TraceStateValue> {
    self.left_deltas.get(var).and_then(|dmap| dmap.get(&state_num))
  }

  pub fn right_delta(&self, var: &String, state_num: usize) -> Option<&TraceStateValue> {
    self.right_deltas.get(var).and_then(|dmap| dmap.get(&state_num))
  }

  pub fn change_sequences(&self, side: Side) -> HashMap<String, Vec<&TraceStateValue>> {
    let mut sequences: HashMap<String, Vec<&TraceStateValue>> = HashMap::new();
    for change_num in 0..self.num_state_changes {
      for var in &self.changed_vars {
        let deltas = match &side {
          Side::Left => &self.left_deltas,
          Side::Right => &self.right_deltas,
        };
        deltas.get(var).map(|dmap| {
          dmap.get(&change_num).map(|tsv| {
            match sequences.get_mut(var) {
              None => {
                let mut seq = Vec::new();
                seq.push(tsv);
                sequences.insert(var.clone(), seq);
              },
              Some(seq) => { seq.push(tsv); }
            }
          })
        });
      }
    }
    sequences
  }
}

enum Side { Left, Right }

fn relations_change_summary(trace: &Trace) -> VariableChangeSummary {
  let states: &mut Vec<(&TraceState, &TraceState)> = &mut Vec::new();
  let mut start_state = None;
  for item in &trace.items {
    match item.tag {
      Tag::RelationStart => start_state = Some(&item.state),
      Tag::RelationEnd => match start_state {
        None => panic!("Saw RelationEnd without a RelationStart"),
        Some(start_state) => states.push((start_state, &item.state)),
      },
      _ => (),
    }
  }
  VariableChangeSummary::new(states)
}

fn loop_change_summaries(trace: &Trace) -> Vec<VariableChangeSummary> {
  let mut trace_segments_by_loop = HashMap::new();
  for item in &trace.items {
    match item.tag {
      Tag::LoopStart(id)
        | Tag::MergedStart{id,..}
        | Tag::RunoffStart{id,..}
        | Tag::LoopHead(id)
        | Tag::MergedHead{id,..}
        | Tag::RunoffHead{id,..}
        | Tag::LoopEnd(id)
        | Tag::MergedEnd{id,..}
        | Tag::RunoffEnd{id,..} => match trace_segments_by_loop.get_mut(&id) {
          None => { trace_segments_by_loop.insert(id, vec!(item)); },
          Some(vec) => vec.push(item),
      },
      _ => (),
    }
  }

  let mut summaries: Vec<VariableChangeSummary> = Vec::new();

  for loop_trace in trace_segments_by_loop.values() {
    let mut cur_state: Option<&TraceState> = None;
    let mut states: Vec<(&TraceState, &TraceState)> = Vec::new();
    for item in loop_trace {
      match item.tag {
        Tag::LoopHead(_) | Tag::MergedHead{..} | Tag::RunoffHead{..} => match cur_state {
          None => cur_state = Some(&item.state),
          Some(state) => {
            states.push((state, &item.state));
            cur_state = Some(&item.state);
          },
        },
        _ => (),
      }
    }
    if !states.is_empty() {
      summaries.push(VariableChangeSummary::new(&states));
    }
  }
  summaries
}

/// Average number of variables changed per relation as a percent of total
/// changed variables across all relations.
/// Goal: Favor programs with smaller state changes per relation.
fn score_avg_rel_size(summary: &VariableChangeSummary) -> f32 {
  let total_vars = summary.all_vars.len();
  if total_vars == 0 { return 0.0; }

  let num_rels = summary.num_state_changes;
  if num_rels == 0 { return 0.0; }

  let mut change_counts = Vec::new();
  for rel_num in 0..num_rels {
    let mut count = 0;
    for var in &summary.changed_vars {
      let changed_left = summary.left_delta(var, rel_num).is_some();
      let changed_right = summary.right_delta(var, rel_num).is_some();
      if changed_left || changed_right { count += 1; }
    }
    change_counts.push(count);
  }
  if change_counts.is_empty() { return 0.0 }
  return (change_counts.iter().sum::<i32>() as f32) / (num_rels as f32) / (total_vars as f32)
}

/// (One minus the) ratio of variables updated on both the left and right to
/// total variables updated. Returned ratio is the average across all relations.
/// Goal: Favor programs whose relations update both left and right variables.
fn score_rel_update_left_right_match(summary: &VariableChangeSummary) -> f32 {
  let mut ratios: Vec<f32> = Vec::new();
  for rel_num in 0..summary.num_state_changes {
    let (mut num_changes, mut num_double_changes) = (0, 0);
    for var in &summary.changed_vars {
      let changed_left = summary.left_delta(var, rel_num).is_some();
      let changed_right = summary.right_delta(var, rel_num).is_some();
      num_changes        += if changed_left || changed_right {1} else {0};
      num_double_changes += if changed_left && changed_right {1} else {0};
    }
    if num_changes == 0 { ratios.push(1.0) } else {
      ratios.push((num_double_changes as f32) / (num_changes as f32));
    }
  }
  if ratios.is_empty() { 0.0 } else {
    1.0 - (ratios.iter().sum::<f32>() / (ratios.len() as f32))
  }
}

/// Two measures of similarity for loop head states:
///   1. (One minus) the ratio of variables which changed by the same
///      amount from loop head to loop head to the total number of variables
///      changed in the loop, and
///   2. (One minus) the ratio of updated variables which were updated on both
///      the left and the right side over the course of the loop.
/// Goal: Favor programs whose loops update variables in a way that makes it
///   easy to infer invariants.
fn score_loop_head_similarity(summaries: &Vec<VariableChangeSummary>) -> (f32, f32) {
  let mut exact_ratios: Vec<f32> = Vec::new();
  let mut double_update_ratios: Vec<f32> = Vec::new();
  for loop_summary in summaries {
    if loop_summary.changed_vars.is_empty() { continue; }
    let l_seqs = loop_summary.change_sequences(Side::Left);
    let r_seqs = loop_summary.change_sequences(Side::Right);
    let mut exact_count = 0;
    let mut updated_on_left = HashSet::new();
    let mut updated_on_right = HashSet::new();
    for var in &loop_summary.changed_vars {
      let all_same_l = l_seqs.get(var).map(|seq| {
        seq.windows(2).all(|w| w[0] == w[1])
      }).unwrap_or(false);
      let all_same_r = r_seqs.get(var).map(|seq| {
        seq.windows(2).all(|w| w[0] == w[1])
      }).unwrap_or(false);
      if all_same_l && all_same_r { exact_count += 1; }

      for head_num in 0..loop_summary.num_state_changes {
        if loop_summary.left_delta(var, head_num).is_some() {
          updated_on_left.insert(var);
          continue;
        }
      }
      for head_num in 0..loop_summary.num_state_changes {
        if loop_summary.right_delta(var, head_num).is_some() {
          updated_on_right.insert(var);
          continue;
        }
      }
    }
    let num_double_updates = updated_on_left.intersection(&updated_on_right).collect::<Vec<_>>().len();

    exact_ratios.push((exact_count as f32) / (loop_summary.changed_vars.len() as f32));
    double_update_ratios.push((num_double_updates as f32) / (loop_summary.changed_vars.len() as f32));
  }
  let exact_avg = if exact_ratios.is_empty() {0.0} else {
    exact_ratios.iter().sum::<f32>() / (exact_ratios.len() as f32)
  };
  let double_update_avg = if double_update_ratios.is_empty() {0.0} else {
    double_update_ratios.iter().sum::<f32>() / (double_update_ratios.len() as f32)
  };
  (1.0 - exact_avg, 1.0 - double_update_avg)
}

/// The number of merged loops without runoff executions as a
/// percentage of total loops.
/// Goal: Favor programs whose post-lockstep "runoffs" do not execute.
fn score_loop_executions(program: &CRel, trace: &Trace) -> f32 {
  let merged_no_runoffs = trace.count_merged_loops_without_runoff_execs();
  let total_merged = program.count_loops().num_merged;
  if total_merged == 0 { 1.0 } else {
    //println!("Score: {}", (merged_no_runoffs as f32) / (total_merged as f32));
    (merged_no_runoffs as f32) / (total_merged as f32)
  }
}

pub fn sa_score_ablate(trace_states: &Vec<State>,
                       trace_fuel: usize,
                       expr: &RecExpr<Eggroll>,
                       repetitions: &to_crel::GuardedRepetitions,
                       af_relation_size: bool,
                       af_update_matching: bool,
                       af_loop_head_matching: bool,
                       af_loop_double_updates: bool,
                       af_loop_executions: bool) -> f32 {
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
    SAScore::new_ablation(&crel, &exec.trace,
                          af_relation_size,
                          af_update_matching,
                          af_loop_head_matching,
                          af_loop_double_updates,
                          af_loop_executions).total()
  };

  trace_states.iter().map(score_state).sum::<f32>() / (trace_states.len() as f32)
}

pub fn sa_score_ablate_debug(trace_states: &Vec<State>,
                             trace_fuel: usize,
                             expr: &RecExpr<Eggroll>,
                             repetitions: &to_crel::GuardedRepetitions,
                             af_relation_size: bool,
                             af_update_matching: bool,
                             af_loop_head_matching: bool,
                             af_loop_double_updates: bool,
                             af_loop_executions: bool) {
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
    SAScore::new_ablation(&crel, &exec.trace,
                          af_relation_size,
                          af_update_matching,
                          af_loop_head_matching,
                          af_loop_double_updates,
                          af_loop_executions).print();
  }
}

pub fn sa_score(trace_states: &Vec<State>,
                trace_fuel: usize,
                expr: &RecExpr<Eggroll>,
                repetitions: &to_crel::GuardedRepetitions) -> f32 {
  sa_score_ablate(trace_states, trace_fuel, expr, repetitions, true, true, true, true, true)
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn test_score_avg_rel_size() {
    let left_deltas = HashMap::from([
      ("a".to_string(), HashMap::from(
        [(1, TraceStateValue::Array(vec!(TraceStateValue::Int(0),
                                         TraceStateValue::Int(7)))),
         (2, TraceStateValue::Array(vec!(TraceStateValue::Int(7),
                                         TraceStateValue::Int(0))))])),
      ("x".to_string(), HashMap::from([(0, TraceStateValue::Int(1)),
                                       (1, TraceStateValue::Int(0))])),
      ("y".to_string(), HashMap::from([(1, TraceStateValue::Int(1))])),
    ]);
    let right_deltas = HashMap::from([
      ("b".to_string(), HashMap::from(
        [(1, TraceStateValue::Array(vec!(TraceStateValue::Int(0),
                                         TraceStateValue::Int(7))))])),
    ]);
    let all_vars = HashSet::from(["a".to_string(),
                                  "b".to_string(),
                                  "c".to_string(),
                                  "d".to_string(),
                                  "e".to_string(),
                                  "v".to_string(),
                                  "w".to_string(),
                                  "x".to_string(),
                                  "y".to_string(),
                                  "z".to_string()]);
    let changed_vars = HashSet::from(["a".to_string(),
                                      "b".to_string(),
                                      "x".to_string(),
                                      "y".to_string()]);
    let summary = VariableChangeSummary {
      num_state_changes: 3,
      left_deltas,
      right_deltas,
      all_vars,
      changed_vars,
    };

    // 10 total variables.
    // In the first relation, 1 was changed => 0.1 score
    // In the second relation, 4 were changed => 0.4 score
    // In the third relation, 1 was changed => 0.1 score
    // Average score: 0.2
    let expected: f32 = 0.2;
    assert_eq!(score_avg_rel_size(&summary), expected);
  }

  #[test]
  fn test_rel_update_lr() {
    let left_deltas = HashMap::from([
      ("a".to_string(), HashMap::from(
        [(0, TraceStateValue::Array(vec!(TraceStateValue::Int(1),
                                         TraceStateValue::Int(1)))),
         (1, TraceStateValue::Array(vec!(TraceStateValue::Int(7),
                                         TraceStateValue::Int(7))))])),
      ("b".to_string(), HashMap::from(
        [(0, TraceStateValue::Array(vec!(TraceStateValue::Int(2),
                                         TraceStateValue::Int(3)))),
         (2, TraceStateValue::Array(vec!(TraceStateValue::Int(7),
                                         TraceStateValue::Int(0))))])),
      ("x".to_string(), HashMap::from([(0, TraceStateValue::Int(1)),
                                       (2, TraceStateValue::Int(4))])),
      ("y".to_string(), HashMap::from([(0, TraceStateValue::Int(4)),
                                       (2, TraceStateValue::Int(5))])),
    ]);
    let right_deltas = HashMap::from([
      ("a".to_string(), HashMap::from(
        [(1, TraceStateValue::Array(vec!(TraceStateValue::Int(3),
                                         TraceStateValue::Int(3)))),
         (2, TraceStateValue::Array(vec!(TraceStateValue::Int(7),
                                         TraceStateValue::Int(3))))])),
      ("b".to_string(), HashMap::from(
        [(0, TraceStateValue::Array(vec!(TraceStateValue::Int(0),
                                         TraceStateValue::Int(5)))),
         (2, TraceStateValue::Array(vec!(TraceStateValue::Int(7),
                                         TraceStateValue::Int(2))))])),
      ("x".to_string(), HashMap::from([(1, TraceStateValue::Int(1)),
                                       (2, TraceStateValue::Int(4))])),
      ("y".to_string(), HashMap::from([(2, TraceStateValue::Int(5))])),
    ]);
    let all_vars = HashSet::from(["a".to_string(),
                                  "b".to_string(),
                                  "c".to_string(),
                                  "d".to_string(),
                                  "e".to_string(),
                                  "v".to_string(),
                                  "w".to_string(),
                                  "x".to_string(),
                                  "y".to_string(),
                                  "z".to_string()]);
    let changed_vars = HashSet::from(["a".to_string(),
                                      "b".to_string(),
                                      "x".to_string(),
                                      "y".to_string()]);
    let summary = VariableChangeSummary {
      num_state_changes: 3,
      left_deltas,
      right_deltas,
      all_vars,
      changed_vars,
    };

    // 10 total variables.
    // In the first relation, 4 variables updated, 1 on both sides => 0.75 score
    // In the second relation, 2 variables updated, 1 on both sides => 0.5 score
    // In the third relation, 4 variables updated, 3 on both sides => 0.25 score
    // Average score: 0.5
    let expected: f32 = 0.5;
    assert_eq!(score_rel_update_left_right_match(&summary), expected);
  }

  #[test]
  fn test_loop_head_similarity() {
    let all_vars = HashSet::from(["a".to_string(),
                                  "b".to_string(),
                                  "c".to_string(),
                                  "d".to_string(),
                                  "e".to_string(),
                                  "v".to_string(),
                                  "w".to_string(),
                                  "x".to_string(),
                                  "y".to_string(),
                                  "z".to_string()]);
    let summary1 = VariableChangeSummary {
      num_state_changes: 3,
      left_deltas: HashMap::from([
        ("a".to_string(), HashMap::from(  // Exact
          [(0, TraceStateValue::Array(vec!(TraceStateValue::Int(3),
                                           TraceStateValue::Int(4)))),
           (1, TraceStateValue::Array(vec!(TraceStateValue::Int(3),
                                           TraceStateValue::Int(4)))),
           (2, TraceStateValue::Array(vec!(TraceStateValue::Int(3),
                                           TraceStateValue::Int(4))))])),
        ("b".to_string(), HashMap::from(  // Nonlinear
          [(0, TraceStateValue::Array(vec!(TraceStateValue::Int(2),
                                           TraceStateValue::Int(3)))),
           (1, TraceStateValue::Array(vec!(TraceStateValue::Int(3),
                                           TraceStateValue::Int(3)))),
           (2, TraceStateValue::Array(vec!(TraceStateValue::Int(6),
                                           TraceStateValue::Int(3))))])),
        ("x".to_string(), HashMap::from(  // Exact
          [(0, TraceStateValue::Int(1)),
           (1, TraceStateValue::Int(1)),
           (2, TraceStateValue::Int(1))])),
        ("y".to_string(), HashMap::from(  // Exact here, linear on right => linear
          [(0, TraceStateValue::Int(4)),
           (1, TraceStateValue::Int(4)),
           (2, TraceStateValue::Int(4))])),
      ]),
      right_deltas: HashMap::from([
        ("a".to_string(), HashMap::from(  // Exact
          [(0, TraceStateValue::Array(vec!(TraceStateValue::Int(1),
                                           TraceStateValue::Int(2)))),
           (1, TraceStateValue::Array(vec!(TraceStateValue::Int(1),
                                           TraceStateValue::Int(2)))),
           (2, TraceStateValue::Array(vec!(TraceStateValue::Int(1),
                                           TraceStateValue::Int(2))))])),
        ("x".to_string(), HashMap::from(  // Exact
          [(0, TraceStateValue::Int(1)),
           (1, TraceStateValue::Int(1)),
           (2, TraceStateValue::Int(1))])),
        ("y".to_string(), HashMap::from(  // Linear
          [(0, TraceStateValue::Int(4)),
           (1, TraceStateValue::Int(5)),
           (2, TraceStateValue::Int(6))])),
      ]),
      all_vars: all_vars.clone(),
      changed_vars: HashSet::from(["a".to_string(),
                                   "b".to_string(),
                                   "x".to_string(),
                                   "y".to_string()]),
    };

    let summary2 = VariableChangeSummary {
      num_state_changes: 3,
      left_deltas: HashMap::from([
        ("a".to_string(), HashMap::from(  // Linear
          [(0, TraceStateValue::Array(vec!(TraceStateValue::Int(3),
                                           TraceStateValue::Int(4)))),
           (1, TraceStateValue::Array(vec!(TraceStateValue::Int(4),
                                           TraceStateValue::Int(5)))),
           (2, TraceStateValue::Array(vec!(TraceStateValue::Int(5),
                                           TraceStateValue::Int(6))))])),
        ("x".to_string(), HashMap::from(  // Non-linear
          [(0, TraceStateValue::Int(1)),
           (1, TraceStateValue::Int(3)),
           (2, TraceStateValue::Int(2))])),
      ]),
      right_deltas: HashMap::from([
        ("x".to_string(), HashMap::from(  // Exact here, nonlinear on left => nonlinear
          [(0, TraceStateValue::Int(1)),
           (1, TraceStateValue::Int(1)),
           (2, TraceStateValue::Int(1))])),
      ]),
      all_vars: all_vars.clone(),
      changed_vars: HashSet::from(["a".to_string(),
                                   "x".to_string()]),
    };

    let summaries = vec!(summary1, summary2);

    // 2 total loops.
    // The first loop updates four variables.
    //   - Two variables change exactly => 0.5 change score
    //   - Three variables are updated on both sides => 0.25 LR score
    // The second loop updates two variables.
    //   - No variables change exactly => 1 change score
    //   - One variable is updated on both sides => 0.5 LR score
    // Averages: (0.75, 0.375)
    let expected = (0.75, 0.375);
    assert_eq!(score_loop_head_similarity(&summaries), expected);
  }
}
