use crate::crel::count_loops::*;
use crate::crel::ast::CRel;
use crate::crel::eval::*;
use crate::crel::state::State;
use crate::crel::trace::Trace;
use crate::eggroll::ast::*;
use egg::*;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub struct LoopCost {
  num_loops: usize,
  ast_size: usize,
}

impl LoopCost {
  pub fn plus(&self, other: LoopCost) -> LoopCost {
    LoopCost {
      num_loops: self.num_loops + other.num_loops,
      ast_size: self.ast_size + other.ast_size,
    }
  }
}

impl PartialOrd for LoopCost {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    let loop_cmp = self.num_loops.cmp(&other.num_loops);
    match loop_cmp {
      Ordering::Equal => Some(self.ast_size.cmp(&other.ast_size)),
      _ => Some(loop_cmp),
    }
  }
}

pub struct LocalCountLoops;
impl CostFunction<Eggroll> for LocalCountLoops {
    type Cost = LoopCost;
    fn cost<C>(&mut self, enode: &Eggroll, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
      let loop_cost = match enode {
        Eggroll::While(_) => 1,
        Eggroll::WhileNoBody(_) => 1,
        Eggroll::WhileLockstep(_) => 1,
        _ => 0,
      };
      let ast_cost = match enode {
        Eggroll::Rel(children) if children.iter().min() == children.iter().max() => 0,
        _ => 1,
      };
      let init_cost = LoopCost{ num_loops: loop_cost, ast_size: ast_cost };
      enode.fold(init_cost, |sum, id| sum.plus(costs(id)))
    }
}

struct StatesSummary {
  l_vals: HashMap<String, Vec<i32>>,
  r_vals: HashMap<String, Vec<i32>>,
  l_diffs: HashMap<String, Vec<i32>>,
  r_diffs: HashMap<String, Vec<i32>>,
  changed_vars: HashSet<String>,
}

fn summarize_states(states: &Vec<State>) -> StatesSummary {
  let mut l_vals : HashMap<String, Vec<i32>> = HashMap::new();
  let mut r_vals : HashMap<String, Vec<i32>> = HashMap::new();
  for state in states {
    for (exec_var, val) in state {
      let(exec, var) = (&exec_var[..1], &exec_var[2..]);
      match exec {
        "l" => {
          let mut seq = match l_vals.get(var) {
            None => Vec::new(),
            Some(seq) => seq.clone(),
          };
          seq.push(val.clone());
          l_vals.insert(var.to_string(), seq);
        },
        "r" => {
          let mut seq = match r_vals.get(var) {
            None => Vec::new(),
            Some(seq) => seq.clone(),
          };
          seq.push(val.clone());
          r_vals.insert(var.to_string(), seq);
        },
        _ => continue,
      }
    }
  }

  let mut l_diffs = HashMap::new();
  for (k,v) in &l_vals {
    let diffs = v.windows(2).map(|w| w[1] - w[0]).collect::<Vec<i32>>();
    if diffs.len() > 0 && !diffs.iter().all(|i| *i == 0) {
      l_diffs.insert(k.clone(), diffs);
    }
  }

  let mut r_diffs = HashMap::new();
  for (k,v) in &r_vals {
    let diffs = v.windows(2).map(|w| w[1] - w[0]).collect::<Vec<i32>>();
    if diffs.len() > 0 && !diffs.iter().all(|i| *i == 0) {
      r_diffs.insert(k.clone(), diffs);
    }
  }

  let l_vars : HashSet<String> = HashSet::from_iter(l_diffs.keys().map(|v| v.clone()));
  let r_vars : HashSet<String> = HashSet::from_iter(r_diffs.keys().map(|v| v.clone()));
  let changed_vars = l_vars.union(&r_vars).map(|v| v.clone()).collect::<HashSet<String>>();

  StatesSummary { l_vals, r_vals, l_diffs, r_diffs, changed_vars }
}

/// Average number of state changes in a relation as a percentage of
/// total trace length.
fn score_avg_rel_size(trace: &Trace) -> f32 {
  let rel_states = trace.relation_states();
  let num_rels = rel_states.len();
  if num_rels == 0 { 1.0 } else {
    let sum = rel_states.iter().map(|v| v.len()).sum::<usize>();
    (sum as f32) / (num_rels as f32) / (trace.len() as f32)
  }
}

/// Average percent of updated variables per relation whose values
/// changed by the same value.
fn score_rel_update_match(trace: &Trace) -> f32 {
  let rel_states = trace.relation_states();
  if rel_states.len() == 0 {
    1.0
  } else {
    let mut match_sum : f32 = 0.0;
    for states in &rel_states {
      let mut matches = 0;
      let summary = summarize_states(states);
      if summary.changed_vars.len() == 0 { continue; }
      for var in &summary.changed_vars {
        let left = summary.l_diffs.get(var);
        let right = summary.r_diffs.get(var);
        match (left, right) {
          (Some(_), Some(_)) => matches += 1,
          _ => (),
        }
      }
      match_sum += (matches as f32) / (summary.changed_vars.len() as f32);
    }
    1.0 - ((match_sum as f32) / (rel_states.len() as f32))
  }
}

fn score_loop_similarity(trace: &Trace) -> (f32, f32) {
  let loop_heads = trace.loop_heads();

  let mut matching_sum : f32 = 0.0;
  let mut similarity_sum : f32 = 0.0;
  for head_states in &loop_heads {
    if head_states.len() == 0 { continue }

    let summary = summarize_states(head_states);
    if summary.changed_vars.len() == 0 { continue; }

    let mut matching = 0;
    let mut similar = 0;
    for var in &summary.changed_vars {
      let left = summary.l_diffs.get(var);
      let right = summary.r_diffs.get(var);
      match (left, right) {
        (None, _) => continue,
        (_, None) => continue,
        (Some(left), Some(right)) => {
          let ratios = left.iter().zip(right)
            .map(|(l,r)| (l / r, l % r))
            .collect::<Vec<(i32, i32)>>();
          let homogeneous = ratios.iter()
            .all(|(d,m)| *d == ratios[0].0 && *m == ratios[0].1);
          if summary.l_vals.get(var) == summary.r_vals.get(var) {
            matching += 1;
          }
          if homogeneous {
            similar += 1;
          }
        },
      }
    }
    matching_sum += (matching as f32) / (summary.changed_vars.len() as f32);
    similarity_sum += (similar as f32) / (summary.changed_vars.len() as f32);
  }
  if loop_heads.len() == 0 { (0.0, 0.0) } else {
    let score_matching = 1.0 - (matching_sum / loop_heads.len() as f32);
    let score_similarity = 1.0 - (similarity_sum / loop_heads.len() as f32);
    (score_matching, score_similarity)
  }
}

fn score_loop_executions(program: &CRel, trace: &Trace) -> f32 {
  let num_executed_loops = trace.count_executed_loops();
  let num_loops = program.count_loops();
  if num_loops == 0 { 0.0 } else {
    (num_executed_loops as f32) / (num_loops as f32)
  }
}

pub struct SAScore {
  pub relation_size: f32,
  pub update_matching: f32,
  pub loop_matching: f32,
  pub loop_similarity: f32,
  pub loop_executions: f32,
}

impl SAScore {

  pub fn score_trace(program: &CRel, trace: &Trace) -> Self {
    let relation_size = score_avg_rel_size(&trace);
    let update_matching = score_rel_update_match(&trace);
    let (loop_matching, loop_similarity) = score_loop_similarity(&trace);
    let loop_executions = score_loop_executions(&program, &trace);
    SAScore {
      relation_size,
      update_matching,
      loop_matching,
      loop_similarity,
      loop_executions,
    }
  }

  pub fn total(&self) -> f32 {
    (0.2 * self.relation_size)
      + (0.2 * self.update_matching)
      + (0.2 * self.loop_matching)
      + (0.2 * self.loop_similarity)
      + (0.2 * self.loop_executions)
  }

  pub fn print(&self) {
    println!("SA Score:");
    println!("  Relation Size:     {}", self.relation_size);
    println!("  Relation Matching: {}", self.update_matching);
    println!("  Loop Matching:     {}", self.loop_matching);
    println!("  Loop Similarity:   {}", self.loop_similarity);
    println!("  Loop Executions:   {}", self.loop_executions);
    println!("  ====================");
    println!("  Total: {}", self.total());
  }
}

pub fn sa_score(trace_states: &Vec<State>, expr: RecExpr<Eggroll>) -> f32 {
  let crel = crate::eggroll::to_crel::eggroll_to_crel(&expr.to_string());
  let body = crate::crel::fundef::extract_fundefs(&crel).1
    .get(&"main".to_string())
    .expect("Missing main function")
    .body.clone();

  let score_state = |state: &State| -> f32 {
    let trace = run(&body, state.clone(), 10000);
    SAScore::score_trace(&crel, &trace).total()
  };

  trace_states.iter().map(score_state).sum::<f32>() / (trace_states.len() as f32)
}
