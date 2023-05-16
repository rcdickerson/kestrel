use crate::crel::count_loops::*;
use crate::crel::eval::*;
use crate::crel::trace::{State, state};
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

pub fn sa_score(expr: RecExpr<Eggroll>) -> f32 {
  let crel = crate::eggroll::to_crel::eggroll_to_crel(&expr.to_string());
  let body = crate::crel::fundef::extract_fundefs(&crel).1
    .get(&"main".to_string())
    .expect("Missing main function")
    .body.clone();
  let trace = run(&body, state(vec!(("l_n", 5), ("r_n", 5))), 100);
  //let trace = crel::trace::run(&body, crel::trace::state(vec!(("l_x", 5), ("r_x", 5))), 100);
  let loop_heads = trace.loop_heads();
  let rel_states = trace.relation_states();

  let num_rels = rel_states.len() as i32;
  let score_rel_size = if num_rels == 0 {
    1.0
  } else {
    let sum : usize = rel_states.iter().map(|v| v.len()).sum();
    (sum as f32) / (num_rels as f32) / (trace.len() as f32)
  };

  let score_rel_update_match = if num_rels == 0 {
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
  };

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
  let score_matching = 1.0 - (matching_sum / loop_heads.len() as f32);
  let score_similarity = 1.0 - (similarity_sum / loop_heads.len() as f32);

  let num_executed_loops = trace.count_executed_loops();
  let num_loops = crel.count_loops();
  let score_loop_execs = (num_executed_loops as f32) / (num_loops as f32);

  (0.2 * score_rel_size)
    + (0.2 * score_rel_update_match)
    + (0.2 * score_similarity)
    + (0.2 * score_matching)
    + (0.2 * score_loop_execs)
}
