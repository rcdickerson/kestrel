use crate::spec::condition::*;
use rand::Rng;
use std::collections::HashMap;

pub type State = HashMap<String, i32>;

#[cfg(test)]
pub fn state(mapping: Vec<(&str, i32)>) -> State {
  let mut st = HashMap::new();
  for (name, val) in mapping { st.insert(name.to_string(), val); }
  st
}

pub fn satisfies(state: &State, cond: &CondBExpr) -> bool {
  match cond {
    CondBExpr::True => true,
    CondBExpr::False => false,
    CondBExpr::Eq{lhs, rhs}  => lookup(state, lhs) == lookup(state, rhs),
    CondBExpr::Neq{lhs, rhs} => lookup(state, lhs) != lookup(state, rhs),
    CondBExpr::Lt{lhs, rhs}  => lookup(state, lhs) <  lookup(state, rhs),
    CondBExpr::Lte{lhs, rhs} => lookup(state, lhs) <= lookup(state, rhs),
    CondBExpr::Gt{lhs, rhs}  => lookup(state, lhs) >  lookup(state, rhs),
    CondBExpr::Gte{lhs, rhs} => lookup(state, lhs) >= lookup(state, rhs),
    CondBExpr::And{lhs, rhs} => satisfies(state, lhs) && satisfies(state, rhs),
    CondBExpr::Or{lhs, rhs}  => satisfies(state, lhs) || satisfies(state, rhs),
    CondBExpr::Not(expr)     => !satisfies(state, expr),
  }
}

fn lookup(state: &State, aexp: &CondAExpr) -> i32 {
  match aexp {
    CondAExpr::Variable(id) => match state.get(&id.state_string()) {
      None => panic!("Variable not defined: {}", id.to_string()),
      Some(val) => *val,
    },
    CondAExpr::Int(i) => *i,
  }
}

pub fn rand_states_satisfying(num: usize, cond: &CondBExpr) -> Vec<State> {
  let mut states = Vec::new();
  let vars = cond.state_vars();
  while states.len() < num {
    let state = rand_state(vars.iter());
    if satisfies(&state, &cond) {
      states.push(state);
    }
  }
  states
}

fn rand_state<'a, I>(vars: I) -> State
  where I: Iterator<Item = &'a String>
{
  let mut state = HashMap::new();
  let mut rng = rand::thread_rng();
  for var in vars {
    state.insert(var.clone(), rng.gen_range(0..10));
  }
  state
}
