use crate::spec::condition::*;
use rand::Rng;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StateKey {
  Name(String),
  ArrayIndex{id: Box<StateKey>, index: usize},
}

#[derive(Clone, Debug, PartialEq)]
pub enum StateValue {
  Int(i32),
  Array(Vec<StateValue>),
}

impl StateValue {
  pub fn int(&self) -> i32 {
    match self {
      StateValue::Int(i) => *i,
      StateValue::Array(_) => panic!("Expected integer, found array"),
    }
  }
  pub fn is_int(&self) -> bool {
    match self {
      StateValue::Int(_) => true,
      StateValue::Array(_) => false,
    }
  }

  pub fn array(&self) -> &Vec<StateValue> {
    match self {
      StateValue::Int(_n) => panic!("Expected array, found integer"),
      StateValue::Array(arr) => arr,
    }
  }
  pub fn is_array(&self) -> bool {
    match self {
      StateValue::Int(_) => false,
      StateValue::Array(_) => true,
    }
  }
}

#[cfg(test)]
pub fn state(mapping: Vec<(&str, i32)>) -> State {
  let mut st = State::new();
  for (name, val) in mapping {
    st.put(name.to_string(), val);
  }
  st
}

#[derive(Clone, Debug, PartialEq)]
pub struct State {
  pub map: HashMap<String, StateValue>,
}

impl State {

  pub fn new() -> Self {
    State { map: HashMap::new() }
  }

  pub fn put(&mut self, name: String, value: i32) {
    self.map.insert(name, StateValue::Int(value));
  }

  pub fn put_array(&mut self, name: String, size: usize) {
    self.map.insert(name, StateValue::Array(vec![StateValue::Int(0); size]));
  }

  pub fn put_indexed(&mut self, name: String, index: usize, value: i32) {
    let mut arr = self.map.get(&name).unwrap().array().clone();
    arr[index] = StateValue::Int(value);
    self.map.insert(name, StateValue::Array(arr));
  }

  pub fn get(&self, key: &String) -> Option<&StateValue> {
    self.map.get(key)
  }

  pub fn lookup(&self, key: &StateKey) -> Option<&StateValue> {
    match key {
      StateKey::Name(name) => self.map.get(name),
      StateKey::ArrayIndex{id, index} => match self.lookup(id) {
        None => None,
        Some(StateValue::Int(_)) => {
          panic!("{:?} is an int, cannot index as array", id)
        },
        Some(StateValue::Array(arr)) => {
          Some(&arr[*index])
        }
      }
    }
  }

  pub fn satisfies(&self, cond: &CondBExpr) -> bool {
    match cond {
      CondBExpr::True => true,
      CondBExpr::False => false,
      CondBExpr::Eq{lhs, rhs}  => self.clookup(lhs) == self.clookup(rhs),
      CondBExpr::Neq{lhs, rhs} => self.clookup(lhs) != self.clookup(rhs),
      CondBExpr::Lt{lhs, rhs}  => self.clookup(lhs) <  self.clookup(rhs),
      CondBExpr::Lte{lhs, rhs} => self.clookup(lhs) <= self.clookup(rhs),
      CondBExpr::Gt{lhs, rhs}  => self.clookup(lhs) >  self.clookup(rhs),
      CondBExpr::Gte{lhs, rhs} => self.clookup(lhs) >= self.clookup(rhs),
      CondBExpr::And{lhs, rhs} => self.satisfies(lhs) && self.satisfies(rhs),
      CondBExpr::Or{lhs, rhs}  => self.satisfies(lhs) || self.satisfies(rhs),
      CondBExpr::Not(expr)     => !self.satisfies(expr),
    }
  }

  fn clookup(&self, aexp: &CondAExpr) -> i32 {
    match aexp {
      CondAExpr::Variable(id) => {
        self.map.get(&id.state_string()).unwrap().int()
      },
      CondAExpr::Int(i) => *i,
    }
  }
}

pub fn rand_states_satisfying(num: usize, cond: &CondBExpr) -> Vec<State> {
  let mut states = Vec::new();
  let vars = cond.state_vars();
  while states.len() < num {
    let state = rand_state(vars.iter());
    if state.satisfies(&cond) {
      states.push(state);
    }
  }
  states
}

fn rand_state<'a, I>(vars: I) -> State
  where I: Iterator<Item = &'a String>
{
  let mut state = State::new();
  let mut rng = rand::thread_rng();
  for var in vars {
    state.put(var.clone(), rng.gen_range(0..10));
  }
  state
}
