use crate::crel::eval::*;
use crate::crel::eval::state::VarRead;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Tag {
  LoopStart,
  LoopHead,
  LoopEnd,
  RelationStart,
  RelationMid,
  RelationEnd,
}

pub type TraceState = HashMap<String, TraceStateValue>;

#[derive(Clone, Debug, PartialEq)]
pub enum TraceStateValue {
  Int(i32),
  Float(f32),
  Array(Vec<TraceStateValue>),
}

impl TraceStateValue {

  pub fn from_var_read(read: &VarRead) -> Self {
    match read {
      VarRead::Value(val) => TraceStateValue::from_heap_value(val),
      VarRead::Array(val) => {
        TraceStateValue::Array(val.iter()
          .map(TraceStateValue::from_heap_value)
          .collect::<Vec<TraceStateValue>>())
      },
    }
  }

  pub fn from_heap_value(value: &HeapValue) -> Self {
    match value {
      HeapValue::Int(i) => TraceStateValue::Int(*i),
      HeapValue::Float(f) => TraceStateValue::Float(*f),
    }
  }

  pub fn minus(&self, other: &TraceStateValue) -> TraceStateValue {
    match (self, other) {
      (TraceStateValue::Int(i1), TraceStateValue::Int(i2)) => TraceStateValue::Int(i1 - i2),
      (TraceStateValue::Float(f1), TraceStateValue::Float(f2)) => TraceStateValue::Float(f1 - f2),
      (TraceStateValue::Array(a1), TraceStateValue::Array(a2)) => {
        let mut arr = Vec::with_capacity(a1.len());
        for (v1, v2) in a1.iter().zip(a2) {
          arr.push(v1.minus(v2));
        }
        TraceStateValue::Array(arr)
      },
      _ => panic!("Cannot subtract values of different types: {:?} and {:?}", self, other),
    }
  }

  pub fn is_zero(&self) -> bool {
    match self {
      TraceStateValue::Int(i) => *i == 0,
      TraceStateValue::Float(f) => *f == 0.0,
      TraceStateValue::Array(a) => a.iter().all(|v| v.is_zero()),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TraceItem {
  pub tag: Tag,
  pub state: TraceState,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Trace {
  pub items: Vec<TraceItem>,
}

impl Trace {

  pub fn new() -> Self {
    Trace { items: Vec::new() }
  }

  pub fn push_state(&mut self, tag: Tag, state: &State) {
    let mut trace_state = HashMap::with_capacity(state.vars().len());
    for (name, _, _) in state.vars() {
      let read = state.read_var(&name);
      trace_state.insert(name, TraceStateValue::from_var_read(&read));
    }
    self.items.push(TraceItem{tag, state: trace_state});
  }

  pub fn len(&self) -> usize {
    self.items.len()
  }

  pub fn loop_heads(&self) -> Vec<Vec<&TraceState>> {
    let mut all_heads = Vec::new();
    let mut current_heads = Vec::new();
    for item in &self.items {
      match item {
        TraceItem{tag: Tag::LoopHead, state} => {
          current_heads.push(state);
        },
        TraceItem{tag: Tag::LoopEnd, state:_} => {
          all_heads.push(current_heads);
          current_heads = Vec::new();
        },
        _ => ()
      }
    }
    all_heads
  }

  pub fn relation_states(&self) -> Vec<Vec<&TraceState>> {
    let mut all_rels = Vec::new();
    let mut current_rel = Vec::new();
    for item in &self.items {
      match item {
        TraceItem{tag: Tag::RelationStart, state} => {
          current_rel.push(state);
        },
        TraceItem{tag: Tag::RelationEnd, state:_} => {
          all_rels.push(current_rel);
          current_rel = Vec::new();
        },
        _ => ()
      }
    }
    all_rels
  }

  pub fn count_executed_loops(&self) -> usize {
    let mut count = 0;
    let mut count_next_head = false;
    let mut nest_count = 0;
    let mut iteration_count: Vec<usize> = Vec::new();
    for item in &self.items {
      match item {
        TraceItem{tag: Tag::LoopStart, state:_} => {
          count_next_head = (nest_count == 0) || (iteration_count[nest_count - 1] == 1);
          nest_count += 1;
          if iteration_count.len() < nest_count {
            iteration_count.push(0);
          } else {
            iteration_count[nest_count - 1] = 0;
          }
        },
        TraceItem{tag: Tag::LoopHead, state:_} => {
          if count_next_head { count += 1; }
          count_next_head = false;
          iteration_count[nest_count - 1] += 1;
        },
        TraceItem{tag: Tag::LoopEnd, state:_} => {
          count_next_head = false;
          nest_count -= 1;
        },
        _ => (),
      }
    }
    count
  }
}
