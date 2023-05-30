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
  Array(Vec<HeapValue>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct TraceItem {
  tag: Tag,
  state: TraceState,
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
    let mut trace_state = HashMap::new();
    for (name, _, _) in state.vars() {
      let read = state.read_var(&name);
      match read {
        VarRead::Value(val) => match val {
          HeapValue::Int(i) => {
            trace_state.insert(name, TraceStateValue::Int(i));
          },
          HeapValue::Float(f) => {
            trace_state.insert(name, TraceStateValue::Float(f));
          },
        },
        VarRead::Array(val) => {
          trace_state.insert(name, TraceStateValue::Array(val.to_vec()));
        },
      }
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
    for item in &self.items {
      match item {
        TraceItem{tag: Tag::LoopStart, state:_} => {
          count_next_head = true;
        },
        TraceItem{tag: Tag::LoopHead, state:_} => {
          if count_next_head { count += 1; }
          count_next_head = false;
        },
        TraceItem{tag: Tag::LoopEnd, state:_} => {
          count_next_head = false;
        },
        _ => (),
      }
    }
    count
  }
}
