use crate::crel::eval::*;
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
  IntArray(Vec<i32>),
  FloatArray(Vec<f32>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TraceItem {
  Tag(Tag),
  State(TraceState),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Trace {
  pub items: Vec<TraceItem>,
}

impl Trace {

  pub fn new() -> Self {
    Trace { items: Vec::new() }
  }

  pub fn push_tag(&mut self, tag: Tag) {
    self.items.push(TraceItem::Tag(tag));
  }

  pub fn push_state(&mut self, state: State) {
    let mut trace_state = HashMap::new();
    for (name, _, _) in state.vars() {
      let val = state.read_var(&name);
      match val.len() {
        1 => match val[0] {
          HeapValue::Int(i) => {
            trace_state.insert(name, TraceStateValue::Int(i));
          },
          HeapValue::Float(f) => {
            trace_state.insert(name, TraceStateValue::Float(f));
          },
        },
        _ => match val[0] {
          HeapValue::Int(_) => {
            let ivec = val.iter().map(|v| v.int()).collect();
            trace_state.insert(name, TraceStateValue::IntArray(ivec));
          },
          HeapValue::Float(_) => {
            let fvec = val.iter().map(|v| v.float()).collect();
            trace_state.insert(name, TraceStateValue::FloatArray(fvec));
          },
        },
      }
    }
    self.items.push(TraceItem::State(trace_state));
  }

  pub fn len(&self) -> usize {
    self.items.len()
  }

  pub fn loop_heads(&self) -> Vec<Vec<TraceState>> {
    let mut all_heads = Vec::new();
    let mut current_heads = Vec::new();
    let mut current_state = None;
    for item in &self.items {
      match item {
        TraceItem::State(state) => {
         current_state = Some(state)
        },
        TraceItem::Tag(Tag::LoopHead) => {
          let head_state = current_state.expect("Loop head before first state").clone();
          current_heads.push(head_state);
        },
        TraceItem::Tag(Tag::LoopEnd) => {
          all_heads.push(current_heads);
          current_heads = Vec::new();
        },
        _ => ()
      }
    }
    all_heads
  }

  pub fn relation_states(&self) -> Vec<Vec<TraceState>> {
    let mut all_rels = Vec::new();
    let mut current_rel = Vec::new();
    let mut current_state = None;
    for item in &self.items {
      match item {
        TraceItem::State(state) => {
          current_state = Some(state);
          if current_rel.len() > 0 {
            current_rel.push(state.clone());
          }
        },
        TraceItem::Tag(Tag::RelationStart) => {
          let state = current_state.expect("Relation start before first state");
          current_rel.push(state.clone());
        },
        TraceItem::Tag(Tag::RelationEnd) => {
          all_rels.push(current_rel);
          current_rel = Vec::new();
        },
        _ => ()
      }
    }
    all_rels
  }

  pub fn count_executed_loops(&self) -> usize {
    let mut run_loop_count = 0;
    let mut loop_start_without_state = false;
    for item in &self.items {
      match item {
        TraceItem::State(_) => if loop_start_without_state {
          run_loop_count += 1;
          loop_start_without_state = false;
        },
        TraceItem::Tag(Tag::LoopStart) => {
          loop_start_without_state = true;
        },
        TraceItem::Tag(Tag::LoopEnd) => {
          loop_start_without_state = false;
        },
        _ => (),
      }
    }
    run_loop_count
  }
}
