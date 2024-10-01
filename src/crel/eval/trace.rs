use crate::crel::eval::*;
use crate::crel::eval::state::VarRead;
use std::collections::HashMap;
use std::collections::HashSet;
use uuid::Uuid;

#[derive(Clone, Debug, PartialEq)]
pub enum Tag {
  LoopStart(Uuid),
  LoopHead(Uuid),
  LoopEnd(Uuid),
  MergedStart{id: Uuid, runoff_link_id: Option<Uuid>},
  MergedHead{id: Uuid, runoff_link_id: Option<Uuid>},
  MergedEnd{id: Uuid, runoff_link_id: Option<Uuid>},
  RunoffStart{id: Uuid, runoff_link_id: Option<Uuid>},
  RunoffHead{id: Uuid, runoff_link_id: Option<Uuid>},
  RunoffEnd{id: Uuid, runoff_link_id: Option<Uuid>},
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
      (TraceStateValue::Int(i1), TraceStateValue::Int(i2)) => TraceStateValue::Int(i1.wrapping_sub(*i2)),
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
        TraceItem{tag: Tag::LoopHead(_), state}
        | TraceItem{tag: Tag::MergedHead{..}, state}
        | TraceItem{tag: Tag::RunoffHead{..}, state}
        => {
          current_heads.push(state);
        },
        TraceItem{tag: Tag::LoopEnd(_), state:_}
        | TraceItem{tag: Tag::MergedEnd{..}, state:_}
        | TraceItem{tag: Tag::RunoffEnd{..}, state:_}
        => {
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

  pub fn count_executed_loops(&self) -> (usize, usize, usize) {
    let mut loop_heads = HashSet::new();
    let mut merged_heads = HashSet::new();
    let mut runoff_heads = HashSet::new();
    for item in &self.items {
      match item {
        TraceItem{tag: Tag::LoopHead(id), state:_} => {
          loop_heads.insert(id);
        },
        TraceItem{tag: Tag::MergedHead{id,..}, state:_} => {
          merged_heads.insert(id);
        },
        TraceItem{tag: Tag::RunoffHead{id,..}, state:_} => {
          runoff_heads.insert(id);
        },
        _ => (),
      }
    }
    (loop_heads.len(), merged_heads.len(), runoff_heads.len())
  }

  pub fn count_merged_loops_without_runoff_execs(&self) -> usize {
    let mut merged_heads = HashSet::new();
    let mut runoff_heads = HashSet::new();
    for item in &self.items {
      match item {
        TraceItem{tag: Tag::MergedHead{runoff_link_id,..}, state:_} => {
          runoff_link_id.map(|id| merged_heads.insert(id));
        },
        TraceItem{tag: Tag::RunoffHead{runoff_link_id,..}, state:_} => {
          runoff_link_id.map(|id| runoff_heads.insert(id));
        },
        _ => (),
      }
    }
    merged_heads.difference(&runoff_heads).collect::<Vec<_>>().len()
  }
}
