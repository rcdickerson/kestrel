use crate::crel::ast::*;
use crate::spec::condition::*;
use crate::crel::eval::run;
use rand::Rng;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum HeapLocation {
  Pointer(usize),
  Offset {
    location: Box<HeapLocation>,
    offset: usize,
  },
}

impl HeapLocation {
  fn to_index(&self) -> usize {
    match self {
      HeapLocation::Pointer(p) => *p,
      HeapLocation::Offset{location, offset} => {
        location.to_index() + offset
      }
    }
  }
}

#[derive(Clone, Debug)]
pub enum HeapValue {
  Int(i32),
  Float(f32),
}

impl PartialEq for HeapValue {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (HeapValue::Int(i1), HeapValue::Int(i2)) => i1 == i2,
      (HeapValue::Float(f1), HeapValue::Float(f2)) => f1 == f2,
      _ => panic!("Attempted to compare incompatible types: {:?} and {:?}", self, other),
    }
  }
}

impl PartialOrd for HeapValue {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    match (self, other) {
      (HeapValue::Int(i1), HeapValue::Int(i2)) => i1.partial_cmp(i2),
      (HeapValue::Float(f1), HeapValue::Float(f2)) => f1.partial_cmp(f2),
      _ => panic!("Attempted to compare incompatible types: {:?} and {:?}", self, other),
    }
  }
}

impl HeapValue {
  pub fn int(&self) -> i32 {
    match self {
      HeapValue::Int(i) => *i,
      _ => panic!("Expected integer, found {:?}", self),
    }
  }
  pub fn is_int(&self) -> bool {
    match self {
      HeapValue::Int(_) => true,
      _ => false
    }
  }

  pub fn float(&self) -> f32 {
    match self {
      HeapValue::Float(f) => *f,
      _ => panic!("Expected float, found {:?}", self),
    }
  }
  pub fn is_float(&self) -> bool {
    match self {
      HeapValue::Float(_) => true,
      _ => false
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct State {
  vars: HashMap<String, (HeapLocation, usize)>,
  heap: Vec<HeapValue>,
}

impl State {

  pub fn new() -> Self {
    State {
      vars: HashMap::new(),
      heap: Vec::new()
    }
  }

  pub fn alloc(&mut self, var: &String, size: usize, init_value: HeapValue) -> HeapLocation {
    if size == 0 { panic!("Cannot allocate zero size"); }
    let location = HeapLocation::Pointer(self.heap.len());
    for _i in 0..size {
      self.heap.push(init_value.clone());
    }
    self.vars.insert(var.clone(), (location.clone(), size));
    location
  }

  pub fn store_loc(&mut self, location: &HeapLocation, value: HeapValue) {
    self.heap[location.to_index()] = value;
  }

  pub fn store_var(&mut self, var: &String, value: HeapValue) {
    let (loc, _) = self.vars.get(var).unwrap().clone();
    self.store_loc(&loc, value)
  }

  pub fn read_loc(&self, location: &HeapLocation) -> HeapValue {
    self.heap[location.to_index()].clone()
  }

  pub fn read_var(&self, var: &String) -> Vec<HeapValue> {
    let (loc, size) = self.vars.get(var).unwrap();
    let mut vals = Vec::new();
    for i in 0..*size {
      let loc = HeapLocation::Offset {
        location: Box::new(loc.clone()),
        offset: i
      };
      vals.push(self.read_loc(&loc));
    }
    vals
  }

  pub fn vars(&self) -> Vec<(String, HeapLocation, usize)> {
    self.vars.iter()
      .map(|(var, (loc, size))| (var.clone(), loc.clone(), *size))
      .collect()
  }

  pub fn lookup_loc(&self, var: &String) -> Option<&HeapLocation> {
    self.vars.get(var).map(|(loc, _)| loc)
  }

  pub fn satisfies(&self, cond: &KestrelCond) -> bool {
    match cond {
      KestrelCond::ForLoop{index_var:_, bexp:_} => panic!("Unsupported"),
      KestrelCond::BExpr(cond) => match cond {
        CondBExpr::True => true,
        CondBExpr::False => false,
        CondBExpr::Unop{bexp, op} => match op {
          CondBUnop::Not => !self.satisfies(&KestrelCond::BExpr(bexp.as_ref().clone()))
        },
        CondBExpr::BinopA{lhs, rhs, op} => match op {
          CondBBinopA::Eq  => self.clookup(lhs) == self.clookup(rhs),
          CondBBinopA::Neq => self.clookup(lhs) != self.clookup(rhs),
          CondBBinopA::Lt  => self.clookup(lhs) <  self.clookup(rhs),
          CondBBinopA::Lte => self.clookup(lhs) <= self.clookup(rhs),
          CondBBinopA::Gt  => self.clookup(lhs) >  self.clookup(rhs),
          CondBBinopA::Gte => self.clookup(lhs) >= self.clookup(rhs),
        },
        CondBExpr::BinopB{lhs, rhs, op} => {
          let lhs = &KestrelCond::BExpr(lhs.as_ref().clone());
          let rhs = &KestrelCond::BExpr(rhs.as_ref().clone());
          match op {
            CondBBinopB::And => self.satisfies(lhs) && self.satisfies(rhs),
            CondBBinopB::Or  => self.satisfies(lhs) || self.satisfies(rhs),
          }
        }

      },
    }
  }

  fn clookup(&self, aexp: &CondAExpr) -> HeapValue {
    match aexp {
      CondAExpr::Variable(id) => self.read_var(&id.state_string())[0].clone(),
      CondAExpr::Int(i) => HeapValue::Int(*i),
      CondAExpr::Float(f) => HeapValue::Float(*f),
      CondAExpr::Unop{aexp, op} => match op {
        CondAUnop::Neg => match self.clookup(aexp) {
          HeapValue::Int(i) => HeapValue::Int(-i),
          HeapValue::Float(f) => HeapValue::Float(-f),
        }
      },
      _ => panic!("AExp does not correspond to a state value: {:?}", aexp),
    }
  }

  pub fn with_declarations(&self, decls: &Vec<Declaration>, trace_fuel: usize) -> Self {
    let mut state = self.clone();
    for decl in decls {
      match &decl.declarator {
        Declarator::Array{name, size: Some(size_expr)} => {
          let stmt = Statement::Expression(Box::new(size_expr.clone()));
          let size = run(&stmt, state.clone(), trace_fuel).value_int();
          state.alloc(&name, size as usize, HeapValue::Int(0));
        },
        _ => ()
      }
      if decl.initializer.is_none() { continue; }
      let lhs = match &decl.declarator {
        Declarator::Identifier{name} => Some(Expression::Identifier{name: name.clone()}),
        Declarator::Array{name, size:_} => Some(Expression::Identifier{name: name.clone()}),
        Declarator::Function{name:_, params:_} => None,
        Declarator::Pointer(_) => panic!("Unsupported: pointer initialization"),
      };
      if lhs.is_none() { continue; }
      let initialization = Statement::Expression(Box::new(Expression::Binop {
        lhs: Box::new(lhs.unwrap()),
        rhs: Box::new(decl.initializer.clone().unwrap()),
        op: BinaryOp::Assign,
      }));
      state = run(&initialization, self.clone(), trace_fuel).current_state;
    }
    state
  }
}

pub fn rand_states_satisfying(num: usize, cond: &KestrelCond) -> Vec<State> {
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
    state.alloc(&var, 1, HeapValue::Int(rng.gen_range(0..10)));
  }
  state
}
