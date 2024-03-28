use crate::crel::ast::*;
use crate::crel::fundef::*;
use crate::spec::condition::*;
use crate::spec::to_crel::*;
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

#[derive(Clone, Debug)]
pub enum VarRead<'a> {
  Value(HeapValue),
  Array(&'a[HeapValue]),
}
impl<'a> VarRead<'a> {
  fn int(&self) -> i32 {
    match self {
      VarRead::Value(HeapValue::Int(i)) => *i,
      _ => panic!("Expected int, found: {:?}", self),
    }
  }
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

  pub fn read_var(&self, var: &String) -> VarRead {
    let (loc, size) = self.vars.get(var).unwrap();
    match size {
      1 => VarRead::Value(self.read_loc(loc)),
      _ => {
        let heap_loc = loc.to_index();
        VarRead::Array(&self.heap[heap_loc..heap_loc + size])
      }
    }
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
      KestrelCond::ForLoop{index_var, start, end, body} => {
        let start = self.clookup(start).int();
        let end = self.clookup(end).int();
        for i in start..end {
          let mut with_idx = self.clone();
          with_idx.alloc(index_var, 1_usize, HeapValue::Int(i));
          if !with_idx.satisfies(&body.clone()) {return false;}
        }
        true
      },
      KestrelCond::BExpr(cond) => match cond {
        CondBExpr::True => true,
        CondBExpr::False => false,
        CondBExpr::Unop{bexp, op} => match op {
          CondBUnop::Not => !self.satisfies(&KestrelCond::BExpr(bexp.as_ref().clone()))
        },
        CondBExpr::BinopA{..} => {
          let crel = cond.to_crel();
          let stmt = Statement::Expression(Box::new(crel));
          let result = run(&stmt, self.clone(), 1000).value_int();
          result != 0
        },
        CondBExpr::BinopB{lhs, rhs, op} => {
          let lhs = &KestrelCond::BExpr(lhs.as_ref().clone());
          let rhs = &KestrelCond::BExpr(rhs.as_ref().clone());
          match op {
            CondBBinopB::And     =>  self.satisfies(lhs) && self.satisfies(rhs),
            CondBBinopB::Or      =>  self.satisfies(lhs) || self.satisfies(rhs),
            CondBBinopB::Implies => !self.satisfies(lhs) || self.satisfies(rhs),
          }
        },
        CondBExpr::Forall{..} => true, // Ignore
        CondBExpr::Predicate{name, args} => {
          let stmt = Statement::Expression(Box::new(Expression::Call{
            callee: Box::new(Expression::Identifier{name: name.clone()}),
            args: args.iter().map(|arg| arg.to_crel()).collect(),
          }));
          let result = run(&stmt, self.clone(), 1000).value_int();
          result != 0
        }
      },
      KestrelCond::And{lhs, rhs} => {
        self.satisfies(lhs) && self.satisfies(rhs)
      },
    }
  }

  fn clookup(&self, aexp: &CondAExpr) -> VarRead {
    match aexp {
      CondAExpr::Var(id) => self.read_var(id),
      CondAExpr::QualifiedVar{exec, name} => {
        let var = qualified_state_var(exec, name);
        self.read_var(&var)
      },
      CondAExpr::Int(i) => VarRead::Value(HeapValue::Int(*i)),
      CondAExpr::Float(f) => VarRead::Value(HeapValue::Float(*f)),
      CondAExpr::Unop{aexp, op} => match op {
        CondAUnop::Neg => match self.clookup(aexp) {
          VarRead::Value(HeapValue::Int(i)) => VarRead::Value(HeapValue::Int(-i)),
          VarRead::Value(HeapValue::Float(f)) => VarRead::Value(HeapValue::Float(-f)),
          _ => panic!("Cannot lookup value for {:?}", aexp),
        },
      },
      CondAExpr::Binop{lhs, rhs, op: CondABinop::Index} => {
        let var = match lhs.as_ref() {
          CondAExpr::Var(v) => v.clone(),
          CondAExpr::QualifiedVar{exec, name} => qualified_state_var(exec, name),
          _ => panic!("Unsupported indexee: {:?}", lhs)
        };
        let loc = self.lookup_loc(&var.clone()).unwrap();
        let index = match self.clookup(rhs) {
          VarRead::Value(HeapValue::Int(i)) => i,
          _ => panic!("Unsupported index value: {:?}", rhs),
        };
        let indexed_loc = HeapLocation::Offset {
          location: Box::new(loc.clone()),
          offset: index as usize,
        };
        VarRead::Value(self.read_loc(&indexed_loc))
      },
      _ => panic!("AExp does not correspond to a state value: {:?}", aexp),
    }
  }

  pub fn with_declarations(&self, decls: &Vec<Declaration>, fuel: usize) -> Self {
    let mut state = self.clone();
    for decl in decls { state = state.alloc_from_decl(&decl.declarator, &decl.initializer, fuel); }
    state
  }

  fn alloc_from_decl(&self, declarator: &Declarator, initializer: &Option<Expression>, fuel: usize) -> Self {
    let mut state = self.clone();
    match &declarator {
      Declarator::Identifier{name} => { state.alloc(name, 1, HeapValue::Int(0)); },
      Declarator::Array{name, sizes} if !sizes.is_empty() => {
        let mut alloc_size = 1;
        for size_expr in sizes {
          let stmt = Statement::Expression(Box::new(size_expr.clone()));
          alloc_size *= run(&stmt, state.clone(), fuel).value_int();
        }
        state.alloc(name, alloc_size as usize, HeapValue::Int(0));
      },
      _ => ()
    }
    if initializer.is_none() { return state; }
    let lhs = match &declarator {
      Declarator::Identifier{name} => Some(Expression::Identifier{name: name.clone()}),
      Declarator::Array{name, sizes:_} => Some(Expression::Identifier{name: name.clone()}),
      Declarator::Function{name:_, params:_} => None,
      Declarator::Pointer(_) => panic!("Unsupported: pointer initialization"),
    };
    if lhs.is_none() { return self.clone(); }
    let initialization = Statement::Expression(Box::new(Expression::Binop {
      lhs: Box::new(lhs.unwrap()),
      rhs: Box::new(initializer.clone().unwrap()),
      op: BinaryOp::Assign,
    }));
    run(&initialization, state.clone(), fuel).current_state
  }

  fn randomize_declaration(&self,
                           declarator: &Declarator,
                           initializer: &Option<Expression>,
                           ty: Type,
                           fuel: usize) -> State {
    match initializer {
      Some(_) => { self.alloc_from_decl(declarator, initializer, fuel) }
      None => {
        let alloc = match &declarator {
          Declarator::Identifier{name} => Some((name.clone(), 1, self.clone())),
          Declarator::Array{name, sizes} => {
            let mut alloc_size = 1;
            let mut state = self.clone();
            for size in sizes {
              let size_stmt = Statement::Expression(Box::new(size.clone()));
              let size_eval = run(&size_stmt, state.clone(), 1000);
              state = size_eval.current_state.clone();
              alloc_size *= size_eval.value_int();
            }
            Some((name.clone(), alloc_size, state))
          },
          Declarator::Function{name:_, params:_} => None,
          Declarator::Pointer(_) => panic!("Unsupported: pointer initialization"),
        };
        if alloc.is_none() { return self.clone(); }
        let (name, alloc_size, mut state) = alloc.unwrap();
        let base_loc = state.alloc(&name, alloc_size as usize, HeapValue::Int(0));
        for i in 0..alloc_size {
          let loc = HeapLocation::Offset {
            location: Box::new(base_loc.clone()),
            offset: i as usize,
          };
          state.store_loc(&loc, rand_val(ty.clone()));
        }
        state
      },
    }
  }
}

pub fn rand_states_satisfying(num: usize,
                              cond: &KestrelCond,
                              decls: Option<&Vec<Declaration>>,
                              generator: Option<&FunDef>,
                              fuel: usize) -> Vec<State> {
  let mut states = Vec::new();
  while states.len() < num {
    let mut state = rand_state(decls, fuel);
    if generator.is_some() {
      let generator = generator.unwrap();
      for decl in &generator.params {
        if decl.declarator.is_none() { continue; }
        let ty = decl.get_type().unwrap();
        state = state.randomize_declaration(decl.declarator.as_ref().unwrap(), &None, ty, fuel);
      }
      state = run(&generator.body, state.clone(), fuel).current_state.clone();
    }
    if state.satisfies(cond) {
      states.push(state);
    }
  }
  states
}

fn rand_state(decls: Option<&Vec<Declaration>>, fuel: usize) -> State {
  let mut state = State::new();
  match decls {
    None => state,
    Some(decls) => {
      for decl in decls {
        let ty = decl.get_type().unwrap();
        state = state.randomize_declaration(&decl.declarator, &decl.initializer, ty, fuel);
      }
      state
    }
  }
}

fn rand_val(ty: Type) -> HeapValue {
  let mut rng = rand::thread_rng();
  match ty {
    Type::Int => HeapValue::Int(rng.gen_range(0..10)),
    Type::Float => HeapValue::Float(rng.gen::<f32>() * 10.0),
    _ => panic!("Unsupported: randomly generated {:?}", ty),
  }
}
