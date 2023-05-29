use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub enum KestrelCond {
  ForLoop {
    index_var: String,
    start: CondAExpr,
    end: CondAExpr,
    body: Box<KestrelCond>,
  },
  BExpr(CondBExpr),
}
impl KestrelCond {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      KestrelCond::ForLoop{index_var:_, start:_, end:_, body} => body.state_vars(),
      KestrelCond::BExpr(bexpr) => bexpr.state_vars(),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondAExpr {
  Var(String),
  QualifiedVar{exec: String, name: String},
  Int(i32),
  Float(f32),
  Unop{aexp: Box<CondAExpr>, op: CondAUnop},
  Binop{lhs: Box<CondAExpr>, rhs: Box<CondAExpr>, op: CondABinop},
}
impl CondAExpr {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      CondAExpr::Var(name) => {
        crate::names::singleton(name.clone())
      },
      CondAExpr::QualifiedVar{exec, name} => {
        let state_var = qualified_state_var(exec, name);
        crate::names::singleton(state_var)
      },
      CondAExpr::Int(_) => HashSet::new(),
      CondAExpr::Float(_) => HashSet::new(),
      CondAExpr::Unop{aexp, op:_} => aexp.state_vars(),
      CondAExpr::Binop{lhs, rhs, op:_} => {
        lhs.state_vars().union(&rhs.state_vars())
          .map(|s| s.clone())
          .collect()
      },
    }
  }
}

pub fn qualified_state_var(exec: &String, name: &String) -> String {
  match exec.as_ref() {
    "left" => format!("l_{}", name),
    "right" => format!("r_{}", name),
    _ => panic!("Unknown execution: {}", exec),
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondAUnop {
  Neg,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondABinop {
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  Index,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondBExpr {
  True,
  False,
  Unop{bexp: Box<CondBExpr>, op: CondBUnop},
  BinopA{lhs: CondAExpr, rhs: CondAExpr, op: CondBBinopA},
  BinopB{lhs: Box<CondBExpr>, rhs: Box<CondBExpr>, op: CondBBinopB},
}

impl CondBExpr {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      CondBExpr::True => HashSet::new(),
      CondBExpr::False => HashSet::new(),
      CondBExpr::Unop{bexp, op:_} => bexp.state_vars(),
      CondBExpr::BinopA{lhs, rhs, op:_} => {
        lhs.state_vars().union(&rhs.state_vars())
          .map(|s| s.clone())
          .collect()
      },
      CondBExpr::BinopB{lhs, rhs, op:_} => {
        lhs.state_vars().union(&rhs.state_vars())
          .map(|s| s.clone())
          .collect()
      },
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondBUnop {
  Not,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondBBinopA {
  Eq,
  Neq,
  Lt,
  Lte,
  Gt,
  Gte,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondBBinopB {
  And,
  Or,
}
