use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub enum KestrelCond {
  ForLoop{index_var: String, bexp: CondBExpr},
  BExpr(CondBExpr),
}
impl KestrelCond {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      KestrelCond::ForLoop{index_var:_, bexp} => bexp.state_vars(),
      KestrelCond::BExpr(bexpr) => bexpr.state_vars(),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondAExpr {
  Variable(CondId),
  Int(i32),
  Float(f32),
  Unop{aexp: Box<CondAExpr>, op: CondAUnop},
  Binop{lhs: Box<CondAExpr>, rhs: Box<CondAExpr>, op: CondABinop},
}
impl CondAExpr {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      CondAExpr::Variable(id) => {
        let mut set = HashSet::new();
        set.insert(id.state_string());
        set
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

#[derive(Clone, Debug, PartialEq)]
pub struct CondId {
  pub exec: String,
  pub name: String,
}

impl CondId {
  pub fn state_string(&self) -> String {
    match self.exec.as_ref() {
      "left" => format!("l_{}", self.name),
      "right" => format!("r_{}", self.name),
      _ => panic!("Unknown execution: {}", self.exec),
    }
  }
}

impl ToString for CondId {
  fn to_string(&self) -> String {
    format!("{}.{}", self.exec, self.name)
  }
}
