use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub enum CondAExpr {
  Variable(CondId),
  Int(i32),
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
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondBExpr {
  True,
  False,
  Eq{lhs: CondAExpr, rhs: CondAExpr},
  Neq{lhs: CondAExpr, rhs: CondAExpr},
  Lt{lhs: CondAExpr, rhs: CondAExpr},
  Lte{lhs: CondAExpr, rhs: CondAExpr},
  Gt{lhs: CondAExpr, rhs: CondAExpr},
  Gte{lhs: CondAExpr, rhs: CondAExpr},
  And{lhs: Box<CondBExpr>, rhs: Box<CondBExpr>},
  Or{lhs: Box<CondBExpr>, rhs: Box<CondBExpr>},
  Not(Box<CondBExpr>),
}

impl CondBExpr {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      CondBExpr::True => HashSet::new(),
      CondBExpr::False => HashSet::new(),
      CondBExpr::Eq{lhs, rhs} => binop_vars_a(lhs, rhs),
      CondBExpr::Neq{lhs, rhs} => binop_vars_a(lhs, rhs),
      CondBExpr::Lt{lhs, rhs} => binop_vars_a(lhs, rhs),
      CondBExpr::Lte{lhs, rhs} => binop_vars_a(lhs, rhs),
      CondBExpr::Gt{lhs, rhs} => binop_vars_a(lhs, rhs),
      CondBExpr::Gte{lhs, rhs} => binop_vars_a(lhs, rhs),
      CondBExpr::And{lhs, rhs} => binop_vars_b(lhs, rhs),
      CondBExpr::Or{lhs, rhs} => binop_vars_b(lhs, rhs),
      CondBExpr::Not(expr) => expr.state_vars(),
    }
  }
}

fn binop_vars_a(expr1: &CondAExpr, expr2: &CondAExpr) -> HashSet<String> {
  expr1.state_vars().union(&expr2.state_vars())
    .map(|v| v.clone())
    .collect::<HashSet<String>>()
}

fn binop_vars_b(expr1: &CondBExpr, expr2: &CondBExpr) -> HashSet<String> {
  expr1.state_vars().union(&expr2.state_vars())
    .map(|v| v.clone())
    .collect::<HashSet<String>>()
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
