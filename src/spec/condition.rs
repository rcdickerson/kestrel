use std::collections::HashSet;
use crate::names::union_all;

#[derive(Clone, Debug, PartialEq)]
pub enum KestrelCond {
  ForLoop {
    index_var: String,
    start: CondAExpr,
    end: CondAExpr,
    body: Box<KestrelCond>,
  },
  BExpr(CondBExpr),
  And {
    lhs: Box<KestrelCond>,
    rhs: Box<KestrelCond>,
  },
}
impl KestrelCond {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      KestrelCond::ForLoop{body, ..} => body.state_vars(),
      KestrelCond::BExpr(bexpr) => bexpr.state_vars(),
      KestrelCond::And{lhs, rhs} => crate::names::union_all(
        vec!(lhs.state_vars(), rhs.state_vars())),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum KestrelType {
  Float,
  Int,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CondAExpr {
  Var(String),
  ReturnValue,
  QualifiedVar{exec: String, name: String},
  Int(i32),
  Float(f32),
  Unop{aexp: Box<CondAExpr>, op: CondAUnop},
  Binop{lhs: Box<CondAExpr>, rhs: Box<CondAExpr>, op: CondABinop},
  FunCall{name: String, args: Vec<CondAExpr>},
}
impl CondAExpr {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      CondAExpr::Var(name) => {
        crate::names::singleton(name.clone())
      },
      CondAExpr::ReturnValue => HashSet::new(),
      CondAExpr::QualifiedVar{exec, name} => {
        let state_var = qualified_state_var(exec, name);
        crate::names::singleton(state_var)
      },
      CondAExpr::Int(_) => HashSet::new(),
      CondAExpr::Float(_) => HashSet::new(),
      CondAExpr::Unop{aexp, op:_} => aexp.state_vars(),
      CondAExpr::Binop{lhs, rhs, op:_} => {
        lhs.state_vars().union(&rhs.state_vars()).cloned()
          .collect()
      },
      CondAExpr::FunCall {name, args} => {
        let mut vars = union_all(args.iter()
          .map(|arg| arg.state_vars())
          .collect::<Vec<HashSet<String>>>());
        vars.insert(name.clone());
        vars
      },
    }
  }

  pub fn contains_binop_a(&self, binop: &CondABinop) -> bool {
    match self {
      CondAExpr::Var(..) => false,
      CondAExpr::ReturnValue => false,
      CondAExpr::QualifiedVar{..} => false,
      CondAExpr::Int(_) => false,
      CondAExpr::Float(_) => false,
      CondAExpr::Unop{aexp, ..} => aexp.contains_binop_a(binop),
      CondAExpr::Binop{lhs, rhs, op} => {
        op == binop || lhs.contains_binop_a(binop) || rhs.contains_binop_a(binop)
      },
      CondAExpr::FunCall{args, ..} => args.iter().any(|arg| arg.contains_binop_a(binop))
    }
  }
}

pub fn qualified_state_var(exec: &String, name: &String) -> String {
  match exec.as_ref() {
    "left" => format!("l_{}", name),
    "right" => format!("r_{}", name),
    "forall" => format!("l_{}", name),
    "exists" => format!("r_{}", name),
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
  Forall{bindings: Vec<(String, KestrelType)>, condition: Box<CondBExpr>},
  Predicate{name: String, args: Vec<CondAExpr>},
}

impl CondBExpr {
  pub fn state_vars(&self) -> HashSet<String> {
    match self {
      CondBExpr::True => HashSet::new(),
      CondBExpr::False => HashSet::new(),
      CondBExpr::Unop{bexp, op:_} => bexp.state_vars(),
      CondBExpr::BinopA{lhs, rhs, op:_} => {
        lhs.state_vars().union(&rhs.state_vars()).cloned()
          .collect()
      },
      CondBExpr::BinopB{lhs, rhs, op:_} => {
        lhs.state_vars().union(&rhs.state_vars()).cloned()
          .collect()
      },
      CondBExpr::Forall{bindings, condition, ..} => {
        let mut vars = condition.state_vars();
        for (pred_var, _) in bindings {
          vars.remove(pred_var);
        }
        vars
      },
      CondBExpr::Predicate{name, args} => {
        let mut vars = union_all(args.iter()
          .map(|arg| arg.state_vars())
          .collect::<Vec<HashSet<String>>>());
        vars.insert(name.clone());
        vars
      }
    }
  }

  pub fn contains_binop_a(&self, binop: &CondABinop) -> bool {
    match self {
      CondBExpr::True => false,
      CondBExpr::False => false,
      CondBExpr::Unop{bexp, ..} => bexp.contains_binop_a(binop),
      CondBExpr::BinopA{lhs, rhs, ..} => lhs.contains_binop_a(binop) || rhs.contains_binop_a(binop),
      CondBExpr::BinopB{lhs, rhs, ..} => lhs.contains_binop_a(binop) || rhs.contains_binop_a(binop),
      CondBExpr::Forall{condition, ..} => condition.contains_binop_a(binop),
      CondBExpr::Predicate{args, ..} => args.iter().any(|arg| arg.contains_binop_a(binop)),
    }
  }
}

pub fn cond_and(conds: &mut Vec<CondBExpr>) -> CondBExpr {
  match conds.len() {
    0 => CondBExpr::True,
    1 => conds.pop().unwrap(),
    _ => {
      let lhs = conds.pop().unwrap();
      CondBExpr::BinopB {
        lhs: Box::new(lhs),
        rhs: Box::new(cond_and(conds)),
        op: CondBBinopB::And,
      }
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
  Implies,
}
