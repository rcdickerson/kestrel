#[derive(Clone, Debug, PartialEq)]
pub enum CondExpr {
  Variable(CondId),
  True,
  False,
  Eq{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Neq{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  And{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Or{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Not(Box<CondExpr>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct CondId {
  pub exec: String,
  pub name: String,
}
