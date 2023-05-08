#[derive(Clone, Debug, PartialEq)]
pub enum CondExpr {
  Variable(CondId),
  True,
  False,
  Eq{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Neq{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Lt{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Lte{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Gt{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Gte{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  And{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Or{ lhs: Box<CondExpr>, rhs: Box<CondExpr> },
  Not(Box<CondExpr>),
  Fun{ name: String },
}

#[derive(Clone, Debug, PartialEq)]
pub struct CondId {
  pub exec: String,
  pub name: String,
}
