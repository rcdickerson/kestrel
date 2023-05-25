use crate::crel::ast as crel;
use crate::spec::condition::*;

pub trait CondToCRel {
  fn to_crel(&self) -> crel::Expression;
}

impl CondToCRel for CondAExpr {
  fn to_crel(&self) -> crel::Expression {
    match self {
      CondAExpr::Variable(id) => {
        crel::Expression::Identifier{name:id.state_string()}
      },
      CondAExpr::Int(i) => {
        crel::Expression::ConstInt(*i)
      },
    }
  }
}

impl CondToCRel for CondBExpr {
  fn to_crel(&self) -> crel::Expression {
    match self {
      CondBExpr::True => crel::Expression::ConstInt(1),
      CondBExpr::False => crel::Expression::ConstInt(0),
      CondBExpr::Eq{lhs, rhs} => binop(lhs, rhs, crel::BinaryOp::Equals),
      CondBExpr::Neq{lhs, rhs} => binop(lhs, rhs, crel::BinaryOp::NotEquals),
      CondBExpr::Lt{lhs, rhs} => binop(lhs, rhs, crel::BinaryOp::Lt),
      CondBExpr::Lte{lhs, rhs} => binop(lhs, rhs, crel::BinaryOp::Lte),
      CondBExpr::Gt{lhs, rhs} => binop(lhs, rhs, crel::BinaryOp::Gt),
      CondBExpr::Gte{lhs, rhs} => binop(lhs, rhs, crel::BinaryOp::Gte),
      CondBExpr::And{lhs, rhs} => binop(lhs.as_ref(), rhs.as_ref(), crel::BinaryOp::And),
      CondBExpr::Or{lhs, rhs} => binop(lhs.as_ref(), rhs.as_ref(), crel::BinaryOp::Or),
      CondBExpr::Not(expr) => crel::Expression::Unop {
        expr: Box::new(expr.to_crel()),
        op: crel::UnaryOp::Minus,
      }
    }
  }
}

fn binop(cond1: &dyn CondToCRel, cond2: &dyn CondToCRel, op: crel::BinaryOp) -> crel::Expression {
  crel::Expression::Binop {
    lhs: Box::new(cond1.to_crel()),
    rhs: Box::new(cond2.to_crel()),
    op: op,
  }
}
