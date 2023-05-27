use crate::crel::ast as crel;
use crate::spec::condition::*;

pub trait CondToCRel {
  fn to_crel(&self) -> crel::Expression;
}

impl CondToCRel for KestrelCond {
  fn to_crel(&self) -> crel::Expression {
    match self {
      KestrelCond::ForLoop{index_var:_, bexp:_} => panic!("Unsupported"),
      KestrelCond::BExpr(bexpr) => bexpr.to_crel(),
    }
  }
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
      CondAExpr::Float(f) => {
        crel::Expression::ConstFloat(*f)
      },
      CondAExpr::Unop{aexp, op} => {
        crel::Expression::Unop {
          expr: Box::new(aexp.to_crel()),
          op: match op {
            CondAUnop::Neg => crel::UnaryOp::Minus,
          }
        }
      },
      CondAExpr::Binop{lhs, rhs, op} => {
        crel::Expression::Binop {
          lhs: Box::new(lhs.to_crel()),
          rhs: Box::new(rhs.to_crel()),
          op: match op {
            CondABinop::Add => crel::BinaryOp::Add,
            CondABinop::Sub => crel::BinaryOp::Sub,
            CondABinop::Mul => crel::BinaryOp::Mul,
            CondABinop::Div => crel::BinaryOp::Div,
            CondABinop::Mod => crel::BinaryOp::Mod,
          }
        }
      },
    }
  }
}

impl CondToCRel for CondBExpr {
  fn to_crel(&self) -> crel::Expression {
    match self {
      CondBExpr::True => crel::Expression::ConstInt(1),
      CondBExpr::False => crel::Expression::ConstInt(0),
      CondBExpr::Unop{bexp, op} => {
        crel::Expression::Unop {
          expr: Box::new(bexp.to_crel()),
          op: match op {
            CondBUnop::Not => crel::UnaryOp::Not,
          }
        }
      },
      CondBExpr::BinopA{lhs, rhs, op} => {
        crel::Expression::Binop {
          lhs: Box::new(lhs.to_crel()),
          rhs: Box::new(rhs.to_crel()),
          op: match op {
            CondBBinopA::Eq => crel::BinaryOp::Equals,
            CondBBinopA::Neq => crel::BinaryOp::NotEquals,
            CondBBinopA::Lt => crel::BinaryOp::Lt,
            CondBBinopA::Lte => crel::BinaryOp::Lte,
            CondBBinopA::Gt => crel::BinaryOp::Gt,
            CondBBinopA::Gte => crel::BinaryOp::Gte,
          }
        }
      },
      CondBExpr::BinopB{lhs, rhs, op} => {
        crel::Expression::Binop {
          lhs: Box::new(lhs.to_crel()),
          rhs: Box::new(rhs.to_crel()),
          op: match op {
            CondBBinopB::And => crel::BinaryOp::And,
            CondBBinopB::Or => crel::BinaryOp::Or,
          }
        }
      }
    }
  }
}
