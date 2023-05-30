use crate::crel::ast as crel;
use crate::spec::condition::*;

pub trait KCondToCRel {
  fn to_crel(&self, kind: StatementKind) -> crel::Statement;
}

pub trait CondToCRel {
  fn to_crel(&self) -> crel::Expression;
}

#[derive(Clone, Debug, PartialEq)]
pub enum StatementKind {
  Assume,
  Assert,
}

impl CondToCRel for StatementKind {
  fn to_crel(&self) -> crel::Expression {
    match self {
      StatementKind::Assume => crel::Expression::Identifier{name: "assume".to_string()},
      StatementKind::Assert => crel::Expression::Identifier{name: "sassert".to_string()},
    }
  }
}

impl KCondToCRel for KestrelCond {
  fn to_crel(&self, kind: StatementKind) -> crel::Statement {
    match self {
      KestrelCond::BExpr(bexpr) => {
        crel::Statement::Expression(Box::new(crel::Expression::Call {
          callee: Box::new(kind.to_crel()),
          args: vec!(bexpr.to_crel())
        }))
      },
      KestrelCond::ForLoop{index_var, start, end, body} => {
        let init_index = crel::Declaration {
          specifiers: vec!(crel::DeclarationSpecifier::TypeSpecifier(crel::Type::Int)),
          declarator: crel::Declarator::Identifier{name: index_var.clone()},
          initializer: Some(start.to_crel()),
        };
        let wloop = crel::Statement::While {
          condition: Box::new(crel::Expression::Binop {
            lhs: Box::new(crel::Expression::Identifier{name: index_var.clone()}),
            rhs: Box::new(end.to_crel()),
            op: crel::BinaryOp::Lt,
          }),
          body: Some(Box::new(body.to_crel(kind))),
        };
        crel::Statement::Compound(vec!(
          crel::BlockItem::Declaration(init_index),
          crel::BlockItem::Statement(wloop),
        ))
      },
      KestrelCond::And{lhs, rhs} => {
        crel::Statement::Compound(vec!(
          crel::BlockItem::Statement(lhs.to_crel(kind.clone())),
          crel::BlockItem::Statement(rhs.to_crel(kind.clone())),
        ))
      }
    }
  }
}

impl CondToCRel for CondAExpr {
  fn to_crel(&self) -> crel::Expression {
    match self {
      CondAExpr::Var(id) => {
        crel::Expression::Identifier{name: id.clone()}
      },
      CondAExpr::QualifiedVar{exec, name} => {
        crel::Expression::Identifier{name: qualified_state_var(exec, name)}
      },
      CondAExpr::Int(i) => {
        crel::Expression::ConstInt(*i)
      },
      CondAExpr::Float(f) => {
        crel::Expression::ConstFloat(*f)
      },
      CondAExpr::Unop{aexp, op} => {
        match op {
          CondAUnop::Neg => crel::Expression::Unop {
            expr: Box::new(aexp.to_crel()),
            op: crel::UnaryOp::Minus,
          },
        }
      },
      CondAExpr::Binop{lhs, rhs, op} => {
        crel::Expression::Binop {
          lhs: Box::new(lhs.to_crel()),
          rhs: Box::new(rhs.to_crel()),
          op: match op {
            CondABinop::Add   => crel::BinaryOp::Add,
            CondABinop::Sub   => crel::BinaryOp::Sub,
            CondABinop::Mul   => crel::BinaryOp::Mul,
            CondABinop::Div   => crel::BinaryOp::Div,
            CondABinop::Mod   => crel::BinaryOp::Mod,
            CondABinop::Index => crel::BinaryOp::Index,
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
