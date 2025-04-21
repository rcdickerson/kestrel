//! Converts a [KestrelCond] to a [CRel] boolean expression.

use crate::crel::ast as crel;
use crate::spec::condition::*;
use uuid::Uuid;

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

impl KCondToCRel for KestrelCond {
  fn to_crel(&self, kind: StatementKind) -> crel::Statement {
    match self {
      KestrelCond::BExpr(bexpr) => match kind {
        StatementKind::Assert => crel::Statement::Assert(Box::new(bexpr.to_crel())),
        StatementKind::Assume => crel::Statement::Assume(Box::new(bexpr.to_crel())),
      },
      KestrelCond::ForLoop{index_var, start, end, body} => {
        let init_index = crel::Declaration {
          specifiers: vec!(crel::DeclarationSpecifier::TypeSpecifier(crel::Type::Int)),
          declarator: crel::Declarator::Identifier{name: index_var.clone()},
          initializer: Some(crel::Initializer::Expression(start.to_crel())),
        };
        let wloop = crel::Statement::While {
          id: Uuid::new_v4(),
          runoff_link_id: None,
          invariants: Vec::new(),
          is_runoff: false,
          is_merged: false,
          condition: Box::new(crel::Expression::Binop {
            lhs: Box::new(crel::Expression::Identifier{name: index_var.clone()}),
            rhs: Box::new(end.to_crel()),
            op: crel::BinaryOp::Lt,
          }),
          body: Some(Box::new(crel::Statement::Compound(vec!(
            crel::BlockItem::Statement(body.to_crel(kind)),
            crel::BlockItem::Statement(crel::Statement::Expression(Box::new(
              crel::Expression::Binop {
                lhs: Box::new(crel::Expression::Identifier{name: index_var.clone()}),
                rhs: Box::new(crel::Expression::Binop {
                  lhs: Box::new(crel::Expression::Identifier{name: index_var.clone()}),
                  rhs: Box::new(crel::Expression::ConstInt(1)),
                  op: crel::BinaryOp::Add,
                }),
                op: crel::BinaryOp::Assign,
              }
            )))
          )))),
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
      },
    }
  }
}

impl CondToCRel for CondAExpr {
  fn to_crel(&self) -> crel::Expression {
    match self {
      CondAExpr::Var(id) => {
        crel::Expression::Identifier{ name: id.clone() }
      },
      CondAExpr::ReturnValue => {
        panic!("Cannot convert a condition return value into CRel.")
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
      CondAExpr::FunCall{name, args} => {
        crel::Expression::Call {
          callee: Box::new(crel::Expression::Identifier{name: name.clone()}),
          args: args.iter().map(|arg| arg.to_crel()).collect(),
        }
      },
    }
  }
}

impl CondToCRel for CondBExpr {
  fn to_crel(&self) -> crel::Expression {
    match self {
      CondBExpr::True => crel::Expression::ConstBool(true),
      CondBExpr::False => crel::Expression::ConstBool(false),
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
          lhs: match op {
            CondBBinopB::Implies => Box::new(crel::Expression::Unop {
              expr: Box::new(lhs.to_crel()),
              op: crel::UnaryOp::Not
            }),
            _ => Box::new(lhs.to_crel()),
          },
          rhs: Box::new(rhs.to_crel()),
          op: match op {
            CondBBinopB::And     => crel::BinaryOp::And,
            CondBBinopB::Or      => crel::BinaryOp::Or,
            CondBBinopB::Implies => crel::BinaryOp::Or,
          }
        }
      },
      CondBExpr::Forall{bindings, condition} => {
        crel::Expression::Forall {
          bindings: bindings.iter().map(|(var, ty)| match ty {
            KestrelType::Float => (var.clone(), crel::Type::Float),
            KestrelType::Int => (var.clone(), crel::Type::Int),
          }).collect(),
          condition: Box::new(condition.to_crel()),
        }
      },
      CondBExpr::Predicate{name, args} => {
        crel::Expression::Call {
          callee: Box::new(crel::Expression::Identifier{name: name.clone()}),
          args: args.iter().map(|arg| arg.to_crel()).collect(),
        }
      },
    }
  }
}
