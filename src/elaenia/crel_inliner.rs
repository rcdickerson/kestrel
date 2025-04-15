use crate::crel::ast::*;
use std::collections::HashMap;

pub struct CRelInliner {
  replacements: HashMap<String, Expression>,
}

impl CRelInliner {

  pub fn new() -> Self {
    CRelInliner {
      replacements: HashMap::new(),
    }
  }

  pub fn inline_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
      Statement::Assert(expr) => {
        Statement::Assert(Box::new(self.inline_expression(expr)))
      },
      Statement::Assume(expr) => {
        Statement::Assume(Box::new(self.inline_expression(expr)))
      },
      Statement::BasicBlock(items) => {
        Statement::BasicBlock(items.into_iter()
                              .map(|item| self.inline_block_item(item))
                              .collect())
      },
      Statement::Break => Statement::Break,
      Statement::Compound(items) => {
        Statement::Compound(items.into_iter()
                            .map(|item| self.inline_block_item(item))
                            .collect())

      },
      Statement::Expression(expr) => {
        Statement::Expression(Box::new(self.inline_expression(expr)))
      },
      Statement::GuardedRepeat { id, repetitions, condition, body } => Statement::GuardedRepeat {
        id: id.clone(),
        repetitions: repetitions.clone(),
        condition: Box::new(self.inline_expression(condition)),
        body: Box::new(self.inline_statement(body)),
      },
      Statement::If{ condition, then, els } => Statement::If {
        condition: Box::new(self.inline_expression(condition)),
        then: Box::new(self.inline_statement(then)),
        els: els.as_ref().map(|els| Box::new(self.inline_statement(&els))),
      },
      Statement::None => Statement::None,
      Statement::Relation{ lhs, rhs } => Statement::Relation {
        lhs: Box::new(self.inline_statement(lhs)),
        rhs: Box::new(self.inline_statement(rhs)),
      },
      Statement::Return(expr) => match expr {
        None => Statement::None,
        Some(expr) => Statement::Expression(Box::new(self.inline_expression(&expr)))
      },
      Statement::While{ id, runoff_link_id, invariants, condition, body, is_runoff, is_merged } => {
        Statement::While {
          id: id.clone(),
          runoff_link_id: runoff_link_id.clone(),
          invariants: invariants.into_iter().map(|inv| self.inline_expression(inv)).collect(),
          condition: Box::new(self.inline_expression(condition)),
          body: body.as_ref().map(|body| Box::new(self.inline_statement(&body))),
          is_runoff: is_runoff.clone(),
          is_merged: is_merged.clone(),
        }
      },
    }
  }

  pub fn inline_expression(&mut self, expr: &Expression) -> Expression {
    match expr {
      Expression::ASpecCall {..} => expr.clone(),
      Expression::ESpecCall {..} => expr.clone(),
      Expression::Identifier { name } => {
        match self.replacements.get(name) {
          None => expr.clone(),
          Some(rep) => rep.clone(),
        }
      },
      Expression::ConstInt(_) => expr.clone(),
      Expression::ConstBool(_) => expr.clone(),
      Expression::ConstFloat(_) => expr.clone(),
      Expression::StringLiteral(_) => expr.clone(),
      Expression::Call{ callee, args } => Expression::Call {
        callee: Box::new(self.inline_expression(callee)),
        args: args.into_iter().map(|arg| self.inline_expression(arg)).collect(),
      },
      Expression::Unop{ expr, op } => Expression::Unop {
        expr: Box::new(self.inline_expression(expr)),
        op: op.clone(),
      },
      Expression::Binop{ lhs, rhs, op } if *op == BinaryOp::Assign => {
        match &**lhs {
          Expression::Identifier{ name } => {
            self.replacements.insert(name.clone(), *rhs.clone());
            Expression::Statement(Box::new(Statement::None))
          }
          _ => Expression::Binop {
            lhs: Box::new(self.inline_expression(lhs)),
            rhs: Box::new(self.inline_expression(rhs)),
            op: op.clone(),
          }
        }
      },
      Expression::Binop{ lhs, rhs, op } => Expression::Binop {
        lhs: Box::new(self.inline_expression(lhs)),
        rhs: Box::new(self.inline_expression(rhs)),
        op: op.clone(),
      },
      Expression::Forall{ bindings, condition } => Expression::Forall {
        bindings: bindings.clone(),
        condition: Box::new(self.inline_expression(condition)),
      },
      Expression::SketchHole => Expression::SketchHole,
      Expression::Statement(stmt) => {
        Expression::Statement(Box::new(self.inline_statement(stmt)))
      }
    }
  }

  pub fn inline_block_item(&mut self, item: &BlockItem) -> BlockItem {
    match item {
      BlockItem::Declaration(decl) => self.add_declaration(decl),
      BlockItem::Statement(stmt) => BlockItem::Statement(self.inline_statement(stmt)),
    }
  }

  fn add_declaration(&mut self, decl: &Declaration) -> BlockItem {
    match &decl.initializer {
      None => BlockItem::Statement(Statement::None),
      Some(expr) => match &decl.declarator {
        Declarator::Identifier{ name } => {
          self.replacements.insert(name.clone(), expr.clone());
          BlockItem::Statement(Statement::None)
        },
        _ => BlockItem::Declaration(decl.clone()),
      }
    }
  }
}
