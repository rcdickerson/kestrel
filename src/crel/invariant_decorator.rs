use crate::crel::ast::*;
use crate::spec::condition::CondBExpr;
use std::collections::HashMap;

pub fn decorate_invariants(crel: &CRel, imap: &HashMap<String, Vec<CondBExpr>>) -> CRel {
  match crel {
    CRel::Declaration(decl) => CRel::Declaration(decorate_declaration(decl, imap)),
    CRel::FunctionDefinition{specifiers, name, params, body} => CRel::FunctionDefinition {
      specifiers: specifiers.clone(),
      name: name.clone(),
      params: params.clone(),
      body: Box::new(decorate_statement(&body, imap)),
    },
    CRel::Seq(seq) => CRel::Seq(seq.iter().map(|crel| decorate_invariants(&crel.clone(), imap)).collect()),
  }
}

fn decorate_declaration(decl: &Declaration, imap: &HashMap<String, Vec<CondBExpr>>) -> Declaration {
  Declaration {
    specifiers: decl.specifiers.clone(),
    declarator: decl.declarator.clone(),
    initializer: decl.initializer.clone().map(|init| decorate_expression(&init, imap)),
  }
}

fn decorate_statement(stmt: &Statement, imap: &HashMap<String, Vec<CondBExpr>>) -> Statement {
  match stmt {
    Statement::BasicBlock(items) => {
      Statement::BasicBlock(items.iter()
        .map(|item| decorate_block_item(item, imap))
        .collect())
    },
    Statement::Break => stmt.clone(),
    Statement::Compound(items) => {
      Statement::Compound(items.iter()
        .map(|item| decorate_block_item(item, imap))
        .collect())
    },
    Statement::Expression(expr) => Statement::Expression(
      Box::new(decorate_expression(&expr, imap))),
    Statement::If{condition, then, els} => Statement::If {
      condition: condition.clone(),
      then: Box::new(decorate_statement(then, imap)),
      els: els.clone().map(|e| Box::new(decorate_statement(&e, imap))),
    },
    Statement::None => stmt.clone(),
    Statement::Relation{lhs, rhs} => Statement::Relation {
      lhs: Box::new(decorate_statement(lhs, imap)),
      rhs: Box::new(decorate_statement(rhs, imap)),
    },
    Statement::Return(expr) => Statement::Return(
      expr.clone().map(|e| Box::new(decorate_expression(&e, imap)))),
    Statement::While{loop_id, condition, body, ..} => Statement::While {
      loop_id: loop_id.clone(),
      invariants: loop_id.clone()
        .and_then(|id| imap.get(&id))
        .map(|inv| inv.clone()),
      condition: condition.clone(),
      body: body.clone().map(|b| Box::new(decorate_statement(&b, imap))),
    },
  }
}

fn decorate_expression(expr: &Expression, imap: &HashMap<String, Vec<CondBExpr>>) -> Expression {
  match expr {
    Expression::Statement(inner) => {
      Expression::Statement(Box::new(decorate_statement(&inner, imap)))
    },
    _ => expr.clone(),
  }
}

fn decorate_block_item(item: &BlockItem, imap: &HashMap<String, Vec<CondBExpr>>) -> BlockItem {
  match item {
    BlockItem::Declaration(..) => item.clone(),
    BlockItem::Statement(stmt) => BlockItem::Statement(decorate_statement(stmt, imap)),
  }
}
