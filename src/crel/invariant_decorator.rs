use crate::crel::ast::*;
use crate::crel::visitor::*;
use crate::spec::condition::CondBExpr;
use std::collections::HashMap;

pub struct InvariantDecorator<'a> {
  imap: &'a HashMap<String, Vec<CondBExpr>>,
}

impl InvariantDecorator<'_> {
  pub fn new<'a>(imap: &'a HashMap<String, Vec<CondBExpr>>) -> InvariantDecorator<'a> {
    InvariantDecorator { imap }
  }
}

impl CRelVisitor for InvariantDecorator<'_> {
  fn visit_statement(&mut self, statement: &mut Statement) {
    match statement {
      Statement::While{loop_id, invariants, ..} => {
        loop_id.as_ref().map(|id| self.imap.get(id).map(|invs| invariants.replace(invs.clone())));
      },
      _ => ()
    }
    statement.walk(self);
  }
}

impl CRel {
  pub fn decorate_invariants(&mut self, imap: &HashMap<String, Vec<CondBExpr>>) {
    self.walk(&mut InvariantDecorator::new(imap));
  }
}
