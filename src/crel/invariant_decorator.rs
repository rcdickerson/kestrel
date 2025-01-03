use crate::crel::ast::*;
use crate::crel::visitor::*;
use std::collections::HashMap;

pub struct InvariantDecorator<'a> {
  imap: &'a HashMap<String, Vec<Expression>>,
}

impl InvariantDecorator<'_> {
  pub fn new<'a>(imap: &'a HashMap<String, Vec<Expression>>) -> InvariantDecorator<'a> {
    InvariantDecorator { imap }
  }
}

impl CRelVisitor for InvariantDecorator<'_> {
  fn visit_statement(&mut self, statement: &mut Statement) {
    match statement {
      Statement::While{id, invariants, ..} => {
        self.imap.get(&loop_head_name(id)).map(|invs| {
          invariants.append(&mut invs.clone())
        });
      },
      _ => ()
    }
  }
}

impl CRel {
  pub fn decorate_invariants(&mut self, imap: &HashMap<String, Vec<Expression>>) {
    self.walk(&mut InvariantDecorator::new(imap));
  }
}
