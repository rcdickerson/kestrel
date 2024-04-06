use crate::crel::ast::*;
use crate::crel::visitor::*;

pub struct ClearInvariants { }

impl ClearInvariants {
  pub fn new() -> Self {
    ClearInvariants {}
  }
}

impl CRelVisitor for ClearInvariants {
  fn visit_statement(&mut self, statement: &mut Statement) {
    match statement {
      Statement::While{invariants, ..} => {
        invariants.clear();
      },
      _ => ()
    }
  }
}

impl CRel {
  pub fn clear_invariants(&mut self) {
    self.walk(&mut ClearInvariants::new());
  }
}
