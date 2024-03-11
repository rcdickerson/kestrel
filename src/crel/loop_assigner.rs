use crate::crel::ast::*;
use crate::crel::visitor::*;

pub struct LoopIdAssigner {
  counter: u64,
  overwrite: bool,
}

impl LoopIdAssigner {
  pub fn new(overwrite: bool) -> Self {
    LoopIdAssigner {
      counter: 0,
      overwrite,
    }
  }
}

impl CRelVisitor for LoopIdAssigner {
  fn visit_statement(&mut self, statement: &mut Statement) {
    match statement {
      Statement::While{loop_id, ..} => if loop_id.is_none() || self.overwrite {
        loop_id.replace(format!("_loop_head_{}", self.counter));
        self.counter += 1;
      },
      _ => (),
    }
    statement.walk(self);
  }
}

impl CRel {
  pub fn assign_loop_ids(&mut self) {
    self.walk(&mut LoopIdAssigner::new(false));
  }
}

impl Statement {
  pub fn assign_loop_ids(&mut self) {
    self.walk(&mut LoopIdAssigner::new(false));
  }
}

impl Expression {
  pub fn assign_loop_ids(&mut self) {
    self.walk(&mut LoopIdAssigner::new(false));
  }
}
