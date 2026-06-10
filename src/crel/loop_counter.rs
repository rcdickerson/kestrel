use crate::crel::ast::*;
use crate::crel::visitor::CRelVisitor;

impl CRel {
  pub fn count_loops(&mut self) -> u32 {
    let mut counter = LoopCounter::new();
    self.walk(&mut counter);
    counter.num_loops
  }
}

struct LoopCounter {
  num_loops: u32,
}

impl LoopCounter {
  pub fn new() -> Self {
    LoopCounter{ num_loops: 0 }
  }
}

impl CRelVisitor for LoopCounter {
  fn visit_statement(&mut self, stmt: &mut Statement) {
    match stmt {
      Statement::While{..} => {
        self.num_loops += 1;
      },
      Statement::WhileRel{..} => {
        self.num_loops += 1;
      },
      _ => (),
    }
  }
}
