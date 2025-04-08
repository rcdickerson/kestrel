use crate::crel::ast::*;
use crate::crel::mapper::*;
use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct CRelLoopUnroll {
  depth: u32,
}

impl CRelLoopUnroll {
  pub fn new(depth: u32) -> Self {
    CRelLoopUnroll {
      depth
    }
  }
}

impl <Ctx: AlignsCRel> Task<Ctx> for CRelLoopUnroll {
  fn name(&self) -> String { "crel-loop-unroll".to_string() }

  fn run(&self, context: &mut Ctx) {
    let unrolled_crel = context.aligned_crel().as_ref()
        .expect("Missing aligned CRel")
        .clone()
        .map(&mut LoopUnroller::new(self.depth));
    context.accept_aligned_crel(unrolled_crel);
  }
}

struct LoopUnroller {
  depth: u32,
}

impl LoopUnroller {
  pub fn new(depth: u32) -> Self {
    LoopUnroller {
      depth
    }
  }
}

impl CRelMapper for LoopUnroller {
  fn map_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
      Statement::While{condition, body, ..} => {
        let mut unrolled = Statement::If {
          condition: condition.clone(),
          then: Box::new(body.clone().unwrap_or(Box::new(Statement::None))
                         .map(&mut LoopUnroller::new(self.depth))),
          els: Some(Box::new(Statement::Fail)),
        };
        for _ in 0..self.depth {
          unrolled = Statement::If {
            condition: condition.clone(),
            then: Box::new(unrolled),
            els: None,
          };
        }
        stmt.clone()
      },
      _ => stmt.clone(),
    }
  }

  fn map_expression(&mut self, expr: &Expression) -> Expression {
    match expr {
      Expression::Statement(stmt) => {
        Expression::Statement(Box::new(self.map_statement(stmt)))
      }
      _ => expr.clone(),
    }
  }
}
