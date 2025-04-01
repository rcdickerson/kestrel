//! A meta-[Task] which executes its enclosed task only when some
//! predicate holds during the workflow execution.

use crate::workflow::task::*;

pub struct PredicateTask<'a, Context> {
  predicate: &'a dyn Fn(&Context) -> bool,
  task: Box<dyn Task<Context>>,
}

impl <'a, Context> PredicateTask<'a, Context> {
  pub fn new(predicate: &'a dyn Fn(&Context) -> bool, task: Box<dyn Task<Context>>) -> Self {
    PredicateTask { predicate, task }
  }
}

impl <Context> Task<Context> for PredicateTask<'_, Context> {
  fn name(&self) -> String { self.task.name() }
  fn run(&self, context: &mut Context) {
    if (self.predicate)(context) {
      self.task.run(context);
    }
  }
}
