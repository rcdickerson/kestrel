use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct PredicateTask<'a> {
  predicate: &'a dyn Fn(&Context) -> bool,
  task: Box<dyn Task>,
}

impl <'a> PredicateTask<'a> {
  pub fn new(predicate: &'a dyn Fn(&Context) -> bool, task: Box<dyn Task>) -> Self {
    PredicateTask { predicate, task }
  }
}

impl Task for PredicateTask<'_> {
  fn run(&self, context: &mut Context) {
    if (self.predicate)(context) {
      self.task.run(context);
    }
  }
}
