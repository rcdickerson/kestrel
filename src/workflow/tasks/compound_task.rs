//! A meta-[Task] which executes its enclosed task only when some
//! predicate holds during the workflow execution.

use crate::workflow::task::*;

pub struct CompoundTask<Context> {
  tasks: Vec<Box<dyn Task<Context>>>,
}

impl <Context> CompoundTask<Context> {
  pub fn new() -> Self {
    CompoundTask { tasks: Vec::new() }
  }

  pub fn from(tasks: Vec<Box<dyn Task<Context>>>) -> Self {
    CompoundTask { tasks }
  }

  pub fn add(&mut self, task: Box<dyn Task<Context>>) -> &Self {
    self.tasks.push(task);
    self
  }
}

impl <Context> Task<Context> for CompoundTask<Context> {
  fn name(&self) -> String { "compound_task".to_string() }
  fn run(&self, context: &mut Context) {
    for task in &self.tasks {
      task.run(context);
    }
  }
}
