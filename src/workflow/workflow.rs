use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct Workflow<'a> {
  context: Context<'a>,
  tasks: Vec<Box<dyn Task>>,
}

impl <'a> Workflow<'a> {
  pub fn new(context: Context<'a>) -> Self {
    Workflow {
      context,
      tasks: Vec::new(),
    }
  }

  pub fn add_task(&mut self, task: impl Task + 'static) {
    self.tasks.push(Box::new(task));
  }

  pub fn execute(&mut self) {
    for task in &self.tasks {
      task.run(&mut self.context);
    }
  }
}
