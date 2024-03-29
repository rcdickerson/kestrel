use crate::workflow::context::*;
use crate::workflow::predicate_task::*;
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

  pub fn add_task_unless_verifed(&mut self, task: impl Task + 'static) {
    self.add_task(PredicateTask::new(&|ctx| !ctx.verified, Box::new(task)));
  }

  pub fn context(&self) -> &Context {
    &self.context
  }

  pub fn execute(&mut self) {
    for task in &self.tasks {
      task.run(&mut self.context);
    }
  }
}
