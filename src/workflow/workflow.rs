use crate::workflow::context::*;
use crate::workflow::predicate_task::*;
use crate::workflow::task::*;
use std::time::Instant;

pub struct Workflow<'a> {
  context: &'a mut Context<'a>,
  tasks: Vec<Box<dyn Task>>,
}

impl <'a> Workflow<'a> {
  pub fn new(context: &'a mut Context<'a>) -> Self {
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
    self.context.mark_started();
    for task in &self.tasks {
      let task_start = Instant::now();
      task.run(&mut self.context);
      self.context.task_timings.push((task.name(), task_start.elapsed()));
    }
    self.context.mark_completed();
  }
}
