//! An ordered collection of [Task]s which carry out some KestRel
//! execution pipeline. Workflows are centered around a [Context],
//! which holds data pertinent to the verification task.

use crate::eggroll::ast::*;
use crate::unaligned::UnalignedCRel;
use crate::workflow::predicate_task::*;
use crate::workflow::stopwatch::*;
use crate::workflow::task::*;
use egg::RecExpr;
use std::time::Instant;

pub trait Context {
  fn unaligned_crel(&self) -> &UnalignedCRel;
  fn unaligned_eggroll(&self) -> &String;
  fn accept_aligned_eggroll(&mut self, eggroll: RecExpr<Eggroll>);
  fn is_verified(&self) -> bool;
}

pub struct Workflow<Ctx: Context + Stopwatch> {
  context: Ctx,
  tasks: Vec<Box<dyn Task<Ctx>>>,
}

impl <'a, Ctx: Context + Stopwatch + 'static> Workflow<Ctx> {
  pub fn new(context: Ctx) -> Self {
    Workflow {
      context,
      tasks: Vec::new(),
    }
  }

  pub fn add_task(&mut self, task: impl Task<Ctx> + 'static) {
    self.tasks.push(Box::new(task));
  }

  pub fn add_task_unless_verifed(&mut self, task: impl Task<Ctx> + 'static) {
    self.add_task(PredicateTask::new(&|ctx: &Ctx| !ctx.is_verified(), Box::new(task)));
  }

  pub fn context(&self) -> &Ctx {
    &self.context
  }

  pub fn execute(&mut self) {
    self.context.mark_started();
    for task in &self.tasks {
      let task_start = Instant::now();
      task.run(&mut self.context);
      self.context.push_task_time(task.name(), task_start.elapsed());
    }
    self.context.mark_completed();
  }
}
