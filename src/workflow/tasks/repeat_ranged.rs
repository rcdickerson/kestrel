//! A meta-[Task] which executes some set of subtasks over some range
//! of values.

use crate::workflow::context::*;
use crate::workflow::task::*;
use std::time::Instant;

pub struct RepeatRanged<'a, T, Context> {
  range: Vec<T>,
  make_task_at: &'a dyn Fn(T) -> Box<dyn Task<Context>>,
  finished: &'a dyn Fn(&Context) -> bool,
}

impl <'a, T, Context> RepeatRanged<'a, T, Context> {
  pub fn new(range: Vec<T>,
             make_task_at: &'a dyn Fn(T) -> Box<dyn Task<Context>>,
             finished: &'a dyn Fn(&Context) -> bool)
             -> Self {
    RepeatRanged { range, make_task_at, finished }
  }
}

impl <Context: Clone + Stopwatch, T: Clone> Task<Context> for RepeatRanged<'_, T, Context> {
  fn name(&self) -> String { "repeat_range".to_string() }
  fn run(&self, context: &mut Context) {
    let mut try_context = context.clone();
    for i in self.range.clone() {
      let task = (self.make_task_at)(i);
      let task_start = Instant::now();
      task.run(&mut try_context);
      context.set_timings_from(&try_context);
      context.push_task_time(task.name(), task_start.elapsed());
      if (self.finished)(&try_context) {
        break;
      }
      try_context = context.clone();
    }
    *context = try_context;
  }
}
