//! A meta-[Task] which executes its enclosed task only when some
//! predicate holds during the workflow execution.

// It would be better to define tasks across a std::ops::Range
// of arbitrary index, but this requires the index to implement
// the Step trait, which is marked unstable at the time of writing.
// https://github.com/rust-lang/rust/issues/42168

use crate::workflow::task::*;
use std::ops::Range;

pub struct RepeatRanged<'a, Context> {
  range: Range<u32>,
  make_task_at: &'a dyn Fn(u32) -> Box<dyn Task<Context>>,
  finished: &'a dyn Fn(&Context) -> bool,
}

impl <'a, Context> RepeatRanged<'a, Context> {
  pub fn new(range: Range<u32>,
             make_task_at: &'a dyn Fn(u32) -> Box<dyn Task<Context>>,
             finished: &'a dyn Fn(&Context) -> bool)
             -> Self {
    RepeatRanged { range, make_task_at, finished }
  }
}

impl <Context: Clone> Task<Context> for RepeatRanged<'_, Context> {
  fn name(&self) -> String { "repeat_range".to_string() }
  fn run(&self, context: &mut Context) {
    let mut try_context = context.clone();
    for i in self.range.clone() {
      let task = (self.make_task_at)(i);
      task.run(&mut try_context);
      if (self.finished)(&try_context) {
        break;
      }
      try_context = context.clone();
    }
    *context = try_context;
  }
}
