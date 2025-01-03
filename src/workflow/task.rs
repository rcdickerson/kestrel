//! Implementors represent some step in a KestRel [Workflow].

use crate::workflow::context::*;

pub trait Task {
  fn name(&self) -> String;
  fn run(&self, context: &mut Context);
}
