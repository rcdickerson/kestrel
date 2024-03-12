use crate::workflow::context::*;

pub trait Task {
  fn run(&self, context: &mut Context);
}
