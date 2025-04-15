use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct WriteDafny { }

impl WriteDafny {
  pub fn new() -> Self {
    WriteDafny {}
  }
}

impl Task<ElaeniaContext> for WriteDafny {
  fn name(&self) -> String { "write-dafny".to_string() }

  fn run(&self, context: &mut ElaeniaContext) {
    context.accept_aligned_output(context.generate_dafny(&"".to_string()).0)
  }
}
