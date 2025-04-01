//! Implementors represent some step in a KestRel [Workflow].

pub trait Task<Context> {
  fn name(&self) -> String;
  fn run(&self, context: &mut Context);
}
