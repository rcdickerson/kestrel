use crate::spec::condition::KestrelCond;

pub trait Context {
  fn workflow_name(&self) -> &String;
  fn working_dir(&self) -> &String;

  fn precondition(&self) -> &KestrelCond;
  fn postcondition(&self) -> &KestrelCond;

  fn mark_verified(&mut self, verified: bool);
  fn is_verified(&self) -> bool;

  fn mark_timed_out(&mut self, timed_out: bool);
  fn is_timed_out(&self) -> bool;
}
