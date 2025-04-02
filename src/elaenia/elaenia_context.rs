use crate::eggroll::ast::*;
use crate::elaenia::elaenia_spec::*;
use crate::unaligned::*;
use crate::workflow::Context;
use crate::workflow::stopwatch::*;
use egg::RecExpr;
use std::time::Duration;

#[derive(Clone)]
pub struct ElaeniaContext {
  pub workflow_name: String,
  pub spec: Option<ElaeniaSpec>,
  pub unaligned_crel: Option<UnalignedCRel>,
  pub unaligned_eggroll: Option<String>,
  pub aligned_eggroll: Option<RecExpr<Eggroll>>,
  pub output_path: Option<String>,
  pub stopwatch: WorkflowStopwatch,
  pub verified: bool,
}

impl ElaeniaContext {
  pub fn new(workflow_name: String) -> Self {
    ElaeniaContext {
      workflow_name,
      spec: None,
      unaligned_crel: None,
      unaligned_eggroll: None,
      aligned_eggroll: None,
      output_path: None,
      stopwatch: WorkflowStopwatch::new(),
      verified: false,
    }
  }

  pub fn spec(&self) -> &ElaeniaSpec {
    self.spec.as_ref().expect("Missing specification")
  }
}

impl Context for ElaeniaContext {
  fn unaligned_crel(&self) -> &UnalignedCRel {
    self.unaligned_crel.as_ref().expect("Missing unaligned CRel")
  }

  fn unaligned_eggroll(&self) -> &String {
    self.unaligned_eggroll.as_ref().expect("Missing unaligned eggroll")
  }

  fn accept_aligned_eggroll(&mut self, eggroll: RecExpr<Eggroll>) {
    self.aligned_eggroll = Some(eggroll);
  }

  fn is_verified(&self) -> bool {
    self.verified
  }
}

impl Stopwatch for ElaeniaContext {
 fn mark_started(&mut self) {
    self.stopwatch.mark_started();
  }

  fn mark_completed(&mut self) {
    self.stopwatch.mark_completed();
  }

  fn push_task_time(&mut self, task_name: String, duration: Duration) {
    self.stopwatch.push_task_time(task_name, duration);
  }

  fn task_timings(&self) -> Vec<(String, Duration)> {
    self.stopwatch.task_timings()
  }

  fn total_elapsed_time(&self) -> Duration {
    self.stopwatch.total_elapsed_time()
  }
}
