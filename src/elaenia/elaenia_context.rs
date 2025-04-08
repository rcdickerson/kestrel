use crate::crel::ast::*;
use crate::eggroll::ast::*;
use crate::eggroll::to_crel::*;
use crate::elaenia::elaenia_spec::*;
use crate::spec::condition::KestrelCond;
use crate::unaligned::*;
use crate::workflow::context::*;
use egg::RecExpr;
use std::path::Path;
use std::time::Duration;

#[derive(Clone)]
pub struct ElaeniaContext {
  workflow_name: String,
  spec: ElaeniaSpec,
  unaligned_crel: Option<UnalignedCRel>,
  unaligned_eggroll: Option<String>,
  aligned_eggroll: Option<RecExpr<Eggroll>>,
  aligned_eggroll_repetitions: Option<GuardedRepetitions>,
  aligned_crel: Option<CRel>,
  aligned_output: Option<String>,
  output_path: Option<String>,
  output_filename: Option<String>,
  stopwatch: WorkflowStopwatch,
  timed_out: bool,
  verified: bool,
}

impl ElaeniaContext {
  pub fn new(workflow_name: String, spec: ElaeniaSpec) -> Self {
    ElaeniaContext {
      workflow_name,
      spec,
      unaligned_crel: None,
      unaligned_eggroll: None,
      aligned_eggroll: None,
      aligned_eggroll_repetitions: None,
      aligned_crel: None,
      aligned_output: None,
      output_path: None,
      output_filename: None,
      stopwatch: WorkflowStopwatch::new(),
      timed_out: false,
      verified: false,
    }
  }

  pub fn spec(&self) -> &ElaeniaSpec {
    &self.spec
  }
}

impl Context for ElaeniaContext {
  fn workflow_name(&self) -> &String {
    &self.workflow_name
  }

  fn precondition(&self) -> &KestrelCond {
    &self.spec.pre
  }

  fn postcondition(&self) -> &KestrelCond {
    &self.spec.post
  }

  fn mark_verified(&mut self, verified: bool) {
    self.verified = verified;
  }

  fn is_verified(&self) -> bool {
    self.verified
  }

  fn mark_timed_out(&mut self, timed_out: bool) {
    self.timed_out = timed_out;
  }

  fn is_timed_out(&self) -> bool {
    self.timed_out
  }
}

impl AlignsCRel for ElaeniaContext {
  fn unaligned_crel(&self) -> &Option<UnalignedCRel> {
    &self.unaligned_crel
  }

  fn accept_unaligned_crel(&mut self, crel: UnalignedCRel) {
    self.unaligned_crel = Some(crel);
  }

  fn aligned_crel(&self) -> &Option<CRel> {
    &self.aligned_crel
  }

  fn accept_aligned_crel(&mut self, crel: CRel) {
    self.aligned_crel = Some(crel);
  }
}

impl AlignsEggroll for ElaeniaContext {
  fn unaligned_eggroll(&self) -> &Option<String> {
    &self.unaligned_eggroll
  }

  fn accept_unaligned_eggroll(&mut self, eggroll: String) {
    self.unaligned_eggroll = Some(eggroll);
  }

  fn aligned_eggroll(&self) -> &Option<RecExpr<Eggroll>> {
    &self.aligned_eggroll
  }

  fn accept_aligned_eggroll(&mut self, eggroll: RecExpr<Eggroll>) {
    self.aligned_eggroll = Some(eggroll);
  }

  fn aligned_eggroll_repetitions(&self) -> &Option<GuardedRepetitions> {
    &self.aligned_eggroll_repetitions
  }

  fn accept_aligned_eggroll_repetitions(&mut self, reps: GuardedRepetitions) {
    self.aligned_eggroll_repetitions = Some(reps);
  }
}

impl OutputsAlignment for ElaeniaContext {
  fn aligned_output(&self) -> &Option<String> {
    &self.aligned_output
  }

  fn accept_aligned_output(&mut self, output: String) {
    self.aligned_output = Some(output);
  }

  fn accept_output_path(&mut self, path: String) {
    self.output_path = Some(path.clone());
    self.output_filename = Some(Path::new(&path)
      .file_name().unwrap()
      .to_str().unwrap()
      .to_string());
  }

  fn output_path(&self) -> &Option<String> {
    &self.output_path
  }

  fn output_filename(&self) -> &Option<String> {
    &self.output_filename
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
