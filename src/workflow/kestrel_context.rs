//! Contains data needed in a KestRel verification [Workflow].

use crate::crel::ast::*;
use crate::eggroll::ast::*;
use crate::eggroll::to_crel;
use crate::spec::KestrelSpec;
use crate::workflow::Context;
use crate::workflow::stopwatch::*;
use crate::unaligned::*;
use egg::*;
use std::path::Path;
use std::time::Duration;

/// A container for data needed in a KestRel verification [Workflow].
#[derive(Clone)]
pub struct KestrelContext {
  pub workflow_name: String,
  pub spec: Option<KestrelSpec>,
  pub unaligned_crel: Option<UnalignedCRel>,
  pub unaligned_eggroll: Option<String>,
  pub aligned_eggroll: Option<RecExpr<Eggroll>>,
  pub aligned_eggroll_repetitions: Option<to_crel::GuardedRepetitions>,
  pub aligned_crel: Option<CRel>,
  pub aligned_output: Option<String>,
  pub output_path: Option<String>,
  pub stopwatch: WorkflowStopwatch,
  pub timed_out: bool,
  pub verified: bool,
}

impl KestrelContext {
  pub fn new(workflow_name: String) -> Self {
    KestrelContext {
      workflow_name,
      spec: None,
      unaligned_crel: None,
      unaligned_eggroll: None,
      aligned_eggroll: None,
      aligned_eggroll_repetitions: None,
      aligned_crel: None,
      aligned_output: None,
      output_path: None,
      stopwatch: WorkflowStopwatch::new(),
      timed_out: false,
      verified: false,
    }
  }

  pub fn spec(&self) -> &KestrelSpec {
    self.spec.as_ref().expect("Missing specification")
  }

  pub fn unaligned_crel(&self) -> &UnalignedCRel {
    self.unaligned_crel.as_ref().expect("Missing unaligned CRel")
  }

  pub fn unaligned_eggroll(&self) -> &String {
    self.unaligned_eggroll.as_ref().expect("Missing unaligned eggroll")
  }

  pub fn aligned_eggroll(&self) -> &RecExpr<Eggroll> {
    self.aligned_eggroll.as_ref().expect("Missing aligned eggroll")
  }

  pub fn aligned_crel(&self) -> &CRel {
    self.aligned_crel.as_ref().expect("Missing aligned CRel")
  }

  pub fn aligned_output(&self) -> &String {
    self.aligned_output.as_ref().expect("Missing aligned output")
  }

  pub fn output_path(&self) -> &String {
    self.output_path.as_ref().expect("Missing output path")
  }

  pub fn filename(&self) -> Option<String> {
    self.output_path.as_ref().map(|path| {
      Path::new(&path).file_name().unwrap().to_str().unwrap().to_string()
    })
  }
}

impl Context for KestrelContext {
  fn is_verified(&self) -> bool {
    self.verified
  }
}

impl Stopwatch for KestrelContext {
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
