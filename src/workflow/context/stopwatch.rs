use std::time::{Duration, Instant};

pub trait Stopwatch {
  fn mark_started(&mut self);
  fn push_task_time(&mut self, task_name: String, duration: Duration);
  fn mark_completed(&mut self);
  fn task_timings(&self) -> Vec<(String, Duration)>;
  fn total_elapsed_time(&self) -> Duration;
}

#[derive(Clone)]
pub struct WorkflowStopwatch {
  start_time: Option<Instant>,
  task_timings: Vec<(String, Duration)>,
  completion_time: Option<Duration>,
}

impl WorkflowStopwatch {
  pub fn new() -> Self {
    WorkflowStopwatch {
      start_time: None,
      task_timings: Vec::new(),
      completion_time: None,
    }
  }
}

impl Stopwatch for WorkflowStopwatch {
  fn mark_started(&mut self) {
    self.start_time.replace(Instant::now());
  }

  fn mark_completed(&mut self) {
    let elapsed = self.start_time.expect("Execution not marked as started").elapsed();
    self.completion_time.replace(elapsed);
  }

  fn push_task_time(&mut self, task_name: String, duration: Duration) {
    self.task_timings.push((task_name, duration));
  }

  fn task_timings(&self) -> Vec<(String, Duration)> {
    self.task_timings.clone()
  }

  fn total_elapsed_time(&self) -> Duration {
    match self.completion_time {
      Some(duration) => duration,
      None => self.start_time.expect("Execution not marked as started").elapsed()
    }
  }
}
