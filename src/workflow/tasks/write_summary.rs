//! Writes an entry to a summary file. This file summarizes results
//! for batch KestRel runs.

use std::fs::OpenOptions;
use std::io::prelude::*;
use crate::workflow::KestrelContext;
use crate::workflow::stopwatch::Stopwatch;
use crate::workflow::task::*;

pub struct WriteSummary {
  location: String,
  tags: Vec<String>,
}

impl WriteSummary {
  pub fn new(location: String, tags: Vec<String>) -> Self {
    WriteSummary { location, tags }
  }
}

impl Task<KestrelContext> for WriteSummary {
  fn name(&self) -> String { "write-summary".to_string() }
  fn run(&self, context: &mut KestrelContext) {
    let mut file = OpenOptions::new()
      .create(true)
      .append(true)
      .open(self.location.clone())
      .unwrap();
    let mut line = Vec::new();
    line.push(context.workflow_name.clone());
    line.append(&mut self.tags.clone());
    line.push(format!("{}", context.total_elapsed_time().as_millis()));
    line.push(format!("{}", context.verified));
    if let Err(e) = writeln!(file, "{}", line.join(",")) {
      panic!("Unable to write to summary file: {}", e);
    }
  }
}
