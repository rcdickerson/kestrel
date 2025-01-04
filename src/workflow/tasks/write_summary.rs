//! Writes an entry to a summary file. This file summarizes results
//! for batch KestRel runs.

use std::fs::OpenOptions;
use std::io::prelude::*;
use crate::workflow::context::*;
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

impl Task for WriteSummary {
  fn name(&self) -> String { "write-summary".to_string() }
  fn run(&self, context: &mut Context) {
    let mut file = OpenOptions::new()
      .create(true)
      .append(true)
      .open(self.location.clone())
      .unwrap();
    let mut line = Vec::new();
    line.push(context.workflow_name.clone());
    line.append(&mut self.tags.clone());
    line.push(format!("{}", context.elapsed_time().as_millis()));
    line.push(format!("{}", context.verified));
    if let Err(e) = writeln!(file, "{}", line.join(",")) {
      panic!("Unable to write to summary file: {}", e);
    }
  }
}
