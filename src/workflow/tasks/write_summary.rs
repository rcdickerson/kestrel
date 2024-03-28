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
  fn run(&self, context: &mut Context) {
    let mut file = OpenOptions::new()
      .create(true)
      .append(true)
      .open(self.location.clone())
      .unwrap();
    let mut line = Vec::new();
    line.push(context.task_name.clone());
    line.append(&mut self.tags.clone());
    if let Err(e) = writeln!(file, "{}", line.join(",")) {
      panic!("Unable to write to summary file: {}", e);
    }
  }
}
