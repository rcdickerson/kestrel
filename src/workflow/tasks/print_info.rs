//! Prints some piece of information to the console.

use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct PrintInfo<'a> {
  header: Option<&'a str>,
  printer: &'a dyn Fn(&Context) -> String,
}

impl <'a> PrintInfo<'a> {
  pub fn new(printer: &'a dyn Fn(&Context) -> String) -> Self {
    PrintInfo { header: None, printer }
  }

  pub fn with_header(header: &'a str, printer: &'a dyn Fn(&Context) -> String) -> Self {
    PrintInfo { header: Some(header), printer }
  }
}

impl Task for PrintInfo<'_> {
  fn name(&self) -> String { "print-info".to_string() }
  fn run(&self, context: &mut Context) {
    self.header.map(|head| {
      let line = std::iter::repeat('-').take(head.len()).collect::<String>();
      println!("\n{}\n{}", head, line);
    });
    println!("{}", (self.printer)(context))
  }
}
