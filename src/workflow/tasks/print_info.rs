//! Prints some piece of information to the console.

use crate::workflow::task::*;

pub struct PrintInfo<'a, Context> {
  header: Option<&'a str>,
  printer: &'a dyn Fn(&Context) -> String,
}

impl <'a, Context> PrintInfo<'a, Context> {
  pub fn new(printer: &'a dyn Fn(&Context) -> String) -> Self {
    PrintInfo { header: None, printer }
  }

  pub fn with_header(header: &'a str, printer: &'a dyn Fn(&Context) -> String) -> Self {
    PrintInfo { header: Some(header), printer }
  }
}

impl <Context> Task<Context> for PrintInfo<'_, Context> {
  fn name(&self) -> String { "print-info".to_string() }
  fn run(&self, context: &mut Context) {
    self.header.map(|head| {
      let line = std::iter::repeat('-').take(head.len()).collect::<String>();
      println!("\n{}\n{}", head, line);
    });
    println!("{}", (self.printer)(context))
  }
}
