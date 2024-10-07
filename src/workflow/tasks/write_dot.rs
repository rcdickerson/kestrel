use crate::eggroll::rewrite::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use egg::*;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

pub struct WriteDot { }

impl WriteDot {
  pub fn new() -> Self {
    WriteDot {}
  }
}

impl Task for WriteDot {
  fn name(&self) -> String { "write-dot".to_string() }
  fn run(&self, context: &mut Context) {
    println!("Writing egraph structure to egraph.dot");
    let runner = Runner::default()
      .with_expr(&context.unaligned_eggroll().parse().unwrap())
      // .with_iter_limit(5)
      .run(&rewrites());
    write_file(&runner.egraph.dot().to_string(), "egraph.dot");
  }
}

fn write_file(contents: &String, location: &str) {
  let path = Path::new(location);
  let mut dot_file = match File::create(path) {
    Err(_) => panic!("Could not create file: {}", location),
    Ok(f)  => f,
  };
  dot_file.write_all(contents.as_bytes()).expect("Unable to write file.")
}
