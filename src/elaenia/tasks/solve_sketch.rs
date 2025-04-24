use crate::crel::parser::*;
use crate::crel::fundef::*;
use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use regex::Regex;
use std::fs::File;
use std::io::Error;
use std::io::prelude::*;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use wait_timeout::ChildExt;

pub struct SolveSketch {
  /// How long in seconds we are willing to wait for a Sketch
  /// solution.
  timeout_secs: u64,
}

impl SolveSketch {
  pub fn new(timeout_secs: Option<u64>) -> Self {
    SolveSketch {
      timeout_secs: match timeout_secs {
        Some(to) => to,
        None => 3600,
      }
    }
  }
}

impl Task<ElaeniaContext> for SolveSketch {
  fn name(&self) -> String { "solve-sketch".to_string() }

  fn run(&self, context: &mut ElaeniaContext) {
    let sketch_path = "sketch.sk".to_string();

    // Write current aligned program as Sketch file.
    let sketch_prog = context.sketch_output().clone().expect("Missing Sketch output.");

    let mut file = File::create(&Path::new(sketch_path.clone().as_str()))
      .unwrap_or_else(|_| panic!("Error creating file: {}", sketch_path));
    match file.write_all(sketch_prog.as_bytes()) {
      Ok(_) => (), // println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }

    // Run Sketch.
    let mut child = Command::new("sketch")
      .args(["--fe-output-code", sketch_path.as_str()])
      .stdout(Stdio::piped())
      .spawn()
      .unwrap();

    let timeout = Duration::from_secs(self.timeout_secs);
    let status = match child.wait_timeout(timeout).unwrap() {
      Some(status) => status,
      None => {
        println!("Sketch timed out.");
        context.mark_sketch_success(false);
        context.mark_timed_out(true);
        child.kill().unwrap();
        child.wait().unwrap();
        return;
      }
    };

    if !status.success() {
      println!("Failed to solve sketch.");
      context.mark_sketch_success(false);
      return;
    }

    match cleanup(&"sketch.cpp") {
      Err(err) => panic!("Unable to manipulate sketch.cpp: {}", err),
      _ => (),
    }
    let solution_crel = parse_c_file(&"sketch.cpp".to_string());
    let (_, solution_funs) = extract_fundefs(&solution_crel);
    for choice_fun in context.choice_funs().clone() {
      let solution = solution_funs
        .get(&choice_fun.name)
        .expect(format!("No solution found for {}", choice_fun.name).as_str());
      context.accept_choice_solution(choice_fun.name.clone(), solution.clone());
      context.mark_sketch_success(true);
    }
  }
}

/// Dirty hacks to convert Sketch's C++ into something C parser
/// library can handle.
fn cleanup(file_path: &str) -> Result<(), Error> {
  // Capture all of the choice functions; this is all we're interested
  // in, and all we're going to output.
  let re = Regex::new(r"(?s)void choice_.*?\n\}").unwrap();
  let contents = std::fs::read_to_string(file_path)?;
  let mut file = std::fs::OpenOptions::new()
    .write(true).truncate(true).open(file_path)?;
  file.write(re.captures_iter(&contents)
                .map(|c| c[0].to_string()
                     // Instead of taking in a ref to an output object,
                     // return the output directly. Doing this with
                     // fragile string find / replaces, sorry!
                     .replace("void choice_", "int choice_")
                     .replace(", int& _out", "")
                     .replace("{", "{\n  int _out;")
                     .replace("return;", "return _out;"))
                .collect::<Vec<_>>()
                .join("\n")
             .as_bytes())?;
  Ok(())
}
