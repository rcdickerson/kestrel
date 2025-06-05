use crate::crel::parser::*;
use crate::crel::fundef::*;
use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use regex::Regex;
use std::fs::File;
use std::io::Error;
use std::io::prelude::*;
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
    let working_dir = std::fs::canonicalize(context.working_dir())
      .expect("unable to canonicalize working dir");
    let sketch_file = "sketch.sk";
    let sketch_path = working_dir.join(sketch_file);
    let sketch_path_str = sketch_path.to_str()
      .expect("Unable to create path for sketch output.");
    let solution_file = "sketch.cpp";
    let solution_path = working_dir.join(solution_file);
    let solution_path_str = solution_path.to_str()
      .expect("Unable to create path for sketch solution.");

    // Write current aligned program as Sketch file.
    let sketch_prog = context.sketch_output().clone().expect("Missing Sketch output.");
    let mut file = File::create(sketch_path.clone())
      .unwrap_or_else(|_| panic!("Error creating file: {}", sketch_path_str));
    match file.write_all(sketch_prog.as_bytes()) {
      Ok(_) => (), // println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }

    // Run Sketch.
    let mut child = Command::new("sketch")
      .current_dir(working_dir.clone())
      .args(["--fe-output-code", sketch_file])
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

    match cleanup(&solution_path_str) {
      Err(err) => panic!("Unable to manipulate {}: {}", solution_path_str, err),
      _ => (),
    }
    let solution_crel = parse_c_file(&solution_path_str.to_string());
    let (_, solution_funs) = extract_fundefs(&solution_crel);
    if context.choice_funs().is_empty() {
      context.mark_sketch_success(true);
    }
    for choice_fun in context.choice_funs().clone() {
      let solution = solution_funs.get(&choice_fun.name);
      if solution.is_none() { continue; }
      let mut solution_fun = solution.unwrap().clone();
      // Arrays come back from Sketch as pointers with commented lengths,
      // just pull the params from the original choice function.
      solution_fun.params = choice_fun.params.clone();
      context.accept_choice_solution(choice_fun.name.clone(), solution_fun.clone());
      context.mark_sketch_success(true);
    }
  }
}

/// Dirty hacks to convert Sketch's C++ into something our C parser
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
