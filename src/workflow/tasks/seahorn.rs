//! Checks the aligned product program with SeaHorn

use crate::workflow::context::*;
use crate::workflow::task::*;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use wait_timeout::ChildExt;

/// A [Task] for performing invariant inference using the Seahorn.
/// If Seahorn discharges the specification, it sets the verified flag in the
/// [Context] to true.
pub struct Seahorn {
  /// How long in seconds we are willing to wait for Seahorn to decide
  /// validity of the product program.
  timeout_secs: u64,
}

impl Seahorn {
  pub fn new(timeout_secs: Option<u64>) -> Self {
    Seahorn {
      timeout_secs: match timeout_secs {
        Some(to) => to,
        None => 3600,
      }
    }
  }
}

impl <Ctx: Context + OutputsAlignment> Task<Ctx> for Seahorn {
  fn name(&self) -> String { "seahorn".to_string() }

  fn run(&self, context: &mut Ctx) {
    let working_dir = std::fs::canonicalize(context.working_dir())
      .expect("unable to canonicalize working dir");
    let seahorn_name = "seahorn.c";
    let seahorn_path = working_dir.join(seahorn_name);
    let seahorn_path_str = seahorn_path.to_str()
      .expect("Unable to create path for seahorn output.");

    let seahorn_prog = context.aligned_output().clone().expect("Missing aligned output");

    let mut file = File::create(&seahorn_path)
      .unwrap_or_else(|_| panic!("Error creating file: {}", seahorn_path_str));
    match file.write_all(seahorn_prog.as_bytes()) {
      Ok(_) => (), // println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }

    let mut child = Command::new("sea")
      .current_dir(working_dir.clone())
      .args(["pf", "-m64", "--horn-strictly-la=false", seahorn_name])
      .stdout(Stdio::piped())
      .stderr(Stdio::piped())
      .spawn()
      .unwrap();

    let timeout = Duration::from_secs(self.timeout_secs);

    match child.wait_timeout(timeout).unwrap() {
      Some(_) => (),
      None => {
        println!("Seahorn timed out.");
        context.mark_timed_out(true);
        child.kill().unwrap();
        child.wait().unwrap();
        return;
      }
    };

    let mut seahorn_output = String::new();
    child.stderr.unwrap().read_to_string(&mut seahorn_output).unwrap();
    child.stdout.unwrap().read_to_string(&mut seahorn_output).unwrap();

    println!("{}", seahorn_output);

    // Clarification: SeaHorn returns 'unsat' when __VERIFIER_error() is unreachable,
    // and 'sat' __VERIFIER_error() is reachable. unreachable == safe and reachable == unsafe
    // So for now im if the output contains unsat then it is verified.
    context.mark_verified(seahorn_output.lines().any(|line| line.trim() == "unsat"));
  }
}