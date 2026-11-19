//! Checks the aligned product program with Frama-C WP

use crate::workflow::context::*;
use crate::workflow::task::*;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use wait_timeout::ChildExt;

/// A [Task] for checking the aligned product with Frama-C's WP tool.
/// If WP proves every goal, it sets the verified flag in the
/// [Context] to true.
pub struct FramaC {
  /// How long in seconds we are willing to wait for Frama-C to decide
  /// validity of the product program.
  timeout_secs: u64,
}

impl FramaC {
  pub fn new(timeout_secs: Option<u64>) -> Self {
    FramaC {
      timeout_secs: match timeout_secs {
        Some(to) => to,
        None => 3600,
      }
    }
  }
}

impl <Ctx: Context + OutputsAlignment> Task<Ctx> for FramaC {
  fn name(&self) -> String { "frama_c".to_string() }

  fn run(&self, context: &mut Ctx) {
    let working_dir = std::fs::canonicalize(context.working_dir())
      .expect("unable to canonicalize working dir");
    let frama_c_name = "frama_c.c";
    let frama_c_path = working_dir.join(frama_c_name);
    let frama_c_path_str = frama_c_path.to_str()
      .expect("Unable to create path for Frama-C output.");

    let frama_c_prog = context.aligned_output().clone().expect("Missing aligned output");

    let mut file = File::create(&frama_c_path)
      .unwrap_or_else(|_| panic!("Error creating file: {}", frama_c_path_str));
    match file.write_all(frama_c_prog.as_bytes()) {
      Ok(_) => (), // println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }

    let mut child = Command::new("frama-c")
      .current_dir(working_dir.clone())
      .args(["-wp", "-wp-model", "Bytes", frama_c_name])
      .stdout(Stdio::piped())
      .stderr(Stdio::piped())
      .spawn()
      .unwrap();

    let timeout = Duration::from_secs(self.timeout_secs);

    match child.wait_timeout(timeout).unwrap() {
      Some(_) => (),
      None => {
        println!("Frama-C timed out.");
        context.mark_timed_out(true);
        child.kill().unwrap();
        child.wait().unwrap();
        return;
      }
    };

    let mut frama_c_output = String::new();
    child.stderr.unwrap().read_to_string(&mut frama_c_output).unwrap();
    child.stdout.unwrap().read_to_string(&mut frama_c_output).unwrap();

    println!("{}", frama_c_output);

    context.mark_verified(frama_c_output.lines().any(|line| {
        match line.trim().strip_prefix("[wp] Proved goals:") {
            Some(counts) => {
                let counts: Vec<&str> = counts.split('/').map(|count| count.trim()).collect(); // This looks like ["n", "m"]
                counts.len() == 2 && counts[0] == counts[1]
            },
            None => false,
        }
    }));
  }
}