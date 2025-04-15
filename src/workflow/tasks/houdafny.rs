//! [Houdini](https://www.cs.utexas.edu/~isil/cs389L/houdini-6up.pdf)-style
//! invariant inference which uses Dafny to check candidate
//! invariants.

use crate::crel::ast::*;
use crate::crel::visitor::CRelVisitor;
use crate::output_mode::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use regex::Regex;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use wait_timeout::ChildExt;

/// A [Task] for performing invariant inference using the Houdafny
/// pipeline. If invariants are found which enable verification,
/// sets the *verified* flag in the [Context] to true.
pub struct Houdafny {
  /// How long in seconds we are willing to wait for Dafny to decide
  /// validity of candidate invariants.
  timeout_secs: u64,
}

impl Houdafny {
  pub fn new(timeout_secs: Option<u64>) -> Self {
    Houdafny {
      timeout_secs: match timeout_secs {
        Some(to) => to,
        None => 3600,
      }
    }
  }
}

impl <Ctx: Context + AlignsCRel + GeneratesDafny> Task<Ctx> for Houdafny {
  fn name(&self) -> String { "houdafny".to_string() }

  fn run(&self, context: &mut Ctx) {
    let dafny_path = "houdafny.dfy".to_string();
    loop {
      // Write current aligned program as Dafny file.
      let (dafny_prog, while_lines) = context.generate_dafny(&dafny_path);

      // println!("Writing Dafny to {}...", dafny_path);
      let mut file = File::create(&Path::new(dafny_path.clone().as_str()))
        .unwrap_or_else(|_| panic!("Error creating file: {}", dafny_path));
      match file.write_all(dafny_prog.as_bytes()) {
        Ok(_) => (), // println!("Done"),
        Err(err) => panic!("Error writing output file: {}", err),
      }

      // Run Dafny.
      // println!("Running Dafny verification...");
      let mut child = Command::new("dafny")
        .args(["verify", dafny_path.as_str(), "--error-limit", "0", "--allow-warnings"])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

      let timeout = Duration::from_secs(self.timeout_secs);
      let status = match child.wait_timeout(timeout).unwrap() {
        Some(status) => status,
        None => {
          println!("Dafny timed out.");
          context.mark_timed_out(true);
          child.kill().unwrap();
          child.wait().unwrap();
          return;
        }
      };

      let mut dafny_output = String::new();
      child.stdout.unwrap().read_to_string(&mut dafny_output).unwrap();

      // Check to see if we're done, either successfull verification or
      // some failure without bad invariants.
      println!("{}", dafny_output);
      if status.success() {
        context.mark_verified(true);
        break;
      }
      let bad_invar_lines = parse_bad_invariants(dafny_output.to_string());
      if bad_invar_lines.is_empty() { break; }

      // We have bad invariants; remove them.
      let mut by_loop_id = HashMap::new();
      for line in bad_invar_lines {
        let (loop_id, offset) = loop_id_for_line(&while_lines, line)
            .expect(format!("No loop on line {}", line).as_str());
        if by_loop_id.get(&loop_id).is_none() {
          by_loop_id.insert(loop_id.clone(), HashSet::new());
        }
        by_loop_id.get_mut(&loop_id).unwrap().insert(offset - 1);
      }
      let mut aligned_crel = context.aligned_crel().clone().expect("Missing aligned CRel");
      aligned_crel.walk(&mut InvarRemover::new(&by_loop_id));
      context.accept_aligned_crel(aligned_crel);
    }
  }
}

struct InvarRemover<'a> {
  bad_invars: &'a HashMap<String, HashSet<usize>>
}

impl <'a> InvarRemover<'a> {
  fn new(bad_invars: &'a HashMap<String, HashSet<usize>>) -> Self {
    InvarRemover { bad_invars }
  }
}

impl CRelVisitor for InvarRemover<'_> {
  fn visit_statement(&mut self, stmt: &mut Statement) {
    match stmt {
      Statement::While{id, invariants, ..} => {
        if !invariants.is_empty() {
          self.bad_invars.get(&loop_head_name(id)).map(|to_remove| {
            let mut to_remove = to_remove.iter().collect::<Vec<_>>();
            to_remove.sort();
            to_remove.reverse();
            for idx in to_remove {
              invariants.remove(*idx);
            }
          });
        }
      },
      _ => (),
    }
  }
}

fn parse_bad_invariants(output: String) -> HashSet<usize> {
  let mut bad_invars = HashSet::new();
  let entry_re = Regex::new(r"loop invariant could not be proved on entry\s*\|\s*(\d+)").unwrap();
  for (_, [line_num]) in entry_re.captures_iter(output.as_str()).map(|c| c.extract()) {
    bad_invars.insert(line_num.parse::<usize>().unwrap());
  }
  let violation_re = Regex::new(r"loop invariant violation\s*\|\s*(\d+)").unwrap();
  for (_, [line_num]) in violation_re.captures_iter(output.as_str()).map(|c| c.extract()) {
    bad_invars.insert(line_num.parse::<usize>().unwrap());
  }
  bad_invars
}

fn loop_id_for_line(while_lines: &HashMap<String, (usize, usize)>, line: usize)
                    -> Option<(String, usize)> {
  while_lines.iter()
    .map(|(id, (start, end))| {
      if line >= *start && line <= *end { Some((id, line - start)) } else { None }
    })
    .filter(|item| item.is_some())
    .map(|item| item.unwrap())
    .fold(None, |cur, (id, offset)| match cur {
      None => Some((id, offset)),
      Some((_, closest)) => if offset < closest { Some((id, offset)) } else { cur }
    })
    .map(|(id, offset)| (id.clone(), offset - 1))
}
