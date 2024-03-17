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

pub struct Houdafny { }

impl Houdafny {
  pub fn new() -> Self {
    Houdafny {}
  }
}

impl Task for Houdafny {
  fn run(&self, context: &mut Context) {
    let dafny_path = "houdafny.dfy".to_string();
    loop {
      // Write current aligned program as Dafny file.
      let (dafny_prog, while_lines) = OutputMode::Dafny.crel_to_dafny(
        &context.aligned_crel(),
        context.spec(),
        context.unaligned_crel().global_decls.clone(),
        &Some(dafny_path.clone()));

      println!("Writing Dafny to {}...", dafny_path);
      let mut file = File::create(&Path::new(dafny_path.clone().as_str()))
        .unwrap_or_else(|_| panic!("Error creating file: {}", dafny_path));
      match file.write_all(dafny_prog.as_bytes()) {
        Ok(_) => println!("Done"),
        Err(err) => panic!("Error writing output file: {}", err),
      }

      // Run Dafny.
      println!("Running Dafny verification...");
      let dafny_result = Command::new("dafny")
        .args(["verify", "houdafny.dfy", "--error-limit", "0"])
        .output()
        .expect("failure executing dafny");
      let dafny_output = match std::str::from_utf8(&dafny_result.stdout) {
        Ok(s) => s,
        Err(e) => panic!("Error reading dafny output: {}", e),
      };

      // Check to see if we're done, either successfull verification or
      // some failure without bad invariants.
      println!("{}", dafny_output);
      if dafny_result.status.success() { break; }
      let bad_invar_lines = parse_bad_invariants(dafny_output.to_string());
      if bad_invar_lines.is_empty() { break; }

      // We have bad invariants; remove them.
      let mut by_loop_id = HashMap::new();
      for line in bad_invar_lines {
        let (loop_id, offset) = loop_id_for_line(&while_lines, line)
            .expect(format!("No loop on line {}", line).as_str());
        if by_loop_id.get(&loop_id).is_none() {
          by_loop_id.insert(loop_id.clone(), Vec::new());
        }
        by_loop_id.get_mut(&loop_id).unwrap().push(offset);
      }
      context.aligned_crel.as_mut().expect("missing aligned CRel")
        .walk(&mut InvarRemover::new(&by_loop_id));
    }
  }
}

struct InvarRemover<'a> {
  bad_invars: &'a HashMap<String, Vec<usize>>
}

impl <'a> InvarRemover<'a> {
  fn new(bad_invars: &'a HashMap<String, Vec<usize>>) -> Self {
    InvarRemover { bad_invars }
  }
}

impl CRelVisitor for InvarRemover<'_> {
  fn visit_statement(&mut self, stmt: &mut Statement) {
    match stmt {
      Statement::While{loop_id, invariants, ..} => {
        if loop_id.is_some() && invariants.is_some() {
          self.bad_invars.get(loop_id.as_ref().unwrap()).map(|to_remove| {
            let mut to_remove = to_remove.clone();
            to_remove.sort();
            to_remove.reverse();
            for idx in to_remove {
              invariants.as_mut().unwrap().remove(idx);
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
