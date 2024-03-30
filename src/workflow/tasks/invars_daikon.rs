use crate::crel::ast::*;
use crate::crel::mapper::*;
use crate::daikon::invariant_parser::*;
use crate::output_mode::*;
use crate::spec::to_crel::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::process::Command;

pub struct InvarsDaikon { }

impl InvarsDaikon {
  pub fn new() -> Self {
    InvarsDaikon {}
  }
}

impl Task for InvarsDaikon {
  fn run(&self, context: &mut Context) {
    // Write Daikon output to file.
    let daikon_path = "daikon_output.c".to_string();
    println!("Writing Daikon to {}...", daikon_path);
    let daikon_output = OutputMode::Daikon.crel_to_daikon(
        &context.aligned_crel(),
        context.unaligned_crel().global_decls.clone(),
        context.unaligned_crel().fundefs.clone(),
        &Some(daikon_path.clone()));
    let mut file = File::create(&Path::new(daikon_path.clone().as_str()))
      .unwrap_or_else(|_| panic!("Error creating file: {}", daikon_path));
    match file.write_all(daikon_output.as_bytes()) {
      Ok(_) => println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }

    // Compile and run Daikon.
    println!("Compiling Daikon output...");
    Command::new("gcc")
      .args(["-gdwarf-2", "-O0", "-no-pie", "-o", "daikon_output", "daikon_output.c"])
      .spawn()
      .expect("failed to start gcc process")
      .wait()
      .expect("failed to compile daikon output");
    println!("Running Kvasir...");
    Command::new("kvasir-dtrace")
      .args(["./daikon_output"])
      .spawn()
      .expect("failed to start kvasir")
      .wait()
      .expect("failed to run kvasir");
    println!("Running Daikon...");
    let daikon_result = Command::new("java")
      .args(["-cp",
             format!("{}/daikon.jar", env::var("DAIKONDIR").expect("$DAIKONDIR not set")).as_str(),
             "daikon.Daikon",
             "--config_option", "daikon.derive.Derivation.disable_derived_variables=true",
             "--conf_limit", "0", // Bad invariants will be weeded out via Houdini.
             "daikon-output/daikon_output.decls",
             "daikon-output/daikon_output.dtrace"])
      .output()
      .expect("failed to run daikon");
    if !daikon_result.status.success() {
      panic!("Daikon failure: {:?}", daikon_output);
    }
    let daikon_output = match std::str::from_utf8(&daikon_result.stdout) {
      Ok(s) => s,
      Err(e) => panic!("Error reading daikon output: {}", e),
    };
    let mut invariants = match parse_invariants(daikon_output) {
      Result::Ok(map) => map.iter().map(|(key, val)| {
        let crel_val = val.iter().map(|v| v.to_crel()).collect::<Vec<_>>();
        (key.clone(), crel_val)
      }).collect::<HashMap<_, _>>(),
      Result::Err(err) => panic!("Error parsing Daikon invariants: {}", err),
    };
    separate_eq(&mut invariants);
    let mut keep_loops = LoopKeeper::new(invariants.keys().collect());
    let mut crel = context.aligned_crel().map(&mut keep_loops);
    crel.decorate_invariants(&invariants);
    context.aligned_crel.replace(crel);
  }
}

/// Reexpress equality (==) as a combination of <= and >=.
fn separate_eq(invariants: &mut HashMap<String, Vec<Expression>>) {
  for (_, invars) in invariants.iter_mut() {
    *invars = invars.iter()
      .flat_map(|invar| match invar {
        Expression::Binop{lhs, rhs, op: BinaryOp::Equals} => vec!(
          Expression::Binop{lhs: lhs.clone(), rhs: rhs.clone(), op: BinaryOp::Equals},
          Expression::Binop{lhs: lhs.clone(), rhs: rhs.clone(), op: BinaryOp::Lte},
          Expression::Binop{lhs: lhs.clone(), rhs: rhs.clone(), op: BinaryOp::Gte},
        ),
        _ => vec!(invar.clone())
      })
      .collect();
  }
}

struct LoopKeeper<'a> {
  keep_ids: HashSet<&'a String>,
  handled_ids: HashSet<String>,
}

impl <'a> LoopKeeper<'a> {
  fn new(keep_ids: HashSet<&'a String>) -> Self {
    LoopKeeper{keep_ids, handled_ids: HashSet::new()}
  }
}

impl CRelMapper for LoopKeeper<'_> {
  fn map_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
      Statement::While{loop_id, condition, ..} => match loop_id {
        None => stmt.clone(),
        Some(id) => if !self.keep_ids.contains(id) && !self.handled_ids.contains(id) {
          self.handled_ids.insert(id.clone());
          Statement::If {
            condition: condition.clone(),
            then: Box::new(stmt.clone()),
            els: None,
          }
        } else { stmt.clone() }
      },
      _ => stmt.clone(),
    }
  }
}
