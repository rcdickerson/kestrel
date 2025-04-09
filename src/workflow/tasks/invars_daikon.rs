//! Invokes Daikon to discover candidate invariants. Decorates the
//! [Context]'s aligned [CRel] with the invariant candidates. (The set
//! of candidates can be further refined with, e.g., [Houdafny].)

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
use std::process::Stdio;
use std::time::Duration;
use wait_timeout::ChildExt;

pub struct InvarsDaikon {
  timeout_secs: u64,
}

impl InvarsDaikon {
  pub fn new(timeout_secs: Option<u64>) -> Self {
    InvarsDaikon {
      timeout_secs: match timeout_secs {
        Some(to) => to,
        None => 3600,
      }
    }
  }
}

impl <Ctx: Context + AlignsCRel> Task<Ctx> for InvarsDaikon {
  fn name(&self) -> String { "invars-daikon".to_string() }

  fn run(&self, context: &mut Ctx) {
    // Write Daikon output to file.
    let daikon_path = "daikon_output.c".to_string();
    println!("Writing Daikon to {}...", daikon_path);
    let daikon_output = OutputMode::Daikon.crel_to_daikon(
        &context.aligned_crel().as_ref().expect("Missing aligned CRel"),
        context.unaligned_crel().as_ref()
          .expect("Missing unaligned CRel")
          .global_decls.clone(),
        context.unaligned_crel().as_ref()
          .expect("Missing unaligned CRel")
          .global_fundefs.clone(),
        &Some(daikon_path.clone()));
    let mut file = File::create(&Path::new(daikon_path.clone().as_str()))
      .unwrap_or_else(|_| panic!("Error creating file: {}", daikon_path));
    match file.write_all(daikon_output.as_bytes()) {
      Ok(_) => println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }

    // Compile and run Daikon.
    println!("Compiling Daikon output...");
    let mut gcc_child = Command::new("gcc")
      .args(["-gdwarf-2", "-O0", "-no-pie", "-o", "daikon_output", "daikon_output.c"])
      .spawn()
      .unwrap();
    let timeout = Duration::from_secs(self.timeout_secs);
    match gcc_child.wait_timeout(timeout).unwrap() {
      Some(_) => (),
      None => {
        println!("Daikon compilation via gcc timed out.");
        context.mark_timed_out(true);
        gcc_child.kill().unwrap();
        gcc_child.wait().unwrap();
        return;
      }
    };

    println!("Running Kvasir...");
    let mut kvasir_child = Command::new("kvasir-dtrace")
      .args(["./daikon_output"])
      .spawn()
      .unwrap();
    match kvasir_child.wait_timeout(timeout).unwrap() {
      Some(_) => (),
      None => {
        println!("Kvasir timed out.");
        context.mark_timed_out(true);
        kvasir_child.kill().unwrap();
        kvasir_child.wait().unwrap();
        return;
      }
    };


    println!("Running Daikon...");
    let mut daikon_child = Command::new("java")
      .args(["-cp",
             format!("{}/daikon.jar", env::var("DAIKONDIR").expect("$DAIKONDIR not set")).as_str(),
             "daikon.Daikon",
             "--config_option", "daikon.derive.Derivation.disable_derived_variables=true",
             "--conf_limit", "0", // Bad invariants will be weeded out via Houdini.
             "daikon-output/daikon_output.decls",
             "daikon-output/daikon_output.dtrace"])
      .stdout(Stdio::piped())
      .spawn()
      .unwrap();
    let daikon_status = match daikon_child.wait_timeout(timeout).unwrap() {
      Some(status) => status,
      None => {
        println!("Daikon timed out.");
        context.mark_timed_out(true);
        daikon_child.kill().unwrap();
        daikon_child.wait().unwrap();
        return;
      }
    };

    let mut daikon_output = String::new();
    daikon_child.stdout.unwrap().read_to_string(&mut daikon_output).unwrap();

    if !daikon_status.success() {
      panic!("Daikon failure: {:?}", daikon_output);
    }
    let mut invariants = match parse_invariants(&daikon_output) {
      Result::Ok(map) => map.iter().map(|(key, val)| {
        let crel_val = val.iter()
          .filter(|v| !v.contains_binop_a(&crate::spec::condition::CondABinop::Mod))
          .map(|v| v.to_crel())
          .collect::<Vec<_>>();
        (key.clone(), crel_val)
      }).collect::<HashMap<_, _>>(),
      Result::Err(err) => panic!("Error parsing Daikon invariants: {}", err),
    };
    separate_eq(&mut invariants);
    let mut keep_loops = LoopKeeper::new(invariants.keys().collect());
    let mut crel = context.aligned_crel().as_ref()
        .expect("Missing aligned CRel")
        .map(&mut keep_loops);
    crel.decorate_invariants(&invariants);
    context.accept_aligned_crel(crel);
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
      Statement::While{id, condition, ..} => {
        let lhid = loop_head_name(id);
        if !self.keep_ids.contains(&lhid) && !self.handled_ids.contains(&lhid) {
          self.handled_ids.insert(lhid);
          Statement::If {
            condition: condition.clone(),
            then: Box::new(stmt.clone()),
            els: None,
          }
        } else {
          stmt.clone()
        }
      },
      _ => stmt.clone(),
    }
  }
}
