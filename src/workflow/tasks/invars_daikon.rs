//! Invokes Daikon to discover candidate invariants. Decorates the
//! [Context]'s aligned [CRel] with the invariant candidates. (The set
//! of candidates can be further refined with, e.g., [Houdafny].)

use crate::crel::ast::*;
use crate::crel::fundef::FunDef;
use crate::daikon::invariant_parser::*;
use crate::output_mode::*;
use crate::spec::to_crel::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use wait_timeout::ChildExt;

pub struct InvarsDaikon {
  extra_global_decls: Vec<Declaration>,
  extra_fundefs: Vec<FunDef>,
  timeout_secs: u64,
}

impl InvarsDaikon {

  pub fn new(timeout_secs: Option<u64>) -> Self {
    InvarsDaikon {
      extra_global_decls: Vec::new(),
      extra_fundefs: Vec::new(),
      timeout_secs: match timeout_secs {
        Some(to) => to,
        None => 3600,
      }
    }
  }

  pub fn add_global_decl(&mut self, declaration: Declaration) {
    self.extra_global_decls.push(declaration);
  }

  pub fn add_fundef(&mut self, fundef: FunDef) {
    self.extra_fundefs.push(fundef);
  }
}

impl <Ctx: Context + FindsInvariants> Task<Ctx> for InvarsDaikon {
  fn name(&self) -> String { "invars-daikon".to_string() }

  fn run(&self, context: &mut Ctx) {
    let working_dir = std::fs::canonicalize(context.working_dir())
      .expect("unable to canonicalize working dir");

    let daikon_c_name = "daikon_output.c";
    let daikon_path = working_dir.join(daikon_c_name);
    let daikon_path_str = daikon_path.to_str()
      .expect("Unable to create path for daikon output.");

    let exec_name = "daikon_output";
    let exec_path = working_dir.join(exec_name);
    let exec_path_str = exec_path.to_str()
      .expect("Unable to create path for instrumented executable.");

    // Write Daikon output to file.
    println!("Writing Daikon to {}...", daikon_path_str);
    let mut global_decls = context.global_decls().clone();
    global_decls.append(&mut self.extra_global_decls.clone());
    let daikon_output = OutputMode::Daikon.crel_to_daikon(
        &context.daikon_crel(),
        global_decls,
        context.global_fundefs().clone(),
        &Some(daikon_path_str.to_string()),
        Some(&self.extra_fundefs),
        20);
    let mut file = File::create(&daikon_path)
      .unwrap_or_else(|_| panic!("Error creating file: {}", daikon_path_str));
    match file.write_all(daikon_output.as_bytes()) {
      Ok(_) => println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }

    // Compile and run Daikon.
    println!("Compiling Daikon output...");
    let mut gcc_child = Command::new("gcc")
      .current_dir(working_dir.clone())
      .args(["-gdwarf-2", "-O0", "-no-pie", "-o", exec_name, daikon_c_name])
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
      .current_dir(working_dir.clone())
      .args([exec_path_str])
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
      .current_dir(working_dir.clone())
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
    context.accept_invariants(invariants);
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
