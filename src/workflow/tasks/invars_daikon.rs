use crate::daikon::invariant_parser::*;
use crate::output_mode::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
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
    let invariants = match parse_invariants(daikon_output) {
      Result::Ok(map) => map,
      Result::Err(err) => panic!("Error parsing Daikon invariants: {}", err),
    };
    if let Some(crel) = context.aligned_crel.as_mut() {
      crel.decorate_invariants(&invariants)
    };
  }
}
