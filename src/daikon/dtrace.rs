//! Produces a dtrace by running Kvasir on a Daikon-instrumented version of
//! the unaligned product. Follows the first half of the InvarsDaikon task,
//! stopping before Daikon itself runs.

use crate::crel::unaligned::UnalignedCRel;
use crate::output_mode::*;
use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;
use wait_timeout::ChildExt;

pub fn generate_dtrace(unaligned_crel: &UnalignedCRel, working_dir: &str, timeout_secs: u64) -> Option<PathBuf> {
  let working_dir = std::fs::canonicalize(working_dir)
    .expect("unable to canonicalize working dir");

  let daikon_c_name = "unaligned_daikon.c";
  let daikon_path = working_dir.join(daikon_c_name);
  let daikon_path_str = daikon_path.to_str()
    .expect("Unable to create path for daikon output.");

  let exec_name = "unaligned_daikon";
  let exec_path = working_dir.join(exec_name);
  let exec_path_str = exec_path.to_str()
    .expect("Unable to create path for instrumented executable.");

  // Write Daikon output to file.
  println!("Writing Daikon to {}...", daikon_path_str);
  let daikon_output = OutputMode::Daikon.crel_to_daikon(
      &unaligned_crel.unaligned_main,
      unaligned_crel.global_decls.clone(),
      unaligned_crel.global_fundefs.clone(),
      &Some(daikon_path_str.to_string()),
      None,
      20);
  let mut file = File::create(&daikon_path)
    .unwrap_or_else(|_| panic!("Error creating file: {}", daikon_path_str));
  match file.write_all(daikon_output.as_bytes()) {
    Ok(_) => println!("Done"),
    Err(err) => panic!("Error writing output file: {}", err),
  }

  // Compile and run Kvasir.
  println!("Compiling Daikon output...");
  let mut gcc_child = Command::new("gcc")
    .current_dir(working_dir.clone())
    .args(["-gdwarf-2", "-O0", "-no-pie", "-o", exec_name, daikon_c_name])
    .spawn()
    .unwrap();
  let timeout = Duration::from_secs(timeout_secs);
  match gcc_child.wait_timeout(timeout).unwrap() {
    Some(_) => (),
    None => {
      println!("Daikon compilation via gcc timed out.");
      gcc_child.kill().unwrap();
      gcc_child.wait().unwrap();
      return None;
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
      kvasir_child.kill().unwrap();
      kvasir_child.wait().unwrap();
      return None;
    }
  };

  Some(working_dir.join("daikon-output").join(format!("{}.dtrace", exec_name)))
}
