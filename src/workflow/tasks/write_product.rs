//! Writes the final product program to disk in accordance with the
//! user-provided [OutputMode].

use crate::output_mode::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

pub struct WriteProduct {
  output_mode: OutputMode,
}

impl WriteProduct {
  pub fn new(output_mode: OutputMode) -> Self {
    WriteProduct { output_mode }
  }
}

impl <Ctx: OutputsAlignment> Task<Ctx> for WriteProduct {
  fn name(&self) -> String { "write-product".to_string() }
  fn run(&self, context: &mut Ctx) {
    let output_path = context.output_path().as_ref().expect("Missing output path");
    println!("Writing output to {}...", output_path);
    let mut file = File::create(output_path)
      .unwrap_or_else(|_| panic!("Error creating file: {}", output_path));
    match file.write_all(context.aligned_output().as_ref()
                         .expect("Missing aligned output")
                         .as_bytes()) {
      Ok(_) => println!("Done"),
      Err(err) => panic!("Error writing output file: {}", err),
    }
    if self.output_mode == OutputMode::SvComp {
      let mut yaml_pathbuf = PathBuf::from(output_path.clone());
      yaml_pathbuf.set_extension("yml");
      let yaml_path = yaml_pathbuf.to_str().unwrap();
      println!("Writing yaml to {}...", yaml_path);
      let mut file = File::create(yaml_path)
        .unwrap_or_else(|_| panic!("Error creating file: {}", yaml_path));
      let filename = context.output_filename().as_ref().expect("Missing output filename");
      match file.write_all(svcomp_yaml(&filename).as_bytes()) {
        Ok(_) => println!("Done"),
        Err(err) => panic!("Error writing output file: {}", err),
      }
    }
  }
}

fn svcomp_yaml(filename: &String) -> String {
format!(
"format_version: '2.0'

input_files: '{}'

properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true

options:
  language: C
  data_model: ILP32
", filename)
}
