use crate::crel::ast::CRel;
use std::path::Path;
use std::fs;
use std::process::Command;

/// Rellic-decomp on the provided LLVM IR file and returns the path to the lifted C file
pub fn run_rellic(clean_ll_file: &String) -> String {
    let mut base_name = clean_ll_file.as_str();
    base_name = base_name.strip_suffix(".ll").unwrap_or(base_name);
    base_name = base_name.strip_suffix("_scrubbed").unwrap_or(base_name);
    base_name = base_name.strip_suffix("_rust").unwrap_or(base_name);
    let lifted_c_file = format!("{}_rellic.c", base_name);
    let output = Command::new("rellic-decomp")
        .arg("-input")
        .arg(clean_ll_file)
        .arg("-output")
        .arg(&lifted_c_file)
        .output()
        .expect("Failed to execute rellic-decomp command. Is it installed and in your PATH?");
    if !output.status.success() {
        panic!("Rellic crashed while lifting the LLVM IR: {}", String::from_utf8_lossy(&output.stderr));
    }
    lifted_c_file
}

/// Processes an LLVM IR file.
pub fn process_llvm_file(input_file: &String) -> CRel {
    if !Path::new(input_file).exists() {
        panic!("File not found: {}", input_file);
    }
    let clean_ll_file = crate::llvm::llvm_scrubber::scrub_llvm_attributes(input_file);
    let lifted_c_file = run_rellic(&clean_ll_file);
    let scrubbed_c_file = crate::llvm::c_scrubber::scrub_rellic_c(&lifted_c_file);
    let parsed_crel = crate::crel::parser::parse_c_file(&scrubbed_c_file);
    parsed_crel
}
