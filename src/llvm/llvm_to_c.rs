use crate::crel::ast::CRel;
use std::path::Path;
use std::fs;
use std::process::Command;

/// Cleans modern LLVM attributes on  provided LLVM IR file to make it compatible with Rellic
pub fn scrub_llvm_attributes(target_ll_file: &String) -> String {
    let mut ll_contents = fs::read_to_string(target_ll_file).expect("Failed to read LLVM IR file");

    ll_contents = ll_contents.replace(" nocreateundeforpoison", "");
    ll_contents = ll_contents.replace(" memory(argmem: readwrite)", "");
    ll_contents = ll_contents.replace(" memory(none)", "");
    ll_contents = ll_contents.replace(" nofree", "");
    ll_contents = ll_contents.replace(" willreturn", "");
    ll_contents = ll_contents.replace(" mustprogress", "");
    ll_contents = ll_contents.replace(" captures(none)", "");
    ll_contents = ll_contents.replace(" nocallback", "");

    let base_name = target_ll_file.strip_suffix(".ll").unwrap_or(target_ll_file);
    let temp_ll_file = format!("{}_scrubbed.ll", base_name);
    fs::write(&temp_ll_file, &ll_contents).expect("Failed to write scrubbed LLVM IR");
    
    temp_ll_file
}

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

/// Parses an LLVM IR file.
pub fn process_llvm_file(input_file: &String) -> CRel {
    if !Path::new(input_file).exists() {
        panic!("File not found: {}", input_file);
    }

    let clean_ll_file = scrub_llvm_attributes(input_file);
    
    let lifted_c_file = run_rellic(&clean_ll_file);
    
    let parsed_crel = crate::crel::parser::parse_c_file(&lifted_c_file);

    parsed_crel
}
