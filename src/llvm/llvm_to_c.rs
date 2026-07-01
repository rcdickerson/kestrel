use crate::crel::ast::CRel;
use std::path::Path;

/// Parses an LLVM IR file. Currently implemented as a stub 
/// to verify that the pipeline correctly routes .ll files.
pub fn process_llvm_file(input_file: &String) -> CRel {
    if !Path::new(input_file).exists() {
        panic!("File not found: {}", input_file);
    }
    
    println!("LLVM IR file detected: {}", input_file);

    CRel::Seq(vec![])
}
