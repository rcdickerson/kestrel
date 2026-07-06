use std::path::Path;
use std::process::Command;

pub fn compile_rust_to_llvm(input_file: &String) -> String {
  if !Path::new(input_file).exists() {
      panic!("File not found: {}", input_file);
  }
  let base_name = input_file.strip_suffix(".rs").unwrap_or(input_file);
  let out_file = format!("{}_rust.ll", base_name);
  let output = Command::new("rustc")
      .arg("--crate-type=lib")
      .arg("-C")             
      .arg("panic=abort")
      .arg("--emit=llvm-ir") 
      .arg(input_file)
      .arg("-o")
      .arg(&out_file)
      .output()
      .expect("Failed to execute rustc command");
  if !output.status.success() {
      panic!("Rust compilation failed: {}", String::from_utf8_lossy(&output.stderr));
  }
  out_file
}
