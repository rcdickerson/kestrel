use std::path::Path;
use std::process::Command;

pub fn compile_rust_to_llvm(input_file: &String, out_dir: &Path) -> String {
  if !Path::new(input_file).exists() {
      panic!("File not found: {}", input_file);
  }

  let path = std::path::Path::new(input_file);
  let out_file = out_dir.join(format!("{}_rust.ll", path.file_stem().unwrap().to_str().unwrap())).to_str().unwrap().to_string();

  let output = Command::new("rustc")
      .arg("--crate-type=lib")
      .arg("-g")
      .arg("-C")
      .arg("panic=abort")
      // TODO: Re-enable overflow checks once the pipeline handles Rust's overflow
      // behavior. Disabling them for now to get clean LLVM IR, but overflow
      // differences will be a key part of Rust vs C verification.
      .arg("-C")
      .arg("overflow-checks=false")
      .arg("-C")
      .arg("opt-level=0")
      .arg("-Awarnings")
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
