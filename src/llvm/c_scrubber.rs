use std::fs;
use regex::Regex;

/// Scrubs Rellic-lifted C source to remove constructs unsupported by the CRel parser.
pub fn scrub_rellic_c(lifted_c_file: &String) -> String {
  let mut code = fs::read_to_string(lifted_c_file).expect("Failed to read lifted C file");

  let forward_declarations   = Regex::new(r"(?m)^\s*(?:unsigned\s+)?\w+\s+\w+\([^)]*\)\s*;\s*\n?").unwrap();
  let char_array_to_int      = Regex::new(r"char\s+([a-zA-Z0-9_]+)\[\d+\];").unwrap();
  let pointer_cast_deref     = Regex::new(r"\*\s*\(\s*(?:unsigned\s+)?int\s*\*\s*\)\s*\(\s*&\s*([a-zA-Z0-9_]+)\s*\)").unwrap();
  let unsigned_literal_suffix = Regex::new(r"\b([0-9]+)U\b").unwrap();
  let int_cast               = Regex::new(r"\(\s*int\s*\)\s*").unwrap();
  let unsigned_int_cast      = Regex::new(r"\(\s*unsigned\s+int\s*\)\s*").unwrap();

  code = forward_declarations.replace_all(&code, "").to_string();
  code = char_array_to_int.replace_all(&code, "int $1;").to_string();
  code = pointer_cast_deref.replace_all(&code, "$1").to_string();
  code = unsigned_literal_suffix.replace_all(&code, "$1").to_string();
  code = int_cast.replace_all(&code, "").to_string();
  code = unsigned_int_cast.replace_all(&code, "").to_string();
  code = code.replace("unsigned ", "");

  let base_name = lifted_c_file.strip_suffix(".c").unwrap_or(lifted_c_file);
  let scrubbed_c_file = format!("{}_scrubbed.c", base_name);
  fs::write(&scrubbed_c_file, &code).expect("Failed to write scrubbed C file");

  scrubbed_c_file
}