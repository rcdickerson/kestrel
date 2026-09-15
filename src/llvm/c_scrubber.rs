use std::fs;
use regex::Regex;

/// Scrubs Rellic-lifted C source to remove constructs unsupported by the CRel parser.
/// Returns the path to the newly created scrubbed C file.
pub fn scrub_rellic_c(lifted_c_file: &String) -> String {
    let mut code = fs::read_to_string(lifted_c_file).expect("Failed to read lifted C file");

    code = remove_declarations_and_suffixes(&code);
    code = remove_rust_artifacts(&code);
    code = remove_unused_parameters(&code);
    code = remove_fat_pointer_artifacts(&code);
    code = fix_formatting(&code);

    let base_name = lifted_c_file.strip_suffix(".c").unwrap_or(lifted_c_file);
    let scrubbed_c_file = format!("{}_scrubbed.c", base_name);
    fs::write(&scrubbed_c_file, &code).expect("Failed to write scrubbed C file");

    scrubbed_c_file
}

/// Removes standard C forward declarations and unsigned integer literal suffixes.
fn remove_declarations_and_suffixes(code: &str) -> String {
    let mut c = code.to_string();
    c = Regex::new(r"(?m)^\s*(?:unsigned\s+)?\w+\s+\w+\([^)]*\)\s*;\s*\n?").unwrap().replace_all(&c, "").into_owned();
    c = Regex::new(r"\b([0-9]+)U\b").unwrap().replace_all(&c, "$1").into_owned();
    c = Regex::new(r"(?m)^\s*return\s*;\s*\n?").unwrap().replace_all(&c, "").into_owned();    
    c
}

/// Removes Rellic-specific artifacts, struct definitions, and unsigned type suffixes.
fn remove_rust_artifacts(code: &str) -> String {
    let mut c = code.to_string();
    c = Regex::new(r"(?ms)^struct\s+[a-zA-Z0-9_]+\s*\{.*?\}\s*;").unwrap().replace_all(&c, "").into_owned();
    c = Regex::new(r"(?ms)^struct\s+[a-zA-Z0-9_]+\s+[a-zA-Z0-9_]+\s*=\s*\{.*?\}\s*;").unwrap().replace_all(&c, "").into_owned();
    c = Regex::new(r"(?m)^char\s+[a-zA-Z0-9_]+\[\d+\]\s*=\s*.*?;").unwrap().replace_all(&c, "").into_owned();
    c = Regex::new(r"\b([0-9]+)UL\b").unwrap().replace_all(&c, "$1").into_owned();
    c
}

/// Cleans up unused parameter declarations and assignments injected by Rellic.
fn remove_unused_parameters(code: &str) -> String {
    let mut c = code.to_string();
    c = Regex::new(r"(?m)^\s*int\s+([a-zA-Z0-9_]+)_var0\s*;\s*\n?").unwrap().replace_all(&c, "").into_owned();
    c = Regex::new(r"(?m)^\s*[a-zA-Z0-9_]+_var0\s*=\s*[^;]+\s*;\s*\n?").unwrap().replace_all(&c, "").into_owned();
    c
}

/// Removes artifacts created by Rust fat pointer string representations.
fn remove_fat_pointer_artifacts(code: &str) -> String {
    let mut c = code.to_string();
    c = Regex::new(r#"(?m)^\s*[a-zA-Z0-9_]+\s*=\s*"[^"]*"\s*;\s*\n?"#).unwrap().replace_all(&c, "").into_owned();
    c
}

/// Dynamically adjusts indentation and removes extra blank lines based on brace depth.
fn fix_formatting(code: &str) -> String {
    let mut formatted = String::new();
    let mut level: usize = 0; // Explicitly define level as usize

    for line in code.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() { continue; }

        if trimmed.starts_with('}') {
            level = level.saturating_sub(1);
        }

        formatted.push_str(&format!("{}{}\n", "    ".repeat(level), trimmed));

        if trimmed.contains('{') {
            level += 1;
        }
    }
    formatted
}