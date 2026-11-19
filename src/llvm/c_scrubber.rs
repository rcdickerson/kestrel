use std::fs;
use regex::Regex;

/// Scrubs Rellic-lifted C source to remove constructs unsupported by the CRel parser.
/// Returns the path to the newly created scrubbed C file.
pub fn scrub_rellic_c(lifted_c_file: &String) -> String {
    let mut code = fs::read_to_string(lifted_c_file).expect("Failed to read lifted C file");

    // Removes bare return statements.
    // TODO: Handle returns in CRel so this scrubbing can be removed.
    code = Regex::new(r"(?m)^[ \t]*return[ \t]*;[ \t]*\n?").unwrap().replace_all(&code, "").into_owned();

    let base_name = lifted_c_file.strip_suffix(".c").unwrap_or(lifted_c_file);
    let scrubbed_c_file = format!("{}_scrubbed.c", base_name);
    fs::write(&scrubbed_c_file, &code).expect("Failed to write scrubbed C file");

    scrubbed_c_file
}
