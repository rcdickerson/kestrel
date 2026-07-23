use std::fs;
use regex::Regex;

/// Cleans modern LLVM attributes on provided LLVM IR file to make it compatible with Rellic
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
  ll_contents = ll_contents.replace("getelementptr inbounds nuw ", "getelementptr inbounds ");
  ll_contents = ll_contents.replace("getelementptr inbounds nusw ", "getelementptr inbounds ");
  ll_contents = ll_contents.replace("getelementptr nusw nuw ", "getelementptr ");
  ll_contents = ll_contents.replace("getelementptr nuw ", "getelementptr ");
  ll_contents = ll_contents.replace("getelementptr nusw ", "getelementptr ");
  ll_contents = translate_debug_records(ll_contents);

  let base_name = target_ll_file.strip_suffix(".ll").unwrap_or(target_ll_file);
  let temp_ll_file = format!("{}_scrubbed.ll", base_name);
  fs::write(&temp_ll_file, &ll_contents).expect("Failed to write scrubbed LLVM IR");

  temp_ll_file
}

/// Translates LLVM 18+ debug records into LLVM 16 intrinsic calls for Rellic compatibility.
pub fn translate_debug_records(mut code: String) -> String {
    let dbg_declare_re = Regex::new(r"(?m)^\s*#dbg_declare\(([^,]+),\s*(!\d+),\s*(.+?),\s*(!\d+)\)").unwrap();
    code = dbg_declare_re.replace_all(&code, "  call void @llvm.dbg.declare(metadata $1, metadata $2, metadata $3), !dbg $4").to_string();

    let dbg_value_re = Regex::new(r"(?m)^\s*#dbg_value\(([^,]+),\s*(!\d+),\s*(.+?),\s*(!\d+)\)").unwrap();
    code = dbg_value_re.replace_all(&code, "  call void @llvm.dbg.value(metadata $1, metadata $2, metadata $3), !dbg $4").to_string();

    if code.contains("@llvm.dbg.declare") && !code.contains("declare void @llvm.dbg.declare") {
        code.push_str("\ndeclare void @llvm.dbg.declare(metadata, metadata, metadata)\n");
    }
    if code.contains("@llvm.dbg.value") && !code.contains("declare void @llvm.dbg.value") {
        code.push_str("\ndeclare void @llvm.dbg.value(metadata, metadata, metadata)\n");
    }

    code
}
