use std::fs;

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

  let base_name = target_ll_file.strip_suffix(".ll").unwrap_or(target_ll_file);
  let temp_ll_file = format!("{}_scrubbed.ll", base_name);
  fs::write(&temp_ll_file, &ll_contents).expect("Failed to write scrubbed LLVM IR");

  temp_ll_file
}
