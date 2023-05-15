use crate::shanty::Writer;

#[derive(Clone, Debug)]
pub struct Include {
  lib_name: String,
}

impl Include {

  pub fn new(lib_name: &str) -> Self {
    Include{lib_name: lib_name.to_string()}
  }

  pub fn emit(&self, writer: &mut Writer) {
    writer.write_line(&format!("#include \"{}\"", self.lib_name));
  }
}
