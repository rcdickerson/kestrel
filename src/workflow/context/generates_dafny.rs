use std::collections::HashMap;

pub trait GeneratesDafny {
  fn generate_dafny(&self, output_path: &String) -> (String, HashMap<String, (usize, usize)>);
}
