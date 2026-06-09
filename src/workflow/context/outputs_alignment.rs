pub trait OutputsAlignment {
  fn aligned_output(&self) -> &Option<String>;
  fn accept_aligned_output(&mut self, output: String);
  fn accept_output_path(&mut self, path: String);
  fn output_path(&self) -> &Option<String>;
  fn output_filename(&self) -> &Option<String>;
}
