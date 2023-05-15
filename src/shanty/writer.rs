pub struct Writer {
  lines: Vec<String>,
  cur_line: Vec<String>,
  indent_level: usize,
}

impl Writer {

  pub fn new() -> Self {
    Writer{
      lines: Vec::new(),
      cur_line: Vec::new(),
      indent_level: 0,
    }
  }

  pub fn write_line(&mut self, line: &str) -> &mut Self {
    self.lines.push(format!("{:indent$}{}\n", "", line, indent=self.indent_level));
    self
  }

  pub fn write(&mut self, item: &str) -> &mut Self {
    if self.cur_line.len() == 0 {
      self.cur_line.push(format!("{:indent$}", "", indent=self.indent_level))
    }
    self.cur_line.push(item.to_string());
    self
  }

  pub fn new_line(&mut self) -> &mut Self {
    self.cur_line.push("\n".to_string());
    self.lines.push(self.cur_line.concat());
    self.cur_line = Vec::new();
    self
  }

  pub fn indent(&mut self) -> &mut Self {
    self.indent_level += 2;
    self
  }

  pub fn dedent(&mut self) -> &mut Self {
    self.indent_level -= 2;
    self
  }
}

impl ToString for Writer {
  fn to_string(&self) -> String {
    self.lines.concat()
  }
}
