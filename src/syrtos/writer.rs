use std::collections::HashMap;

pub struct Writer {
  lines: Vec<String>,
  cur_line: Vec<String>,
  indent_level: usize,
  while_lines: HashMap<String, (usize, usize)>,
  termin_checking: bool,
}

impl Writer {
  pub fn new() -> Self {
    Writer{
      lines: Vec::new(),
      cur_line: Vec::new(),
      indent_level: 0,
      while_lines: HashMap::new(),
      termin_checking: true,
    }
  }

  pub fn write_line(&mut self, line: &str) -> &mut Self {
    self.lines.push(format!("{:indent$}{}\n", "", line, indent=self.indent_level));
    self
  }

  pub fn write(&mut self, item: &str) -> &mut Self {
    if self.cur_line.is_empty() {
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

  pub fn cur_line(&self) -> usize {
    self.lines.len()
  }

  pub fn tag_while(&mut self, id: String, start: usize, end: usize) {
    self.while_lines.insert(id, (start, end));
  }

  pub fn while_lines(&self) -> &HashMap<String, (usize, usize)> {
    &self.while_lines
  }

  pub fn indent(&mut self) -> &mut Self {
    self.indent_level += 2;
    self
  }

  pub fn dedent(&mut self) -> &mut Self {
    self.indent_level -= 2;
    self
  }

  pub fn disable_termination_checking(&mut self) -> &mut Self {
    self.termin_checking = false;
    self
  }

  pub fn check_termination(&self) -> bool {
    self.termin_checking
  }
}

impl ToString for Writer {
  fn to_string(&self) -> String {
    self.lines.concat()
  }
}
