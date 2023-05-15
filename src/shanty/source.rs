use crate::shanty::Function;
use crate::shanty::Include;
use crate::shanty::Statement;
use crate::shanty::Variable;
use crate::shanty::Writer;

#[derive(Clone, Debug)]
pub struct Source {
  items: Vec<Item>,
}

impl Source {
  pub fn new() -> Self {
    Source {
      items: Vec::new(),
    }
  }

  pub fn include(&mut self, include: &str) -> &Self {
    self.items.push(Item::Include(Include::new(&include.to_string())));
    self
  }

  pub fn declare_variable(&mut self, var: &Variable) -> &Self {
    self.items.push(Item::Statement(Statement::Variable(var.clone())));
    self
  }

  pub fn push_function(&mut self, fun: &Function) -> &Self {
    self.items.push(Item::Function(fun.clone()));
    self
  }
}

impl ToString for Source {
  fn to_string(&self) -> String {
    let mut writer = Writer::new();
    for item in &self.items {
      item.emit(&mut writer);
    }
    writer.to_string()
  }
}

#[derive(Clone, Debug)]
enum Item {
  Function(Function),
  Include(Include),
  Statement(Statement),
}

impl Item {
  fn emit(&self, writer: &mut Writer) {
    match self {
      Item::Function(fun) => {
        writer.new_line();
        fun.emit(writer)
      },
      Item::Include(include) => include.emit(writer),
      Item::Statement(stmt) => stmt.emit(writer),
    }
  }
}
