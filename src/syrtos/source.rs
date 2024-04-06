use crate::syrtos::Function;
use crate::syrtos::Method;
use crate::syrtos::Statement;
use crate::syrtos::Variable;
use crate::syrtos::Writer;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Source {
  items: Vec<Item>,
  termin_checking: bool,
}

impl Source {
  pub fn new() -> Self {
    Source {
      items: Vec::new(),
      termin_checking: true,
    }
  }

  pub fn declare_variable(&mut self, var: &Variable) -> &Self {
    self.items.push(Item::Statement(Statement::Variable(var.clone())));
    self
  }

  pub fn push_function(&mut self, fun: &Function) -> &Self {
    self.items.push(Item::Function(fun.clone()));
    self
  }

  pub fn push_method(&mut self, method: &Method) -> &Self {
    self.items.push(Item::Method(method.clone()));
    self
  }

  pub fn disable_termination_checking(&mut self) -> &mut Self {
    self.termin_checking = false;
    self
  }

  pub fn write(&self) -> (String, HashMap<String, (usize, usize)>) {
    let mut writer = Writer::new();
    if !self.termin_checking { writer.disable_termination_checking(); }
    for item in &self.items {
      item.emit(&mut writer);
    }
    (writer.to_string(), writer.while_lines().clone())
  }
}

impl ToString for Source {
  fn to_string(&self) -> String { self.write().0 }
}

#[derive(Clone, Debug)]
enum Item {
  Function(Function),
  Method(Method),
  Statement(Statement),
}

impl Item {
  fn emit(&self, writer: &mut Writer) {
    match self {
      Item::Function(fun) => {
        writer.new_line();
        fun.emit(writer)
      },
      Item::Method(method) => {
        writer.new_line();
        method.emit(writer)
      },
      Item::Statement(stmt) => stmt.emit(writer),
    }
  }
}
