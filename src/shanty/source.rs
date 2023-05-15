use crate::shanty::Function;
use crate::shanty::Statement;
use crate::shanty::Variable;

#[derive(Clone, Debug)]
pub struct Source {
  includes: Vec<String>,
  items: Vec<Item>,
}

#[derive(Clone, Debug)]
enum Item {
  Statement(Statement),
  Function(Function),
}

impl Source {
  pub fn new() -> Self {
    Source {
      includes: Vec::new(),
      items: Vec::new(),
    }
  }

  pub fn include(&mut self, include: &str) -> &Self {
    self.includes.push(include.to_string());
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
    // self.includes.iter()
    //   .map(|inc| format!("#include \"{}\"\n", inc))
    //   .collect()
    format!("{:?}", self)
  }
}
