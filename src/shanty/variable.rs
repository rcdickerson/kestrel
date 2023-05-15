use crate::shanty::Expression;
use crate::shanty::Type;

#[derive(Clone, Debug)]
pub struct Variable {
  name: String,
  typ: Type,
  value: Option<Expression>,
  is_extern: bool,
}

impl Variable {
  pub fn new(name: &str, typ: Type) -> Self {
    Variable {
      name: name.to_string(),
      typ: typ,
      value: None,
      is_extern: false,
    }
  }

  pub fn set_extern(&mut self, is_extern: bool) -> &Self {
    self.is_extern = is_extern;
    self
  }

  pub fn set_value(&mut self, value: &Expression) -> &Self {
    self.value = Some(value.clone());
    self
  }
}
