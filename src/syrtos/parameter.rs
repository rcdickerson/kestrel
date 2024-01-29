use crate::syrtos::Expression;
use crate::syrtos::Type;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub struct Parameter {
  pub name: String,
  pub ty: Type,
  pub array_sizes: Vec<Expression>,
  pub is_array: bool,
  pub is_const: bool,
}

impl Parameter {

  pub fn new(name: &str, ty: Type) -> Self {
    Parameter{
      name: name.to_string(),
      ty,
      array_sizes: Vec::new(),
      is_array: false,
      is_const: false,
    }
  }

  pub fn anonymous(ty: Type) -> Self {
    Parameter{
      name: "anon".to_string(), // TODO
      ty,
      array_sizes: Vec::new(),
      is_array: false,
      is_const: false,
    }
  }

  pub fn set_const(&mut self, is_const: bool) -> &Self {
    self.is_const = is_const;
    self
  }

  pub fn set_array(&mut self, is_array: bool) -> &Self {
    self.is_array = is_array;
    self
  }

  pub fn set_array_sizes(&mut self, sizes: &Vec<Expression>) -> &Self {
    self.array_sizes = sizes.clone();
    self
  }

  pub fn emit(&self, writer: &mut Writer) {
    if self.is_const {
      writer.write("const ");
    }
    writer.write(&self.name);
    writer.write(": ");
    self.ty.emit(writer);
  }
}
