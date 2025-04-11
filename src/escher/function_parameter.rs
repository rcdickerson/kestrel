use crate::escher::Expression;
use crate::escher::Type;
use crate::escher::Writer;

#[derive(Clone, Debug)]
pub struct FunctionParameter {
  pub name: Option<String>,
  pub ty: Type,
  pub array_sizes: Vec<Expression>,
  pub is_array: bool,
  pub is_const: bool,
  pub is_pointer: bool,
}

impl FunctionParameter {

  pub fn new(name: &str, ty: Type) -> Self {
    FunctionParameter{
      name: Some(name.to_string()),
      ty,
      array_sizes: Vec::new(),
      is_array: false,
      is_const: false,
      is_pointer: false,
    }
  }

  pub fn anonymous(ty: Type) -> Self {
    FunctionParameter{
      name: None,
      ty,
      array_sizes: Vec::new(),
      is_array: false,
      is_const: false,
      is_pointer: false,
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

  pub fn set_pointer(&mut self, is_pointer: bool) -> &Self {
    self.is_pointer = is_pointer;
    self
  }

  pub fn emit(&self, writer: &mut Writer) {
    if self.is_const {
      writer.write("const ");
    }
    self.ty.emit(writer);
    if self.is_pointer {
      writer.write("*");
    }
    self.name.as_ref().map(|name| writer.write(" ").write(name));
    if self.is_array {
      writer.write("[");
      let mut delimit = "";
      for size in &self.array_sizes {
        writer.write(delimit);
        size.emit(writer, false);
        delimit = "]["
      }
      writer.write("]");
    }
  }
}
