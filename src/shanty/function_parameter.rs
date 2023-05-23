use crate::shanty::Expression;
use crate::shanty::Type;
use crate::shanty::Writer;

#[derive(Clone, Debug)]
pub struct FunctionParameter {
  name: String,
  ty: Type,
  array_size: Option<Expression>,
  is_array: bool,
  is_const: bool,
  is_pointer: bool,
}

impl FunctionParameter {

  pub fn new(name: &str, ty: Type) -> Self {
    FunctionParameter{
      name: name.to_string(),
      ty,
      array_size: None,
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

  pub fn set_array_size(&mut self, size: &Expression) -> &Self {
    self.array_size = Some(size.clone());
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
      writer.write("* ");
    } else {
      writer.write(" ");
    }
    writer.write(&self.name);
    match &self.array_size {
      None => (),
      Some(expr) => {
        writer.write("[");
        expr.emit(writer, false);
        writer.write("]");
      }
    }
  }
}
