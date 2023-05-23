use crate::shanty::Expression;
use crate::shanty::FunctionParameter;
use crate::shanty::Type;
use crate::shanty::Writer;

#[derive(Clone, Debug)]
pub struct Variable {
  name: String,
  ty: Type,
  value: Option<Expression>,
  is_array: bool,
  array_size: Option<Expression>,
  is_extern: bool,
  is_function: bool,
  function_params: Option<Vec<FunctionParameter>>,
  is_const: bool,
  is_pointer: bool,
}

impl Variable {
  pub fn new(name: &str, typ: Type) -> Self {
    Variable {
      name: name.to_string(),
      ty: typ,
      value: None,
      is_array: false,
      array_size: None,
      is_extern: false,
      is_function: false,
      function_params: None,
      is_const: false,
      is_pointer: false,
    }
  }

  pub fn set_value(&mut self, value: &Expression) -> &Self {
    self.value = Some(value.clone());
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

  pub fn set_extern(&mut self, is_extern: bool) -> &Self {
    self.is_extern = is_extern;
    self
  }

  pub fn set_function(&mut self, is_function: bool) -> &Self {
    self.is_function = is_function;
    self
  }

  pub fn set_function_params(&mut self, params: Vec<FunctionParameter>) -> &Self {
    self.function_params = Some(params);
    self
  }

  pub fn set_const(&mut self, is_const: bool) -> &Self {
    self.is_const = is_const;
    self
  }

  pub fn set_pointer(&mut self, is_pointer: bool) -> &Self {
    self.is_pointer = is_pointer;
    self
  }

  pub fn emit(&self, writer: &mut Writer) {
    if self.is_extern {
      writer.write("extern ");
    }
    if self.is_const {
      writer.write("const ");
    }
    self.ty.emit(writer);
    if self.is_pointer {
      writer.write("*");
    } else {
      writer.write(" ");
    }
    writer.write(&self.name);
    if self.is_array {
      writer.write("[");
      self.array_size.as_ref().map(|size| {
        size.emit(writer, false)
      });
      writer.write("]");
    }
    if self.is_function {
      writer.write("(");
      self.emit_params(writer);
      writer.write(")");
    }
    match &self.value {
      None => (),
      Some(val) => {
        writer.write(" = ");
        val.emit(writer, false);
      }
    }
  }

  fn emit_params(&self, writer: &mut Writer) {
    match &self.function_params {
      None => (),
      Some(params) => {
        let mut comma = "";
        for param in params {
          writer.write(comma);
          param.emit(writer);
          comma = ", ";
        }
      }
    }
  }
}
