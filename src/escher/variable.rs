use crate::escher::Expression;
use crate::escher::FunctionParameter;
use crate::escher::Initializer;
use crate::escher::Type;
use crate::escher::Writer;

#[derive(Clone, Debug)]
pub struct Variable {
  name: Option<String>,
  ty: Type,
  init: Option<Initializer>,
  is_array: bool,
  array_sizes: Vec<Expression>,
  is_function: bool,
  function_params: Option<Vec<FunctionParameter>>,
  is_const: bool,
  is_pointer: bool,
}

impl Variable {
  pub fn new(typ: Type) -> Self {
    Variable {
      name: None,
      ty: typ,
      init: None,
      is_array: false,
      array_sizes: Vec::new(),
      is_function: false,
      function_params: None,
      is_const: false,
      is_pointer: false,
    }
  }

  pub fn set_name(&mut self, name: String) -> &Self {
    self.name = Some(name);
    self
  }

  pub fn set_initializer(&mut self, init: Initializer) -> &Self {
    self.init = Some(init);
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
    if self.is_const {
      writer.write("const ");
    }
    self.ty.emit(writer);
    if self.is_pointer {
      writer.write("* ");
    } else {
      writer.write(" ");
    }
    writer.write(self.name.as_ref().unwrap_or(&"".to_string()));
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
    if self.is_function {
      writer.write("(");
      self.emit_params(writer);
      writer.write(")");
    }
    match &self.init {
      None => (),
      Some(init) => {
        writer.write(" = ");
        init.emit(writer);
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
