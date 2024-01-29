use crate::syrtos::Expression;
use crate::syrtos::Type;
use crate::syrtos::Writer;

#[derive(Clone, Debug)]
pub struct Variable {
  name: String,
  ty: Type,
  value: Option<Expression>,
  is_const: bool,
  is_ghost: bool,
  is_nullable: bool,
}

impl Variable {
  pub fn new(ty: Type, name: String) -> Self {
    Variable {
      name,
      ty,
      value: None,
      is_const: false,
      is_ghost: false,
      is_nullable: false,
    }
  }

  pub fn set_name(&mut self, name: String) -> &Self {
    self.name = name;
    self
  }

  pub fn set_value(&mut self, value: &Expression) -> &Self {
    self.value = Some(value.clone());
    self
  }

  pub fn set_const(&mut self, is_const: bool) -> &Self {
    self.is_const = is_const;
    self
  }

  pub fn set_ghost(&mut self, is_ghost: bool) -> &Self {
    self.is_ghost = is_ghost;
    self
  }

  pub fn set_nullable(&mut self, is_nullable: bool) -> &Self {
    self.is_nullable = is_nullable;
    self
  }

  pub fn emit(&self, writer: &mut Writer) {
    if self.is_ghost {
      writer.write("ghost ");
    }
    if self.is_const {
      writer.write("const ");
    } else {
      writer.write("var ");
    }
    writer.write(&self.name);
    writer.write(": ");
    self.ty.emit(writer);
    if self.is_nullable {
      writer.write("?");
    }
    match &self.value {
      Some(value) => {
        writer.write(" := ");
        value.emit(writer, false);
      }
      _ => ()
    }
  }
}
