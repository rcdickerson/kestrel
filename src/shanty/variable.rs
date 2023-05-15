use crate::shanty::Expression;
use crate::shanty::Type;
use crate::shanty::Writer;

#[derive(Clone, Debug)]
pub struct Variable {
  name: String,
  ty: Type,
  value: Option<Expression>,
  is_extern: bool,
}

impl Variable {
  pub fn new(name: &str, typ: Type) -> Self {
    Variable {
      name: name.to_string(),
      ty: typ,
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

  pub fn emit(&self, writer: &mut Writer) {
    if self.is_extern {
      writer.write("extern ");
    }
    self.ty.emit(writer);
    writer.write(" ").write(&self.name);
    match &self.value {
      None => (),
      Some(val) => {
        writer.write(" = ");
        val.emit(writer, false);
      }
    }
  }
}
