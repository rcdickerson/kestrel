use crate::shanty::Type;
use crate::shanty::Writer;

#[derive(Clone, Debug)]
pub struct FunctionParameter {
  name: String,
  ty: Type,
}

impl FunctionParameter {

  pub fn new(name: &str, ty: Type) -> Self {
    FunctionParameter{name: name.to_string(), ty}
  }

  pub fn emit(&self, writer: &mut Writer) {
    self.ty.emit(writer);
    writer.write(&self.name);
  }
}
