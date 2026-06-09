use crate::syrtos::Writer;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
  Bool,
  Int,
  Nat,
  Object,
  Real,
}

impl Type {
  pub fn emit(&self, writer: &mut Writer) {
    let type_str = match self {
      Type::Bool => "bool",
      Type::Int => "int",
      Type::Nat => "nat",
      Type::Object => "object",
      Type::Real => "real",
    };
    writer.write(type_str);
  }
}
