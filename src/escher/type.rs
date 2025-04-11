use crate::escher::Writer;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
  Bit,
  Char,
  Double,
  Float,
  Int,
  Void,
}

impl Type {
  pub fn emit(&self, writer: &mut Writer) {
    let type_str = match self {
      Type::Bit => "bit",
      Type::Char => "char",
      Type::Double => "double",
      Type::Float => "float",
      Type::Int => "int",
      Type::Void => "void",
    };
    writer.write(type_str);
  }
}

#[derive(Clone, Debug)]
pub enum TypeQualifier {
  Const,
}
